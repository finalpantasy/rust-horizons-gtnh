//! Windows: one sampler thread suspends each sampled thread in turn, reads its registers, copies the top of its
//! stack into its ring and resumes it. A thread's CPU samples follow its cycle count, so they weigh CPU time as the
//! Linux CPU-time timers do; nothing allocates or locks while a thread is suspended, since it may hold the heap lock.

use std::io;
use std::sync::atomic::Ordering::Relaxed;
use std::sync::{Arc, Condvar, Mutex, OnceLock};
use std::time::{Duration, Instant};

use windows_sys::Win32::Foundation::{
    CloseHandle, DUPLICATE_SAME_ACCESS, DuplicateHandle, HANDLE, HMODULE,
};
use windows_sys::Win32::System::Diagnostics::Debug::{
    CONTEXT, CONTEXT_CONTROL_AMD64, CONTEXT_INTEGER_AMD64, GetThreadContext,
};
use windows_sys::Win32::System::ProcessStatus::{
    EnumProcessModules, GetModuleFileNameExW, GetModuleInformation, MODULEINFO,
};
use windows_sys::Win32::System::Threading::{
    CREATE_WAITABLE_TIMER_HIGH_RESOLUTION, CreateWaitableTimerExW, GetCurrentProcess,
    GetCurrentThread, INFINITE, ResumeThread, SetThreadPriority, SetWaitableTimer, SuspendThread,
    THREAD_PRIORITY_TIME_CRITICAL, TIMER_ALL_ACCESS, WaitForSingleObject,
};
use windows_sys::Win32::System::WindowsProgramming::QueryThreadCycleTime;

use super::eh::Loaded;
use super::{Regs, TIME_EVERY, ThreadState};

/// A duplicated handle to a sampled thread, with the rights to suspend it and read its context and cycle count.
pub struct Target(HANDLE);

// SAFETY: a thread handle is a kernel handle, usable and closable from any thread.
unsafe impl Send for Target {}
// SAFETY: see Send; the handle is never changed after creation.
unsafe impl Sync for Target {}

impl Default for Target {
    fn default() -> Self {
        Self(std::ptr::null_mut())
    }
}

impl Drop for Target {
    fn drop(&mut self) {
        if !self.0.is_null() {
            // SAFETY: the handle came from DuplicateHandle and is closed once.
            unsafe { CloseHandle(self.0) };
        }
    }
}

impl Target {
    pub fn current() -> Option<Self> {
        let mut handle = std::ptr::null_mut();
        // SAFETY: the pseudo-handles are always valid for the calling process and thread; handle is a live out-pointer.
        let ok = unsafe {
            let process = GetCurrentProcess();
            DuplicateHandle(
                process,
                GetCurrentThread(),
                process,
                &mut handle,
                0,
                0,
                DUPLICATE_SAME_ACCESS,
            )
        };
        (ok != 0).then_some(Self(handle))
    }

    fn cycles(&self) -> u64 {
        let mut cycles = 0;
        // SAFETY: the handle is a live thread handle with query rights; cycles is a live out-pointer.
        unsafe { QueryThreadCycleTime(self.0, &mut cycles) };
        cycles
    }
}

/// One armed timer: the sampler thread's entry for a thread and kind of sample.
pub struct Timer(u64);

struct Armed {
    id: u64,
    state: Arc<ThreadState>,
    wall: bool,
    period: Duration,
    due: Instant,
    /// The thread's cycle count at the last visit.
    cycles: u64,
    /// CPU cycles run and not yet sampled (CPU timers only).
    owed: u64,
}

struct Sampler {
    armed: Vec<Armed>,
    next_id: u64,
}

static SAMPLER: Mutex<Sampler> = Mutex::new(Sampler {
    armed: Vec::new(),
    next_id: 0,
});
static ARMED: Condvar = Condvar::new();
/// Cycle counter ticks per second, measured once against the monotonic clock.
static CYCLES_PER_SEC: OnceLock<f64> = OnceLock::new();
/// CPU samples one visit may write for a thread the sampler reached late.
const MAX_CATCH_UP: u64 = 4;

/// QueryThreadCycleTime counts time-stamp counter ticks while the thread runs, so the TSC's rate converts it. Both
/// ends of this measurement are wall clocks: a preemption during it costs no accuracy. Spins 2 ms, once.
fn cycles_per_sec() -> f64 {
    // SAFETY: RDTSC reads a counter every x86-64 processor has; it touches no memory.
    let tsc = || unsafe { std::arch::x86_64::_rdtsc() };
    *CYCLES_PER_SEC.get_or_init(|| {
        let (started, from) = (Instant::now(), tsc());
        while started.elapsed() < Duration::from_millis(2) {
            std::hint::spin_loop();
        }
        let ticks = tsc().saturating_sub(from) as f64;
        (ticks / started.elapsed().as_secs_f64()).max(1.0)
    })
}

fn cycles_to_ns(cycles: u64) -> u64 {
    (cycles as f64 * 1e9 / cycles_per_sec()) as u64
}

fn arm_timer(state: &Arc<ThreadState>, hz: u32, wall: bool) -> io::Result<Timer> {
    let mut sampler = SAMPLER.lock().unwrap();
    let id = sampler.next_id;
    sampler.next_id += 1;
    let period = Duration::from_nanos(1_000_000_000 / u64::from(hz.max(1)));
    sampler.armed.push(Armed {
        id,
        state: state.clone(),
        wall,
        period,
        due: Instant::now() + period,
        cycles: state.target.cycles(),
        owed: 0,
    });
    ARMED.notify_all();
    Ok(Timer(id))
}

pub fn arm(state: &Arc<ThreadState>, hz: u32) -> io::Result<Timer> {
    arm_timer(state, hz, false)
}

pub fn arm_wall(state: &Arc<ThreadState>, hz: u32) -> io::Result<Timer> {
    arm_timer(state, hz, true)
}

/// Removes the timer; the sampler holds the lock while it samples, so no sample of it is written after this returns.
pub fn disarm(timer: Timer) {
    SAMPLER.lock().unwrap().armed.retain(|a| a.id != timer.0);
}

/// The calling thread's CPU time, from its cycle count.
pub fn thread_cpu_ns() -> u64 {
    // SAFETY: the pseudo-handle is valid for the calling thread; cycles is a live out-pointer.
    let mut cycles = 0;
    unsafe { QueryThreadCycleTime(GetCurrentThread(), &mut cycles) };
    cycles_to_ns(cycles)
}

/// Starts the sampler thread once and leaves it waiting (idle when nothing is armed).
pub fn install_handler() -> io::Result<()> {
    static STARTED: OnceLock<Result<(), String>> = OnceLock::new();
    let result = STARTED.get_or_init(|| {
        cycles_per_sec();
        std::thread::Builder::new()
            .name("cpu sampler".into())
            .spawn(run)
            .map(drop)
            .map_err(|e| e.to_string())
    });
    result.clone().map_err(io::Error::other)
}

/// A waitable timer with sub-millisecond resolution (Windows 10 1803 and later), else none: the loop sleeps instead.
struct Waiter(HANDLE);

impl Waiter {
    fn new() -> Self {
        // SAFETY: no name or security attributes; a null handle on failure is handled by `until`.
        Self(unsafe {
            CreateWaitableTimerExW(
                std::ptr::null(),
                std::ptr::null(),
                CREATE_WAITABLE_TIMER_HIGH_RESOLUTION,
                TIMER_ALL_ACCESS,
            )
        })
    }

    fn until(&self, at: Instant) {
        let wait = at.saturating_duration_since(Instant::now());
        if wait.is_zero() {
            return;
        }
        // Relative due times are negative, in 100 ns units.
        let due = -((wait.as_nanos() / 100).max(1) as i64);
        // SAFETY: the handle is a live waitable timer; due is a live local; no completion routine.
        let set = !self.0.is_null()
            && unsafe { SetWaitableTimer(self.0, &due, 0, None, std::ptr::null(), 0) } != 0;
        if set {
            // SAFETY: as above.
            unsafe { WaitForSingleObject(self.0, INFINITE) };
        } else {
            std::thread::sleep(wait);
        }
    }
}

fn run() {
    let waiter = Waiter::new();
    // A late visit costs the profile its timing, so the sampler runs ahead of the game's threads.
    // SAFETY: the pseudo-handle is valid for the calling thread.
    unsafe { SetThreadPriority(GetCurrentThread(), THREAD_PRIORITY_TIME_CRITICAL) };
    let mut sampler = SAMPLER.lock().unwrap();
    loop {
        if sampler.armed.is_empty() {
            sampler = ARMED.wait(sampler).unwrap();
            continue;
        }
        let now = Instant::now();
        for armed in sampler.armed.iter_mut().filter(|a| a.due <= now) {
            // CPU timers keep their phase and catch up (`MAX_CATCH_UP`). A wall visit comes a whole period after the
            // last one: "running" means more than half a period of CPU since then, so a short gap would read as waiting.
            armed.due = if armed.wall {
                now + armed.period
            } else {
                (armed.due + armed.period).max(now)
            };
            visit(armed);
        }
        let next = sampler.armed.iter().map(|a| a.due).min().unwrap_or(now);
        drop(sampler);
        waiter.until(next);
        sampler = SAMPLER.lock().unwrap();
    }
}

/// The 16-byte alignment GetThreadContext requires of a CONTEXT.
#[repr(C, align(16))]
struct Aligned(CONTEXT);

/// Samples one armed thread if its timer owes a sample: suspend, read the registers, copy the stack, resume.
fn visit(armed: &mut Armed) {
    let state = &*armed.state;
    let cycles = state.target.cycles();
    let ran = cycles.saturating_sub(std::mem::replace(&mut armed.cycles, cycles));
    let count = if armed.wall {
        1
    } else {
        let period = (armed.period.as_secs_f64() * cycles_per_sec()) as u64;
        armed.owed = armed.owed.saturating_add(ran);
        let count = (armed.owed / period.max(1)).min(MAX_CATCH_UP);
        armed.owed = (armed.owed - count * period).min(period);
        count
    };
    if count == 0 {
        return;
    }
    let timed = state.seen.load(Relaxed).is_multiple_of(TIME_EVERY);
    let started = if timed { thread_cpu_ns() } else { 0 };
    let handle = state.target.0;
    // SAFETY: a live thread handle with suspend rights; it is resumed below on every path.
    if unsafe { SuspendThread(handle) } == u32::MAX {
        return;
    }
    let mut context = Aligned(CONTEXT {
        ContextFlags: CONTEXT_CONTROL_AMD64 | CONTEXT_INTEGER_AMD64,
        ..CONTEXT::default()
    });
    // GetThreadContext also waits until the suspension has taken effect.
    // SAFETY: the handle has get-context rights and the CONTEXT is 16-byte aligned.
    let mut recorded = false;
    if unsafe { GetThreadContext(handle, &mut context.0) } != 0 {
        let c = &context.0;
        let regs = Regs {
            pc: c.Rip as usize,
            fp: c.Rbp as usize,
            sp: c.Rsp as usize,
            lr: 0,
        };
        for _ in 0..count {
            // SAFETY: the thread is suspended and these are its registers, so its stack above sp stays put.
            recorded |=
                unsafe { super::record_sample(state, regs, armed.wall, cycles_to_ns(cycles)) };
        }
    }
    // SAFETY: suspended above.
    unsafe { ResumeThread(handle) };
    if recorded && timed {
        state.add_timed(thread_cpu_ns().saturating_sub(started));
    }
}

/// The modules loaded in the process now, with their files' paths.
pub(crate) fn loaded_modules() -> Vec<Loaded> {
    // SAFETY: the pseudo-handle is valid for this process; every buffer passed is live and sized as stated.
    unsafe {
        let process = GetCurrentProcess();
        let mut modules: Vec<HMODULE> = vec![std::ptr::null_mut(); 512];
        let mut needed = 0;
        loop {
            let bytes = (modules.len() * size_of::<HMODULE>()) as u32;
            if EnumProcessModules(process, modules.as_mut_ptr(), bytes, &mut needed) == 0 {
                return Vec::new();
            }
            if needed <= bytes {
                break;
            }
            modules.resize(needed as usize / size_of::<HMODULE>(), std::ptr::null_mut());
        }
        modules.truncate(needed as usize / size_of::<HMODULE>());
        let mut name = vec![0u16; 1024];
        modules
            .into_iter()
            .filter_map(|module| {
                let mut info: MODULEINFO = std::mem::zeroed();
                let size = size_of::<MODULEINFO>() as u32;
                if GetModuleInformation(process, module, &mut info, size) == 0 {
                    return None;
                }
                let len =
                    GetModuleFileNameExW(process, module, name.as_mut_ptr(), name.len() as u32);
                let base = info.lpBaseOfDll as u64;
                (len > 0).then(|| Loaded {
                    path: String::from_utf16_lossy(&name[..len as usize]),
                    base,
                    range: base..base + u64::from(info.SizeOfImage),
                })
            })
            .collect()
    }
}
