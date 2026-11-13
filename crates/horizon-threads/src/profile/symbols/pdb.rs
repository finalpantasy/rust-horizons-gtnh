//! Windows: names from each module's PDB (pdb-addr2line), found through the module's CodeView record.

use std::fs::File;
use std::path::{Path, PathBuf};

use object::{Object, ObjectSection};
use pdb_addr2line::pdb::{FallibleIterator, PDB, SymbolData, SymbolIndex, SymbolTable};
use pdb_addr2line::{Context, ContextPdbData, TypeFormatterFlags};

use super::{Sym, SymbolQuality, Symbols, base_name, demangled};
use crate::sampler::Loaded;

/// The PDB the linker wrote for the module at `path`: at the path its CodeView record names, else beside the module.
/// None when there is none whose GUID matches the module's (a stale PDB from another build). With it, the module's
/// functions from `.pdata` as (start, end) RVAs, sorted by start: every x64 function that calls or saves a register
/// has one, a leaf function doesn't.
fn pdb_for(path: &str) -> Option<(PDB<'static, File>, Vec<(u32, u32)>)> {
    let file = File::open(path).ok()?;
    // SAFETY: the mapping is read-only and dropped before this returns; a file truncated meanwhile could fault, which a profiler tolerates.
    let map = unsafe { memmap2::Mmap::map(&file) }.ok()?;
    let object = object::File::parse(&*map).ok()?;
    let codeview = object.pdb_info().ok()??;
    let guid = codeview.guid();
    let recorded = PathBuf::from(String::from_utf8_lossy(codeview.path()).into_owned());
    let beside = Path::new(path).with_file_name(recorded.file_name()?);
    let pdb = [recorded, beside].into_iter().find_map(|p| {
        let mut pdb = PDB::open(File::open(p).ok()?).ok()?;
        (pdb.pdb_information().ok()?.guid.to_bytes_le() == guid).then_some(pdb)
    })?;
    let pdata = object
        .section_by_name(".pdata")
        .and_then(|s| s.data().ok())
        .unwrap_or_default();
    // RUNTIME_FUNCTION: begin, end, unwind info; the section's padding reads as empty entries.
    let mut functions: Vec<(u32, u32)> = pdata
        .as_chunks::<12>()
        .0
        .iter()
        .map(|e| {
            let word = |i: usize| u32::from_le_bytes([e[i], e[i + 1], e[i + 2], e[i + 3]]);
            (word(0), word(4))
        })
        .filter(|(start, end)| start < end)
        .collect();
    functions.sort_unstable();
    Some((pdb, functions))
}

/// Whether any module in the PDB has line records. A build without debug info has none, nor procedure records: its
/// PDB names functions only through public symbols, and only those linked across codegen units.
fn has_lines(pdb: &mut PDB<'static, File>) -> bool {
    let Ok(dbi) = pdb.debug_information() else {
        return false;
    };
    let Ok(mut modules) = dbi.modules() else {
        return false;
    };
    let mut any = false;
    while let Ok(Some(module)) = modules.next() {
        any |= module.info().c13_lines_size > 0;
    }
    any
}

/// The PDB's function public symbols by address. They carry the full path, which a line-tables-only build's procedure
/// records leave out, as the symbol table does for DWARF on Linux. Only the names asked for are read and demangled.
#[derive(Default)]
struct Publics {
    table: Option<SymbolTable<'static>>,
    by_rva: Vec<(u32, SymbolIndex)>,
}

impl Publics {
    fn read(pdb: &mut PDB<'static, File>) -> Self {
        let (Ok(map), Ok(table)) = (pdb.address_map(), pdb.global_symbols()) else {
            return Self::default();
        };
        let mut by_rva = Vec::new();
        let mut iter = table.iter();
        while let Ok(Some(symbol)) = iter.next() {
            if let Ok(SymbolData::Public(p)) = symbol.parse()
                && p.function
                && let Some(rva) = p.offset.to_rva(&map)
            {
                by_rva.push((rva.0, symbol.index()));
            }
        }
        by_rva.sort_unstable_by_key(|p| p.0);
        Self {
            table: Some(table),
            by_rva,
        }
    }

    /// The name of the public symbol at `rva`.
    fn name(&self, rva: u32) -> Option<String> {
        let at = self.by_rva.binary_search_by_key(&rva, |p| p.0).ok()?;
        let symbol = self
            .table
            .as_ref()?
            .iter_at(self.by_rva[at].1)
            .next()
            .ok()??;
        match symbol.parse() {
            Ok(SymbolData::Public(p)) => Some(demangled(&p.name.to_string())),
            _ => None,
        }
    }
}

/// A module's public symbols and its `.pdata` functions (see [`pdb_for`]).
#[derive(Default)]
struct Names {
    publics: Publics,
    functions: Vec<(u32, u32)>,
}

/// Runs `f` with the module's procedure, line and inline records and its other names. The records are None without a
/// matching PDB, or in one without line records: there pdb-addr2line would end each public symbol at the next one, and
/// so name a local function after its neighbour.
fn with_pdb<R>(path: &str, f: impl FnOnce(Option<&Context>, &Names) -> R) -> R {
    let mut found = pdb_for(path);
    let names = found
        .as_mut()
        .map_or_else(Names::default, |(pdb, functions)| Names {
            publics: Publics::read(pdb),
            functions: std::mem::take(functions),
        });
    let data = found
        .as_mut()
        .and_then(|(pdb, _)| has_lines(pdb).then_some(pdb))
        .and_then(|pdb| ContextPdbData::try_from_pdb_ref(pdb).ok());
    // Names as Linux reports them: no argument list or return type.
    let flags = TypeFormatterFlags::NO_ARGUMENTS | TypeFormatterFlags::NO_FUNCTION_RETURN;
    let context = data
        .as_ref()
        .and_then(|d| d.make_context_with_formatter_flags(flags).ok());
    f(context.as_ref(), &names)
}

/// The frames at `rva`, innermost inlined function first; empty when the PDB names nothing there.
fn frames_at(context: Option<&Context>, names: &Names, rva: u64) -> Vec<Sym> {
    let Ok(rva) = u32::try_from(rva) else {
        return Vec::new();
    };
    let found = context.and_then(|c| c.find_frames(rva).ok().flatten());
    let start = found.as_ref().map(|f| f.start_rva);
    let mut frames: Vec<Sym> = found.map_or_else(Vec::new, |f| {
        f.frames
            .into_iter()
            .map(|frame| Sym {
                name: frame.function.as_deref().map(demangled).unwrap_or_default(),
                file: frame.file.as_deref().map(base_name),
                line: frame.line.unwrap_or(0),
            })
            .collect()
    });
    // The public symbol at the function's start. With no procedure there, the function is the `.pdata` one around
    // `rva`: a public symbol has no size, so the nearest one below may belong to another function.
    let start = start.or_else(|| {
        let at = names
            .functions
            .partition_point(|f| f.0 <= rva)
            .checked_sub(1)?;
        let (start, end) = names.functions[at];
        (rva < end).then_some(start)
    });
    let public = start.and_then(|start| names.publics.name(start));
    if let Some(name) = public {
        match frames.last_mut() {
            Some(outer) => outer.name = name,
            None => frames.push(Sym {
                name,
                file: None,
                line: 0,
            }),
        }
    }
    frames
}

/// How well [`super::symbolize`] can name the functions of the running executable. Reads only the PDB's module list,
/// not its symbols: a capture asks at its start.
pub fn symbol_quality() -> SymbolQuality {
    let Some((mut pdb, _)) = std::env::current_exe()
        .ok()
        .and_then(|exe| pdb_for(exe.to_str()?))
    else {
        return SymbolQuality::None;
    };
    match has_lines(&mut pdb) {
        true => SymbolQuality::Dwarf,
        false => SymbolQuality::Symtab,
    }
}

pub(super) fn resolve_module(module: &Loaded, addrs: &[u64], out: &mut Symbols) {
    with_pdb(&module.path, |context, names| {
        for &addr in addrs {
            let rva = addr.wrapping_sub(module.base);
            let mut frames = frames_at(context, names, rva);
            if frames.is_empty() {
                frames.push(Sym {
                    name: String::new(),
                    file: None,
                    line: 0,
                });
            }
            for frame in &mut frames {
                if frame.name.is_empty() {
                    frame.name = format!("[{} 0x{rva:x}]", base_name(&module.path));
                }
            }
            out.frames.insert(addr, frames);
            out.offsets.insert(addr, rva);
        }
    });
}
