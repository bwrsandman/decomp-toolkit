//! Classic Mac OS PowerPC PEF (Preferred Executable Format) reader/writer.
//!
//! PEF is the container used by CFM (Code Fragment Manager) executables on
//! classic Mac OS / early Mac OS X PowerPC builds (e.g. Black & White Mac).
//! Container layout:
//!   - `PefFileHeader` (40 bytes) at file offset 0
//!   - `PefSectionHeader` table (28 bytes each) immediately following
//!   - Section name table (packed C strings) after section headers
//!   - Section containers at their `container_offset`
//!
//! One section (kind == Loader) holds a `PefLoaderInfoHeader`, an imported
//! library table, an imported symbol table, a relocation header table + opcode
//! stream, an export hash table and a loader string table.
//!
//! Currently implemented:
//!   - FileHeader + SectionHeader parse
//!   - Section data extraction for Code / UnpackedData / ConstantData
//!   - Loader parse: imported libraries + imported symbols → extern ObjSymbols
//!                   exported symbol hash table → defined ObjSymbols
//!   - Entry points (main/init/term) → function ObjSymbols
//!
//! Not yet implemented (tracked in TODO.md):
//!   - Relocation opcode VM (`apply_pef_relocations` is a no-op)
//!   - CodeWarrior traceback table scan for in-code function names / sizes
//!   - PatternInitData decompression
//!   - PEF writer (`write_pef`) for relink step

use anyhow::{Context, Result, bail};
use cwdemangle::demangle;

use crate::{
    array_ref,
    obj::{
        ObjArchitecture, ObjInfo, ObjKind, ObjSection, ObjSectionKind, ObjSymbol,
        ObjSymbolFlagSet, ObjSymbolFlags, ObjSymbolKind,
        SectionIndex as ObjSectionIndex,
    },
};

pub const PEF_MAGIC_TAG1: u32 = 0x4A6F_7921; // "Joy!"
pub const PEF_MAGIC_TAG2: u32 = 0x7065_6666; // "peff"
pub const PEF_ARCH_PPC: u32 = 0x7077_7063; // "pwpc"
pub const PEF_ARCH_M68K: u32 = 0x6D36_386B; // "m68k"

pub const PEF_FILE_HEADER_SIZE: usize = 40;
pub const PEF_SECTION_HEADER_SIZE: usize = 28;
pub const PEF_LOADER_INFO_HEADER_SIZE: usize = 56;
pub const PEF_IMPORTED_LIBRARY_SIZE: usize = 24;
pub const PEF_EXPORTED_SYMBOL_SIZE: usize = 10;

// PEF imported-symbol class codes (low nibble of class byte).
pub const PEF_CLASS_CODE: u8 = 0;
pub const PEF_CLASS_DATA: u8 = 1;
pub const PEF_CLASS_TVECTOR: u8 = 2;
pub const PEF_CLASS_TOC: u8 = 3;
pub const PEF_CLASS_GLUE: u8 = 4;
pub const PEF_CLASS_UNDEFINED: u8 = 0x0F;

// PEF imported-symbol flags (high nibble of class byte).
pub const PEF_WEAK_IMPORT: u8 = 0x80;

// PEF exported-symbol sectionIndex sentinels.
pub const PEF_EXPORT_ABSOLUTE: i16 = -2;
pub const PEF_EXPORT_REEXPORT: i16 = -3;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum PefSectionKind {
    Code = 0,
    UnpackedData = 1,
    PatternInitData = 2,
    ConstantData = 3,
    Loader = 4,
    Debug = 5,
    ExecutableData = 6,
    Exception = 7,
    Traceback = 8,
}

impl PefSectionKind {
    pub fn from_u8(v: u8) -> Option<Self> {
        Some(match v {
            0 => Self::Code,
            1 => Self::UnpackedData,
            2 => Self::PatternInitData,
            3 => Self::ConstantData,
            4 => Self::Loader,
            5 => Self::Debug,
            6 => Self::ExecutableData,
            7 => Self::Exception,
            8 => Self::Traceback,
            _ => return None,
        })
    }

    pub fn short_name(self) -> &'static str {
        match self {
            Self::Code => "code",
            Self::UnpackedData => "data",
            Self::PatternInitData => "pidata",
            Self::ConstantData => "rdata",
            Self::Loader => "loader",
            Self::Debug => "debug",
            Self::ExecutableData => "xdata",
            Self::Exception => "except",
            Self::Traceback => "trace",
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct PefFileHeader {
    pub tag1: u32,
    pub tag2: u32,
    pub architecture: u32,
    pub format_version: u32,
    pub date_time_stamp: u32,
    pub old_def_version: u32,
    pub old_imp_version: u32,
    pub current_version: u32,
    pub section_count: u16,
    pub inst_section_count: u16,
    pub reserved_a: u32,
}

impl PefFileHeader {
    pub fn parse(data: &[u8]) -> Result<Self> {
        if data.len() < PEF_FILE_HEADER_SIZE {
            bail!("PEF file too small: {} < {}", data.len(), PEF_FILE_HEADER_SIZE);
        }
        let h = Self {
            tag1: u32::from_be_bytes(*array_ref!(data, 0, 4)),
            tag2: u32::from_be_bytes(*array_ref!(data, 4, 4)),
            architecture: u32::from_be_bytes(*array_ref!(data, 8, 4)),
            format_version: u32::from_be_bytes(*array_ref!(data, 12, 4)),
            date_time_stamp: u32::from_be_bytes(*array_ref!(data, 16, 4)),
            old_def_version: u32::from_be_bytes(*array_ref!(data, 20, 4)),
            old_imp_version: u32::from_be_bytes(*array_ref!(data, 24, 4)),
            current_version: u32::from_be_bytes(*array_ref!(data, 28, 4)),
            section_count: u16::from_be_bytes(*array_ref!(data, 32, 2)),
            inst_section_count: u16::from_be_bytes(*array_ref!(data, 34, 2)),
            reserved_a: u32::from_be_bytes(*array_ref!(data, 36, 4)),
        };
        if h.tag1 != PEF_MAGIC_TAG1 || h.tag2 != PEF_MAGIC_TAG2 {
            bail!(
                "Not a PEF file (magic {:08X} {:08X}, expected {:08X} {:08X})",
                h.tag1, h.tag2, PEF_MAGIC_TAG1, PEF_MAGIC_TAG2
            );
        }
        if h.architecture != PEF_ARCH_PPC {
            bail!(
                "Unsupported PEF architecture {:08X} (only PowerPC 'pwpc' supported)",
                h.architecture
            );
        }
        if h.format_version != 1 {
            bail!("Unsupported PEF format version {}", h.format_version);
        }
        Ok(h)
    }
}

#[derive(Debug, Clone, Copy)]
pub struct PefSectionHeader {
    /// Offset into the section name table. `-1` (0xFFFFFFFF) means unnamed.
    pub name_offset: i32,
    pub default_address: u32,
    pub total_size: u32,
    pub unpacked_size: u32,
    pub container_size: u32,
    pub container_offset: u32,
    pub section_kind: u8,
    pub share_kind: u8,
    pub alignment: u8,
    pub reserved_b: u8,
}

impl PefSectionHeader {
    pub fn parse(data: &[u8]) -> Result<Self> {
        if data.len() < PEF_SECTION_HEADER_SIZE {
            bail!("PEF section header truncated");
        }
        Ok(Self {
            name_offset: i32::from_be_bytes(*array_ref!(data, 0, 4)),
            default_address: u32::from_be_bytes(*array_ref!(data, 4, 4)),
            total_size: u32::from_be_bytes(*array_ref!(data, 8, 4)),
            unpacked_size: u32::from_be_bytes(*array_ref!(data, 12, 4)),
            container_size: u32::from_be_bytes(*array_ref!(data, 16, 4)),
            container_offset: u32::from_be_bytes(*array_ref!(data, 20, 4)),
            section_kind: data[24],
            share_kind: data[25],
            alignment: data[26],
            reserved_b: data[27],
        })
    }

    pub fn kind(&self) -> Option<PefSectionKind> { PefSectionKind::from_u8(self.section_kind) }
}

/// Parsed PEF container: file header + section headers + resolved names.
/// Kept separate from `ObjInfo` so `pef info` can dump raw container
/// structure without running the full loader analysis.
#[derive(Debug, Clone)]
pub struct PefContainer {
    pub header: PefFileHeader,
    pub sections: Vec<PefSectionHeader>,
    pub section_names: Vec<Option<String>>,
}

impl PefContainer {
    pub fn parse(data: &[u8]) -> Result<Self> {
        let header = PefFileHeader::parse(data).context("Parsing PEF file header")?;
        let sh_table_off = PEF_FILE_HEADER_SIZE;
        let section_count = header.section_count as usize;
        let sh_table_end =
            sh_table_off.checked_add(section_count.checked_mul(PEF_SECTION_HEADER_SIZE).context(
                "PEF section header table size overflow",
            )?).context("PEF section header table offset overflow")?;
        if data.len() < sh_table_end {
            bail!(
                "PEF section header table extends past EOF ({} < {})",
                data.len(),
                sh_table_end
            );
        }
        let mut sections = Vec::with_capacity(section_count);
        for i in 0..section_count {
            let off = sh_table_off + i * PEF_SECTION_HEADER_SIZE;
            sections.push(
                PefSectionHeader::parse(&data[off..off + PEF_SECTION_HEADER_SIZE])
                    .with_context(|| format!("Parsing section header {i}"))?,
            );
        }

        // Section name table begins immediately after the section header table.
        // Names are NUL-terminated C strings.  Length of the table is not
        // recorded in the header; callers read names lazily by offset.
        let name_table_start = sh_table_end;
        let mut section_names = Vec::with_capacity(section_count);
        for sh in &sections {
            if sh.name_offset == -1 {
                section_names.push(None);
                continue;
            }
            let abs = name_table_start
                .checked_add(sh.name_offset as u32 as usize)
                .context("Section name offset overflow")?;
            section_names.push(Some(read_c_string(data, abs)?.to_string()));
        }

        Ok(Self { header, sections, section_names })
    }
}

/// PEF Loader Info Header (56 bytes, at offset 0 of the Loader section container).
#[derive(Debug, Clone, Copy)]
pub struct PefLoaderInfoHeader {
    pub main_section: i32,
    pub main_offset: u32,
    pub init_section: i32,
    pub init_offset: u32,
    pub term_section: i32,
    pub term_offset: u32,
    pub imported_library_count: u32,
    pub total_imported_symbol_count: u32,
    pub reloc_section_count: u32,
    pub reloc_instr_offset: u32,
    pub loader_strings_offset: u32,
    pub export_hash_offset: u32,
    pub export_hash_table_power: u32,
    pub exported_symbol_count: u32,
}

impl PefLoaderInfoHeader {
    pub fn parse(loader: &[u8]) -> Result<Self> {
        if loader.len() < PEF_LOADER_INFO_HEADER_SIZE {
            bail!("Loader section too small for info header");
        }
        Ok(Self {
            main_section: i32::from_be_bytes(*array_ref!(loader, 0, 4)),
            main_offset: u32::from_be_bytes(*array_ref!(loader, 4, 4)),
            init_section: i32::from_be_bytes(*array_ref!(loader, 8, 4)),
            init_offset: u32::from_be_bytes(*array_ref!(loader, 12, 4)),
            term_section: i32::from_be_bytes(*array_ref!(loader, 16, 4)),
            term_offset: u32::from_be_bytes(*array_ref!(loader, 20, 4)),
            imported_library_count: u32::from_be_bytes(*array_ref!(loader, 24, 4)),
            total_imported_symbol_count: u32::from_be_bytes(*array_ref!(loader, 28, 4)),
            reloc_section_count: u32::from_be_bytes(*array_ref!(loader, 32, 4)),
            reloc_instr_offset: u32::from_be_bytes(*array_ref!(loader, 36, 4)),
            loader_strings_offset: u32::from_be_bytes(*array_ref!(loader, 40, 4)),
            export_hash_offset: u32::from_be_bytes(*array_ref!(loader, 44, 4)),
            export_hash_table_power: u32::from_be_bytes(*array_ref!(loader, 48, 4)),
            exported_symbol_count: u32::from_be_bytes(*array_ref!(loader, 52, 4)),
        })
    }
}

#[derive(Debug, Clone)]
pub struct PefImportedLibrary {
    pub name: String,
    pub old_imp_version: u32,
    pub current_version: u32,
    pub imported_symbol_count: u32,
    pub first_imported_symbol: u32,
    pub options: u8,
}

#[derive(Debug, Clone)]
pub struct PefImportedSymbol {
    pub name: String,
    /// Low nibble of the class byte (code/data/tvector/toc/glue/undefined).
    pub symbol_class: u8,
    /// High nibble of the class byte (flags; weak-import etc.).
    pub flags: u8,
    /// Index into the imported library table.
    pub library_index: u32,
}

#[derive(Debug, Clone)]
pub struct PefExportedSymbol {
    pub name: String,
    pub symbol_class: u8,
    pub value: u32,
    pub section_index: i16,
}

/// Resolve a NUL-terminated C string anchored at `abs` inside `data`.
fn read_c_string(data: &[u8], abs: usize) -> Result<&str> {
    if abs > data.len() {
        bail!("String offset {abs:#x} past EOF ({:#x})", data.len());
    }
    let end = data[abs..]
        .iter()
        .position(|&b| b == 0)
        .map(|p| abs + p)
        .unwrap_or(data.len());
    std::str::from_utf8(&data[abs..end])
        .with_context(|| format!("Non-UTF-8 string at offset {abs:#x}"))
}

fn pef_class_to_symbol_kind(class: u8) -> ObjSymbolKind {
    match class {
        PEF_CLASS_CODE | PEF_CLASS_GLUE => ObjSymbolKind::Function,
        PEF_CLASS_DATA | PEF_CLASS_TVECTOR | PEF_CLASS_TOC => ObjSymbolKind::Object,
        _ => ObjSymbolKind::Unknown,
    }
}

/// Parse the PEF Loader section.  Produces the loader header, the imported
/// library + symbol tables, and the exported symbol table.
pub fn parse_loader_section(
    loader: &[u8],
) -> Result<(PefLoaderInfoHeader, Vec<PefImportedLibrary>, Vec<PefImportedSymbol>, Vec<PefExportedSymbol>)>
{
    let info = PefLoaderInfoHeader::parse(loader)?;
    let strings_base = info.loader_strings_offset as usize;

    // Imported library table (24 bytes each), immediately after the header.
    let mut libraries = Vec::with_capacity(info.imported_library_count as usize);
    for i in 0..info.imported_library_count as usize {
        let off = PEF_LOADER_INFO_HEADER_SIZE + i * PEF_IMPORTED_LIBRARY_SIZE;
        if off + PEF_IMPORTED_LIBRARY_SIZE > loader.len() {
            bail!("Imported library {i} truncated");
        }
        let entry = &loader[off..off + PEF_IMPORTED_LIBRARY_SIZE];
        let name_off = u32::from_be_bytes(*array_ref!(entry, 0, 4));
        let old_imp = u32::from_be_bytes(*array_ref!(entry, 4, 4));
        let cur_ver = u32::from_be_bytes(*array_ref!(entry, 8, 4));
        let sym_count = u32::from_be_bytes(*array_ref!(entry, 12, 4));
        let first_sym = u32::from_be_bytes(*array_ref!(entry, 16, 4));
        let options = entry[20];
        libraries.push(PefImportedLibrary {
            name: read_c_string(loader, strings_base + name_off as usize)?.to_string(),
            old_imp_version: old_imp,
            current_version: cur_ver,
            imported_symbol_count: sym_count,
            first_imported_symbol: first_sym,
            options,
        });
    }

    // Imported symbol table (4 bytes per entry), immediately after the library table.
    let imp_sym_base =
        PEF_LOADER_INFO_HEADER_SIZE + libraries.len() * PEF_IMPORTED_LIBRARY_SIZE;
    let mut imported_symbols =
        Vec::with_capacity(info.total_imported_symbol_count as usize);
    for i in 0..info.total_imported_symbol_count as usize {
        let off = imp_sym_base + i * 4;
        if off + 4 > loader.len() {
            bail!("Imported symbol {i} truncated");
        }
        let raw = u32::from_be_bytes(*array_ref!(loader, off, 4));
        let class_byte = (raw >> 24) as u8;
        let name_off = raw & 0x00FF_FFFF;
        let name = read_c_string(loader, strings_base + name_off as usize)?.to_string();

        // Find which library this symbol belongs to (first_imported_symbol ranges).
        let library_index = libraries
            .iter()
            .enumerate()
            .find(|(_, lib)| {
                let start = lib.first_imported_symbol as usize;
                let end = start + lib.imported_symbol_count as usize;
                (start..end).contains(&i)
            })
            .map(|(idx, _)| idx as u32)
            .unwrap_or(u32::MAX);

        imported_symbols.push(PefImportedSymbol {
            name,
            symbol_class: class_byte & 0x0F,
            flags: class_byte & 0xF0,
            library_index,
        });
    }

    // Exported symbol table.  Walk the export key table + exported symbol
    // array in parallel.  We don't actually need the hash table itself to
    // enumerate exports — it only accelerates by-name lookup.
    //
    // Layout starting at export_hash_offset:
    //   PEFExportedSymbolHashSlot    hashTable[1 << exportHashTablePower]  (u32)
    //   PEFExportedSymbolKey         keyTable [exportedSymbolCount]        (u32)
    //   PEFExportedSymbol            symTable [exportedSymbolCount]        (10 bytes)
    let export_hash_start = info.export_hash_offset as usize;
    let hash_slot_count = 1usize << info.export_hash_table_power;
    let export_table_start = export_hash_start
        .checked_add(hash_slot_count.checked_mul(4).context("hash slots overflow")?)
        .context("export_hash_offset overflow")?
        .checked_add((info.exported_symbol_count as usize).checked_mul(4).context("key table overflow")?)
        .context("key table offset overflow")?;
    let mut exported_symbols = Vec::with_capacity(info.exported_symbol_count as usize);
    for i in 0..info.exported_symbol_count as usize {
        let off = export_table_start + i * PEF_EXPORTED_SYMBOL_SIZE;
        if off + PEF_EXPORTED_SYMBOL_SIZE > loader.len() {
            bail!("Exported symbol {i} truncated");
        }
        let entry = &loader[off..off + PEF_EXPORTED_SYMBOL_SIZE];
        let class_and_name = u32::from_be_bytes(*array_ref!(entry, 0, 4));
        let value = u32::from_be_bytes(*array_ref!(entry, 4, 4));
        let section_index = i16::from_be_bytes(*array_ref!(entry, 8, 2));
        let class = ((class_and_name >> 24) & 0xFF) as u8;
        let name_off = class_and_name & 0x00FF_FFFF;
        let name = read_c_string(loader, strings_base + name_off as usize)?.to_string();
        exported_symbols.push(PefExportedSymbol {
            name,
            symbol_class: class & 0x0F,
            value,
            section_index,
        });
    }

    Ok((info, libraries, imported_symbols, exported_symbols))
}

/// Parse a PEF binary into an `ObjInfo`.
///
/// Converts instantiated sections (Code / UnpackedData / ConstantData /
/// PatternInitData) into `ObjSection`s, then parses the Loader section to
/// populate external and exported `ObjSymbols`.  Relocations are filled in
/// later by `apply_pef_relocations` (P3).
pub fn process_pef(data: &[u8], name: &str) -> Result<(ObjInfo, Option<u32>)> {
    let container = PefContainer::parse(data)?;

    // Map PEF physical section index → ObjSection index (or None if skipped).
    let mut pef_to_obj: Vec<Option<ObjSectionIndex>> = vec![None; container.sections.len()];
    let mut sections: Vec<ObjSection> = Vec::new();
    let mut loader_bytes: Option<&[u8]> = None;

    for (pef_idx, sh) in container.sections.iter().enumerate() {
        let Some(kind) = sh.kind() else {
            log::warn!("Skipping PEF section {pef_idx}: unknown kind {}", sh.section_kind);
            continue;
        };

        if matches!(kind, PefSectionKind::Loader) {
            let end = (sh.container_offset as usize)
                .checked_add(sh.container_size as usize)
                .context("Loader container offset overflow")?;
            if end > data.len() {
                bail!("Loader section {pef_idx} extends past EOF");
            }
            loader_bytes = Some(&data[sh.container_offset as usize..end]);
            continue;
        }

        let (obj_kind, section_data): (ObjSectionKind, Vec<u8>) = match kind {
            PefSectionKind::Code => (
                ObjSectionKind::Code,
                read_container(data, sh).context("Reading code container")?,
            ),
            PefSectionKind::ConstantData => (
                ObjSectionKind::ReadOnlyData,
                read_container(data, sh).context("Reading const data container")?,
            ),
            PefSectionKind::UnpackedData => {
                let mut buf = read_container(data, sh).context("Reading unpacked data container")?;
                // PEF allows total_size > unpacked_size; trailing gap is
                // zero-initialised BSS handled downstream by split logic.
                if sh.total_size as usize > buf.len() {
                    buf.resize(sh.total_size as usize, 0);
                }
                (ObjSectionKind::Data, buf)
            }
            PefSectionKind::ExecutableData => (
                ObjSectionKind::Data,
                read_container(data, sh).context("Reading xdata container")?,
            ),
            PefSectionKind::PatternInitData => {
                // TODO (P5): decompress pattern stream.  For now, allocate a
                // zero buffer of the unpacked size so section indices stay
                // stable and downstream analysis has correct extents.
                log::warn!(
                    "PEF section {pef_idx}: PatternInitData decompression not yet implemented; \
                     using zero-filled placeholder ({} bytes)",
                    sh.unpacked_size
                );
                (ObjSectionKind::Data, vec![0u8; sh.unpacked_size as usize])
            }
            PefSectionKind::Loader => unreachable!(),
            PefSectionKind::Debug
            | PefSectionKind::Exception
            | PefSectionKind::Traceback => continue,
        };

        let section_name = container
            .section_names
            .get(pef_idx)
            .and_then(|n| n.clone())
            .unwrap_or_else(|| format!(".{}{pef_idx}", kind.short_name()));

        let align = if sh.alignment == 0 { 1u64 } else { 1u64 << sh.alignment };
        let obj_idx = sections.len() as ObjSectionIndex;
        pef_to_obj[pef_idx] = Some(obj_idx);
        sections.push(ObjSection {
            name: section_name,
            kind: obj_kind,
            address: sh.default_address as u64,
            size: sh.total_size as u64,
            data: section_data,
            align,
            elf_index: pef_idx as ObjSectionIndex,
            relocations: Default::default(),
            virtual_address: None,
            file_offset: sh.container_offset as u64,
            section_known: true,
            splits: Default::default(),
        });
    }

    // Parse Loader section → symbols.  Missing Loader section is fatal: every
    // real PEF executable has one.
    let Some(loader) = loader_bytes else {
        bail!("PEF has no Loader section");
    };
    let (info, libraries, imported_symbols, exported_symbols) =
        parse_loader_section(loader).context("Parsing PEF loader section")?;
    log::debug!(
        "PEF loader: {} libraries, {} imports, {} exports",
        libraries.len(),
        imported_symbols.len(),
        exported_symbols.len()
    );

    // Build ObjSymbols.
    let mut symbols: Vec<ObjSymbol> = Vec::new();

    // Imported symbols become extern (section = None).  Prefix weak imports
    // with the library name so same-name symbols from different libs don't
    // collide.
    for imp in &imported_symbols {
        let lib_name = libraries
            .get(imp.library_index as usize)
            .map(|l| l.name.as_str())
            .unwrap_or("<unknown>");
        let mut flags = ObjSymbolFlagSet(ObjSymbolFlags::Global.into());
        if imp.flags & PEF_WEAK_IMPORT != 0 {
            flags.set_scope(crate::obj::ObjSymbolScope::Weak);
        }
        let demangled = demangle(&imp.name, &Default::default());
        symbols.push(ObjSymbol {
            name: imp.name.clone(),
            demangled_name: demangled,
            address: 0,
            section: None,
            size: 0,
            size_known: false,
            flags,
            kind: pef_class_to_symbol_kind(imp.symbol_class),
            ..Default::default()
        });
        log::trace!("import {:>2}:{} {} ({})", imp.library_index, imp.name, lib_name, imp.symbol_class);
    }

    // Exported symbols become defined symbols at (section.default_address + value).
    for exp in &exported_symbols {
        match exp.section_index {
            PEF_EXPORT_ABSOLUTE => {
                // Absolute export: no section anchor; value is the absolute address.
                symbols.push(ObjSymbol {
                    name: exp.name.clone(),
                    demangled_name: demangle(&exp.name, &Default::default()),
                    address: exp.value as u64,
                    section: None,
                    size: 0,
                    size_known: false,
                    flags: ObjSymbolFlagSet(ObjSymbolFlags::Global | ObjSymbolFlags::Exported),
                    kind: pef_class_to_symbol_kind(exp.symbol_class),
                    ..Default::default()
                });
            }
            PEF_EXPORT_REEXPORT => {
                // Re-export of an imported symbol.  Skip for now; these are
                // rare and don't contribute address-carrying symbols.
                log::debug!("Skipping re-exported symbol '{}'", exp.name);
            }
            si if si >= 0 => {
                let pef_idx = si as usize;
                let Some(obj_idx) = pef_to_obj.get(pef_idx).copied().flatten() else {
                    log::warn!(
                        "Export '{}' references non-instantiated section {pef_idx}",
                        exp.name
                    );
                    continue;
                };
                let section = &sections[obj_idx as usize];
                let addr = section.address + exp.value as u64;
                symbols.push(ObjSymbol {
                    name: exp.name.clone(),
                    demangled_name: demangle(&exp.name, &Default::default()),
                    address: addr,
                    section: Some(obj_idx),
                    size: 0,
                    size_known: false,
                    flags: ObjSymbolFlagSet(ObjSymbolFlags::Global | ObjSymbolFlags::Exported),
                    kind: pef_class_to_symbol_kind(exp.symbol_class),
                    ..Default::default()
                });
            }
            other => {
                log::warn!("Export '{}' has invalid section index {other}", exp.name);
            }
        }
    }

    // Entry points: main / init / term.  Each is (section_index, offset) where
    // section_index == -1 means "no entry point".
    let mut entry: Option<u64> = None;
    let entry_triples = [
        ("_pef_main", info.main_section, info.main_offset),
        ("_pef_init", info.init_section, info.init_offset),
        ("_pef_term", info.term_section, info.term_offset),
    ];
    for (tag, sec, off) in entry_triples {
        if sec < 0 {
            continue;
        }
        let pef_idx = sec as usize;
        let Some(obj_idx) = pef_to_obj.get(pef_idx).copied().flatten() else {
            log::warn!("Entry point {tag} references non-instantiated section {pef_idx}");
            continue;
        };
        let section = &sections[obj_idx as usize];
        // PEF mainSection / mainOffset for a TVector points at a 2-word
        // (code_ptr, toc_ptr) descriptor in a data section.  We can't cheaply
        // dereference it here, so record the TVector itself; the P3 reloc
        // pass will resolve the real code entry via its relocations.
        let addr = section.address + off as u64;
        if tag == "_pef_main" {
            entry = Some(addr);
        }
        symbols.push(ObjSymbol {
            name: tag.to_string(),
            demangled_name: None,
            address: addr,
            section: Some(obj_idx),
            size: 0,
            size_known: false,
            flags: ObjSymbolFlagSet(ObjSymbolFlags::Global | ObjSymbolFlags::Exported),
            kind: if section.kind == ObjSectionKind::Code {
                ObjSymbolKind::Function
            } else {
                ObjSymbolKind::Object
            },
            ..Default::default()
        });
    }

    let mut obj = ObjInfo::new(
        ObjKind::Executable,
        ObjArchitecture::PowerPc,
        name.to_string(),
        symbols,
        sections,
    );
    obj.entry = entry;
    // PEF has no single ImageBase; each section carries its own default_address.
    Ok((obj, None))
}

fn read_container(data: &[u8], sh: &PefSectionHeader) -> Result<Vec<u8>> {
    let end = (sh.container_offset as usize)
        .checked_add(sh.container_size as usize)
        .context("Container offset + size overflow")?;
    if end > data.len() {
        bail!("Section container extends past EOF");
    }
    Ok(data[sh.container_offset as usize..end].to_vec())
}

/// Serialize an `ObjInfo` back into a PEF container.
///
/// Not yet implemented — emitting PEF requires rebuilding the Loader section
/// (import table, export hash table, relocation opcode stream).  Tracked in
/// TODO.md.
pub fn write_pef(_obj: &ObjInfo) -> Result<Vec<u8>> {
    bail!("PEF writer not yet implemented")
}

/// Reconstruct absolute + relative relocations from the Loader section's
/// relocation opcode stream.  Mirrors `apply_base_relocations` for PE.
/// Not yet implemented (P3).
pub fn apply_pef_relocations(_obj: &mut ObjInfo) -> Result<()> { Ok(()) }
