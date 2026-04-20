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
//!   - Relocation opcode VM → `ObjReloc`s (section-targeted + import-targeted)
//!
//! Not yet implemented (tracked in TODO.md):
//!   - CodeWarrior traceback table scan for in-code function names / sizes
//!   - PatternInitData decompression
//!   - PEF writer (`write_pef`) for relink step

use anyhow::{Context, Result, bail};
use cwdemangle::demangle;

use crate::{
    analysis::cfa::SectionAddress,
    array_ref,
    obj::{
        ObjArchitecture, ObjInfo, ObjKind, ObjReloc, ObjRelocKind, ObjSection, ObjSectionKind,
        ObjSymbol, ObjSymbolFlagSet, ObjSymbolFlags, ObjSymbolKind,
        SectionIndex as ObjSectionIndex, SymbolIndex,
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
pub const PEF_LOADER_RELOC_HEADER_SIZE: usize = 12;

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

/// PEF Loader Relocation Header (12 bytes).  One entry per relocated section.
#[derive(Debug, Clone, Copy)]
pub struct PefLoaderRelocationHeader {
    /// PEF section index of the target section being fixed up.
    pub section_index: u16,
    pub reserved_a: u16,
    /// Number of 16-bit relocation chunks (NOT individual instructions — some
    /// instructions span two chunks).
    pub reloc_count: u32,
    /// Byte offset of the first relocation chunk, relative to
    /// `reloc_instr_offset` in the loader info header.
    pub first_reloc_offset: u32,
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
/// PatternInitData) into `ObjSection`s, parses the Loader section to populate
/// external and exported `ObjSymbols`, then walks the relocation opcode
/// stream to emit `ObjReloc`s and materialize fully-resolved VAs in section
/// data.
pub fn process_pef(data: &[u8], name: &str) -> Result<(ObjInfo, Option<u32>)> {
    let container = PefContainer::parse(data)?;

    // Compute a non-overlapping synthetic VA layout for the instantiated
    // sections.  PEF files typically have every `default_address` set to 0
    // (CFM assigns runtime bases), which would give every ObjSection the same
    // base and break every VA→section lookup downstream.  We preserve any
    // non-zero `default_address`es the PEF explicitly requests, then place
    // remaining sections contiguously above 0x0100_0000 with per-section
    // alignment honoured.
    let section_bases = compute_pef_section_bases(&container.sections);

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
                let compressed = read_container(data, sh)
                    .context("Reading pidata container")?;
                let mut buf = decompress_pidata(&compressed, sh.unpacked_size as usize)
                    .with_context(|| format!("Decompressing PEF pidata section {pef_idx}"))?;
                // total_size > unpacked_size tail is zero-initialised BSS.
                if sh.total_size as usize > buf.len() {
                    buf.resize(sh.total_size as usize, 0);
                }
                (ObjSectionKind::Data, buf)
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
            address: section_bases[pef_idx] as u64,
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
    // Track the obj symbol index assigned to each imported symbol.  The
    // relocation VM references imports by pef import index, so we need to
    // translate back to ObjSymbol indices when emitting ObjRelocs.
    let mut import_sym_indices: Vec<SymbolIndex> =
        Vec::with_capacity(imported_symbols.len());

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
        let idx = symbols.len() as SymbolIndex;
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
        import_sym_indices.push(idx);
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

    // Scan every Code section for CodeWarrior AIX-style traceback tables.
    // These provide in-binary function names for stripped PEFs and must be
    // added before relocation resolution so `for_relocation` can match
    // Va-targeted fixups against function-entry symbols.
    let code_section_indices: Vec<(ObjSectionIndex, u32)> = obj
        .sections
        .iter()
        .filter(|(_, s)| s.kind == ObjSectionKind::Code)
        .map(|(idx, s)| (idx, s.address as u32))
        .collect();
    let mut tb_total = 0u32;
    let mut tb_skipped_dup = 0u32;
    for (sec_idx, sec_addr) in code_section_indices {
        let tb_entries = {
            let section = &obj.sections[sec_idx];
            scan_traceback_tables(&section.data)
        };
        for entry in tb_entries {
            let va = sec_addr.wrapping_add(entry.func_offset);
            let demangled = demangle(&entry.name, &Default::default());
            let res = obj.symbols.add_direct(ObjSymbol {
                name: entry.name.clone(),
                demangled_name: demangled,
                address: va as u64,
                section: Some(sec_idx),
                size: entry.func_size as u64,
                size_known: entry.func_size > 0,
                flags: ObjSymbolFlagSet(ObjSymbolFlags::Local.into()),
                kind: ObjSymbolKind::Function,
                ..Default::default()
            });
            match res {
                Ok(_) => tb_total += 1,
                Err(_) => tb_skipped_dup += 1,
            }
        }
    }
    log::info!(
        "PEF {}: {} traceback-table symbols added ({} duplicates skipped)",
        name, tb_total, tb_skipped_dup
    );

    // Reloc VM must see the same synthetic bases we assigned to ObjSections
    // so that emitted fixups reference consistent VAs.
    let pef_section_default_addr: Vec<u32> = section_bases.clone();
    // Pick default sectionC / sectionD: first Code section index for C,
    // first UnpackedData section for D.  PEFBinaryFormat.h states the VM
    // defaults are sections 0 and 1, which matches this convention for
    // normal CodeWarrior PEF layouts.
    let default_section_c = container
        .sections
        .iter()
        .position(|sh| matches!(sh.kind(), Some(PefSectionKind::Code)))
        .unwrap_or(0);
    let default_section_d = container
        .sections
        .iter()
        .position(|sh| matches!(sh.kind(), Some(PefSectionKind::UnpackedData)))
        .unwrap_or(1);

    let reloc_count = apply_pef_relocations(
        &mut obj,
        loader,
        &info,
        libraries.len(),
        &pef_to_obj,
        &pef_section_default_addr,
        &import_sym_indices,
        default_section_c,
        default_section_d,
    )
    .context("Applying PEF relocations")?;
    log::info!(
        "PEF {}: {} relocations applied across {} target sections",
        name,
        reloc_count,
        info.reloc_section_count
    );

    // Resolve TVector entry points to real code addresses.  A PEF TVector is
    // two 32-bit words: (code_ptr, toc_ptr).  After relocations are applied,
    // the section data at (mainSection, mainOffset) holds the resolved VAs.
    // Emit `_start`/`_init_fn`/`_term_fn` function symbols at the code VAs and
    // point `obj.entry` at the real start address.
    let entry_triples = [
        ("_start", info.main_section, info.main_offset),
        ("_init_fn", info.init_section, info.init_offset),
        ("_term_fn", info.term_section, info.term_offset),
    ];
    for (tag, sec, off) in entry_triples {
        if sec < 0 {
            continue;
        }
        let pef_idx = sec as usize;
        let Some(tvec_obj_idx) = pef_to_obj.get(pef_idx).copied().flatten() else {
            continue;
        };
        let code_va = {
            let section = &obj.sections[tvec_obj_idx];
            let off = off as usize;
            if off + 4 > section.data.len() {
                log::warn!("TVector {tag} offset {off:#X} past section end");
                continue;
            }
            u32::from_be_bytes(*array_ref!(section.data, off, 4))
        };
        if code_va == 0 {
            continue;
        }
        let Some((code_sec_idx, code_sec)) = obj
            .sections
            .iter()
            .find(|(_, s)| {
                s.kind == ObjSectionKind::Code
                    && code_va as u64 >= s.address
                    && (code_va as u64) < s.address + s.size
            })
        else {
            log::warn!("TVector {tag} target {code_va:#X} not in any code section");
            continue;
        };
        if tag == "_start" {
            obj.entry = Some(code_va as u64);
        }
        log::info!(
            "PEF {}: TVector {} → {:#010X} (section {})",
            name, tag, code_va, code_sec.name
        );
        let _ = obj.symbols.add_direct(ObjSymbol {
            name: tag.to_string(),
            demangled_name: None,
            address: code_va as u64,
            section: Some(code_sec_idx),
            size: 0,
            size_known: false,
            flags: ObjSymbolFlagSet(ObjSymbolFlags::Global | ObjSymbolFlags::Exported),
            kind: ObjSymbolKind::Function,
            ..Default::default()
        });
    }

    // PEF has no single ImageBase; each section carries its own default_address.
    Ok((obj, None))
}

/// Compute synthetic, non-overlapping VA bases for each PEF section.
///
/// If the PEF specifies non-zero `default_address`es that do not overlap, they
/// are preserved verbatim.  Otherwise the instantiated, code/data-kind sections
/// are laid out contiguously starting at `SYNTHETIC_BASE`, honouring each
/// section's alignment and leaving a small gap between them.  Loader / Debug /
/// Exception / Traceback sections and unknown-kind sections receive a base of
/// 0 (they are skipped when building ObjSections and never participate in the
/// synthetic layout).
fn compute_pef_section_bases(sections: &[PefSectionHeader]) -> Vec<u32> {
    const SYNTHETIC_BASE: u32 = 0x0100_0000;
    const INTER_GAP: u32 = 0x0000_1000;

    fn is_loadable(kind: Option<PefSectionKind>) -> bool {
        matches!(
            kind,
            Some(PefSectionKind::Code)
                | Some(PefSectionKind::UnpackedData)
                | Some(PefSectionKind::PatternInitData)
                | Some(PefSectionKind::ConstantData)
                | Some(PefSectionKind::ExecutableData)
        )
    }

    let mut bases: Vec<u32> = sections.iter().map(|sh| sh.default_address).collect();

    // Detect overlap between loadable sections' explicit default_addresses.
    let mut ranges: Vec<(u32, u32)> = Vec::new();
    let mut any_zero = false;
    let mut overlap = false;
    for sh in sections.iter().filter(|sh| is_loadable(sh.kind())) {
        if sh.default_address == 0 {
            any_zero = true;
        }
        let end = sh.default_address.saturating_add(sh.total_size);
        for &(rs, re) in &ranges {
            if sh.default_address < re && end > rs {
                overlap = true;
                break;
            }
        }
        ranges.push((sh.default_address, end));
    }

    if !overlap && !any_zero {
        return bases;
    }

    let mut cur = SYNTHETIC_BASE;
    for (idx, sh) in sections.iter().enumerate() {
        if !is_loadable(sh.kind()) {
            bases[idx] = 0;
            continue;
        }
        let raw_align = if sh.alignment == 0 { 1u32 } else { 1u32 << sh.alignment };
        // Enforce at least 16-byte alignment to keep addresses human-readable.
        let align = raw_align.max(16);
        cur = (cur + align - 1) & !(align - 1);
        bases[idx] = cur;
        cur = cur.saturating_add(sh.total_size).saturating_add(INTER_GAP);
    }
    bases
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

// -------------------- PatternInitData decompression --------------------
//
// A PatternInitData section's container is a stream of opcodes that expand to
// `unpacked_size` bytes.  Each opcode byte encodes:
//   bits 7..5: 3-bit opcode
//   bits 4..0: 5-bit immediate count ("N").
// If the 5-bit count is zero, the real count follows as a variable-length
// unsigned integer (high bit = continuation, 7 bits per byte, big-endian).
// Additional varints (customSize, repeatCount) follow for opcodes 3 and 4.
//
// Opcode semantics (see Apple PEFBinaryFormat.h, Ghidra SectionHeader.java):
//   0 Zero:        emit N zero bytes
//   1 BlockCopy:   copy N bytes from the stream
//   2 RepeatedBlock:
//        blockSize = N; repeat = varint + 1
//        read blockSize bytes, emit them `repeat` times
//   3 InterleaveRepeatBlockWithBlockCopy:
//        commonSize = N; customSize = varint; repeat = varint
//        read commonSize bytes (common), emit common,
//        then `repeat` times: read customSize bytes, emit them, emit common
//   4 InterleaveRepeatBlockWithZero:
//        commonSize = N; customSize = varint; repeat = varint
//        emit commonSize zeros,
//        then `repeat` times: read customSize bytes, emit them, emit zeros
/// Read one variable-length count from the pidata stream.  Advances `input`.
fn unpack_next_value(input: &mut &[u8]) -> Result<u32> {
    let mut result: u32 = 0;
    loop {
        let (&byte, rest) =
            input.split_first().context("pidata stream truncated reading varint")?;
        *input = rest;
        result = result
            .checked_shl(7)
            .context("pidata varint overflow")?
            | u32::from(byte & 0x7F);
        if byte & 0x80 == 0 {
            return Ok(result);
        }
    }
}

/// Expand a PEF PatternInitData container into its unpacked representation.
pub fn decompress_pidata(compressed: &[u8], unpacked_size: usize) -> Result<Vec<u8>> {
    let mut out: Vec<u8> = Vec::with_capacity(unpacked_size);
    let mut input: &[u8] = compressed;
    while let Some((&first, rest)) = input.split_first() {
        input = rest;
        let opcode = (first >> 5) & 0x07;
        let mut count = u32::from(first & 0x1F);
        if count == 0 {
            count = unpack_next_value(&mut input)?;
        }
        match opcode {
            0 => {
                // Zero
                out.resize(out.len() + count as usize, 0);
            }
            1 => {
                // BlockCopy
                let size = count as usize;
                let (block, rest) = input
                    .split_at_checked(size)
                    .context("pidata BlockCopy past end of stream")?;
                out.extend_from_slice(block);
                input = rest;
            }
            2 => {
                // RepeatedBlock: emit block (repeat+1) times
                let block_size = count as usize;
                let repeat = unpack_next_value(&mut input)?
                    .checked_add(1)
                    .context("pidata RepeatedBlock count overflow")?;
                let (block, rest) = input
                    .split_at_checked(block_size)
                    .context("pidata RepeatedBlock past end of stream")?;
                for _ in 0..repeat {
                    out.extend_from_slice(block);
                }
                input = rest;
            }
            3 => {
                // InterleaveRepeatBlockWithBlockCopy
                let common_size = count as usize;
                let custom_size = unpack_next_value(&mut input)? as usize;
                let repeat = unpack_next_value(&mut input)? as usize;
                let (common, mut rest) = input
                    .split_at_checked(common_size)
                    .context("pidata IRB/Copy common past end of stream")?;
                out.extend_from_slice(common);
                for _ in 0..repeat {
                    let (custom, next) = rest
                        .split_at_checked(custom_size)
                        .context("pidata IRB/Copy custom past end of stream")?;
                    out.extend_from_slice(custom);
                    out.extend_from_slice(common);
                    rest = next;
                }
                input = rest;
            }
            4 => {
                // InterleaveRepeatBlockWithZero
                let common_size = count as usize;
                let custom_size = unpack_next_value(&mut input)? as usize;
                let repeat = unpack_next_value(&mut input)? as usize;
                out.resize(out.len() + common_size, 0);
                for _ in 0..repeat {
                    let (custom, next) = input
                        .split_at_checked(custom_size)
                        .context("pidata IRB/Zero custom past end of stream")?;
                    out.extend_from_slice(custom);
                    out.resize(out.len() + common_size, 0);
                    input = next;
                }
            }
            _ => bail!("Unknown PEF pidata opcode {opcode}"),
        }
    }
    if out.len() != unpacked_size {
        bail!(
            "PEF pidata decompression size mismatch: got {}, expected {}",
            out.len(),
            unpacked_size
        );
    }
    Ok(out)
}

/// Serialize an `ObjInfo` back into a PEF container.
///
/// Not yet implemented — emitting PEF requires rebuilding the Loader section
/// (import table, export hash table, relocation opcode stream).  Tracked in
/// TODO.md.
pub fn write_pef(_obj: &ObjInfo) -> Result<Vec<u8>> {
    bail!("PEF writer not yet implemented")
}

/// Parse the PEF loader relocation header table.  The table lives immediately
/// after the imported symbol table inside the loader section.
pub fn parse_reloc_headers(
    loader: &[u8],
    info: &PefLoaderInfoHeader,
    library_count: usize,
) -> Result<Vec<PefLoaderRelocationHeader>> {
    let base = PEF_LOADER_INFO_HEADER_SIZE
        + library_count * PEF_IMPORTED_LIBRARY_SIZE
        + info.total_imported_symbol_count as usize * 4;
    let count = info.reloc_section_count as usize;
    let end = base + count * PEF_LOADER_RELOC_HEADER_SIZE;
    if end > loader.len() {
        bail!("Reloc header table extends past loader section end");
    }
    let mut out = Vec::with_capacity(count);
    for i in 0..count {
        let off = base + i * PEF_LOADER_RELOC_HEADER_SIZE;
        let entry = &loader[off..off + PEF_LOADER_RELOC_HEADER_SIZE];
        out.push(PefLoaderRelocationHeader {
            section_index: u16::from_be_bytes(*array_ref!(entry, 0, 2)),
            reserved_a: u16::from_be_bytes(*array_ref!(entry, 2, 2)),
            reloc_count: u32::from_be_bytes(*array_ref!(entry, 4, 4)),
            first_reloc_offset: u32::from_be_bytes(*array_ref!(entry, 8, 4)),
        });
    }
    Ok(out)
}

// -------------------- Relocation opcode constants --------------------
//
// Opcode groups identified by the top 7 bits of the 16-bit chunk.  See
// Apple's PEFBinaryFormat.h / Mac OS Runtime Architectures ch. 11.

// "DSKP": top 2 bits == 00.  0x00..=0x1F occupy the full 5-bit subrange
// because only the top 2 bits (of the top 7) are significant.
const OP7_DSKP_MIN: u16 = 0x00;
const OP7_DSKP_MAX: u16 = 0x1F;
// Run group: 010_0xxx
const OP7_BY_SECT_C: u16 = 0x20;
const OP7_BY_SECT_D: u16 = 0x21;
const OP7_TVECTOR12: u16 = 0x22;
const OP7_TVECTOR8: u16 = 0x23;
const OP7_VTABLE8: u16 = 0x24;
const OP7_IMPORT_RUN: u16 = 0x25;
// SmIndex group: 011_00xx
const OP7_SM_BY_IMPORT: u16 = 0x30;
const OP7_SM_SET_SECT_C: u16 = 0x31;
const OP7_SM_SET_SECT_D: u16 = 0x32;
const OP7_SM_BY_SECTION: u16 = 0x33;
// IncrPosition: 100_0xxx (0x40..=0x47)
const OP7_INCR_POS_MIN: u16 = 0x40;
const OP7_INCR_POS_MAX: u16 = 0x47;
// SmRepeat: 100_1xxx (0x48..=0x4F)
const OP7_SM_REPEAT_MIN: u16 = 0x48;
const OP7_SM_REPEAT_MAX: u16 = 0x4F;
// SetPosition: 101_000x (0x50..=0x51) — 2-chunk
const OP7_SET_POS_MIN: u16 = 0x50;
const OP7_SET_POS_MAX: u16 = 0x51;
// LgByImport: 101_001x (0x52..=0x53) — 2-chunk
const OP7_LG_BY_IMPORT_MIN: u16 = 0x52;
const OP7_LG_BY_IMPORT_MAX: u16 = 0x53;
// LgRepeat: 101_100x (0x58..=0x59) — 2-chunk
const OP7_LG_REPEAT_MIN: u16 = 0x58;
const OP7_LG_REPEAT_MAX: u16 = 0x59;
// LgSetOrBySection: 101_101x (0x5A..=0x5B) — 2-chunk
const OP7_LG_SET_OR_SECTION_MIN: u16 = 0x5A;
const OP7_LG_SET_OR_SECTION_MAX: u16 = 0x5B;

// LgSetOrBySection 4-bit subopcodes (bits [9:6] of the first chunk).
const LG_SUBOP_BY_SECTION: u32 = 0x0;
const LG_SUBOP_SET_SECT_C: u32 = 0x1;
const LG_SUBOP_SET_SECT_D: u32 = 0x2;

// Extract an `(offset, length)` bit-field from a 16-bit chunk, following the
// PEFRelocField macro convention from PEFBinaryFormat.h.
#[inline]
fn rfield(chunk: u16, offset: u16, length: u16) -> u32 {
    let shift = 16 - (offset + length);
    ((chunk as u32) >> shift) & ((1u32 << length) - 1)
}

/// Pending fixup produced by the relocation VM, awaiting symbol resolution.
#[derive(Debug, Clone, Copy)]
enum PendingRelocTarget {
    /// Target is an absolute VA in the PEF's default-address space.
    Va(u32),
    /// Target is an imported symbol with the given obj symbol index.
    Import(SymbolIndex),
}

#[derive(Debug, Clone, Copy)]
struct PendingFixup {
    /// Byte offset into the target section where the 32-bit slot lives.
    offset: u32,
    target: PendingRelocTarget,
    /// Value originally stored at the slot, pre-add.  For import fixups this
    /// becomes the ObjReloc addend directly.
    original_word: u32,
}

/// Apply all relocations described by a single loader-relocation header.
///
/// The VM maintains four pieces of state per section:
///   * `reloc_addr` — current byte offset within the target section
///   * `section_c` / `section_d` — default_address of the currently-selected
///     code/data anchor section (changed by SetSectC / SetSectD)
///   * `import_index` — next imported symbol to resolve
///
/// Each fixup reads the existing 32-bit word, computes the target (either an
/// absolute VA = `stored + section_base` or an imported symbol with the
/// stored word as addend), writes the resolved absolute VA back into the
/// section (for VA targets) or leaves the stored word alone (for imports),
/// and records a `PendingFixup` for later conversion to `ObjReloc`.
fn execute_reloc_vm(
    instr_stream: &[u8],
    header: &PefLoaderRelocationHeader,
    target_section: &mut [u8],
    pef_section_default_addr: &[u32],
    import_sym_indices: &[SymbolIndex],
    default_section_c: usize,
    default_section_d: usize,
    pending: &mut Vec<PendingFixup>,
) -> Result<()> {
    let start = header.first_reloc_offset as usize;
    let total_chunks = header.reloc_count as usize;
    let total_bytes = total_chunks * 2;
    if start + total_bytes > instr_stream.len() {
        bail!(
            "Reloc header for PEF section {} extends past instruction stream ({}+{} > {})",
            header.section_index,
            start,
            total_bytes,
            instr_stream.len()
        );
    }
    let instrs = &instr_stream[start..start + total_bytes];

    let initial_c = pef_section_default_addr.get(default_section_c).copied().unwrap_or(0);
    let initial_d = pef_section_default_addr.get(default_section_d).copied().unwrap_or(0);
    let mut reloc_addr: u32 = 0;
    let mut section_c: u32 = initial_c;
    let mut section_d: u32 = initial_d;
    let mut import_index: u32 = 0;

    // Inline helpers capturing the section buffer.  These mutate the
    // in-memory section data to contain fully-resolved VAs and enqueue a
    // pending ObjReloc.
    macro_rules! read_word {
        ($off:expr) => {{
            let o = $off as usize;
            if o + 4 > target_section.len() {
                bail!(
                    "Reloc at offset {:#x} past section end ({} bytes)",
                    $off,
                    target_section.len()
                );
            }
            u32::from_be_bytes(*array_ref!(target_section, o, 4))
        }};
    }
    macro_rules! write_word {
        ($off:expr, $val:expr) => {{
            let o = $off as usize;
            target_section[o..o + 4].copy_from_slice(&($val as u32).to_be_bytes());
        }};
    }
    macro_rules! fixup_va {
        ($off:expr, $base:expr) => {{
            let orig = read_word!($off);
            let va = orig.wrapping_add($base);
            write_word!($off, va);
            pending.push(PendingFixup {
                offset: $off,
                target: PendingRelocTarget::Va(va),
                original_word: orig,
            });
        }};
    }
    macro_rules! fixup_import {
        ($off:expr, $idx:expr) => {{
            let orig = read_word!($off);
            let Some(&sym_idx) = import_sym_indices.get($idx as usize) else {
                bail!(
                    "Reloc references out-of-range import index {} (have {} imports)",
                    $idx,
                    import_sym_indices.len()
                );
            };
            pending.push(PendingFixup {
                offset: $off,
                target: PendingRelocTarget::Import(sym_idx),
                original_word: orig,
            });
        }};
    }

    // Cap total VM chunk executions to guard against pathological repeat
    // loops in malformed input.  Legit PEFs run at most reloc_count chunks
    // linearly — repeats multiply that, so use a generous 16x budget.
    let budget = total_chunks.saturating_mul(16).max(1024);
    let mut executed: usize = 0;

    let mut ip: usize = 0;
    while ip < total_chunks {
        executed += 1;
        if executed > budget {
            bail!("PEF reloc VM exceeded execution budget ({} chunks)", budget);
        }
        let chunk = u16::from_be_bytes([instrs[ip * 2], instrs[ip * 2 + 1]]);
        let op7 = chunk >> 9;

        match op7 {
            // RelocBySectDWithSkip(skip, count)
            OP7_DSKP_MIN..=OP7_DSKP_MAX => {
                let skip_count = rfield(chunk, 2, 8);
                let reloc_count = rfield(chunk, 10, 6);
                reloc_addr = reloc_addr.wrapping_add(skip_count.wrapping_mul(4));
                for _ in 0..reloc_count {
                    fixup_va!(reloc_addr, section_d);
                    reloc_addr = reloc_addr.wrapping_add(4);
                }
                ip += 1;
            }
            // Run group: run-length encoded fixups.  Length field is
            // stored-minus-1 so value N means N+1 iterations.
            OP7_BY_SECT_C => {
                let run = rfield(chunk, 7, 9) + 1;
                for _ in 0..run {
                    fixup_va!(reloc_addr, section_c);
                    reloc_addr = reloc_addr.wrapping_add(4);
                }
                ip += 1;
            }
            OP7_BY_SECT_D => {
                let run = rfield(chunk, 7, 9) + 1;
                for _ in 0..run {
                    fixup_va!(reloc_addr, section_d);
                    reloc_addr = reloc_addr.wrapping_add(4);
                }
                ip += 1;
            }
            OP7_TVECTOR12 => {
                let run = rfield(chunk, 7, 9) + 1;
                for _ in 0..run {
                    fixup_va!(reloc_addr, section_c);
                    fixup_va!(reloc_addr.wrapping_add(4), section_d);
                    reloc_addr = reloc_addr.wrapping_add(12);
                }
                ip += 1;
            }
            OP7_TVECTOR8 => {
                let run = rfield(chunk, 7, 9) + 1;
                for _ in 0..run {
                    fixup_va!(reloc_addr, section_c);
                    fixup_va!(reloc_addr.wrapping_add(4), section_d);
                    reloc_addr = reloc_addr.wrapping_add(8);
                }
                ip += 1;
            }
            OP7_VTABLE8 => {
                let run = rfield(chunk, 7, 9) + 1;
                for _ in 0..run {
                    fixup_va!(reloc_addr, section_d);
                    reloc_addr = reloc_addr.wrapping_add(8);
                }
                ip += 1;
            }
            OP7_IMPORT_RUN => {
                let run = rfield(chunk, 7, 9) + 1;
                for _ in 0..run {
                    fixup_import!(reloc_addr, import_index);
                    import_index = import_index.wrapping_add(1);
                    reloc_addr = reloc_addr.wrapping_add(4);
                }
                ip += 1;
            }
            // SmIndex group
            OP7_SM_BY_IMPORT => {
                let index = rfield(chunk, 7, 9);
                fixup_import!(reloc_addr, index);
                import_index = index.wrapping_add(1);
                reloc_addr = reloc_addr.wrapping_add(4);
                ip += 1;
            }
            OP7_SM_SET_SECT_C => {
                let index = rfield(chunk, 7, 9) as usize;
                section_c = *pef_section_default_addr
                    .get(index)
                    .with_context(|| format!("SmSetSectC index {} out of range", index))?;
                ip += 1;
            }
            OP7_SM_SET_SECT_D => {
                let index = rfield(chunk, 7, 9) as usize;
                section_d = *pef_section_default_addr
                    .get(index)
                    .with_context(|| format!("SmSetSectD index {} out of range", index))?;
                ip += 1;
            }
            OP7_SM_BY_SECTION => {
                let index = rfield(chunk, 7, 9) as usize;
                let base = *pef_section_default_addr
                    .get(index)
                    .with_context(|| format!("SmBySection index {} out of range", index))?;
                fixup_va!(reloc_addr, base);
                reloc_addr = reloc_addr.wrapping_add(4);
                ip += 1;
            }
            // IncrPosition: offset field is stored-minus-1.
            OP7_INCR_POS_MIN..=OP7_INCR_POS_MAX => {
                let off = rfield(chunk, 4, 12) + 1;
                reloc_addr = reloc_addr.wrapping_add(off);
                ip += 1;
            }
            // SmRepeat(chunkCount-1, repeatCount-1): re-execute the
            // `chunkCount` chunks preceding this instruction `repeatCount`
            // additional times.
            OP7_SM_REPEAT_MIN..=OP7_SM_REPEAT_MAX => {
                let chunk_count = rfield(chunk, 4, 4) + 1;
                let repeat_count = rfield(chunk, 8, 8) + 1;
                if chunk_count as usize > ip {
                    bail!(
                        "SmRepeat at chunk {} wants {} preceding chunks but only {} exist",
                        ip,
                        chunk_count,
                        ip
                    );
                }
                let back_ip = ip - chunk_count as usize;
                // Execute the block repeat_count additional times.  Use a
                // local budget to avoid a runaway nested-repeat situation;
                // the outer `executed` counter also catches this.
                for _ in 0..repeat_count {
                    let mut sub_ip = back_ip;
                    while sub_ip < ip {
                        executed += 1;
                        if executed > budget {
                            bail!("PEF reloc VM exceeded execution budget during repeat");
                        }
                        let c =
                            u16::from_be_bytes([instrs[sub_ip * 2], instrs[sub_ip * 2 + 1]]);
                        // Re-dispatch a subset of opcodes (the ones that
                        // commonly appear inside a repeat block).  Nested
                        // repeats aren't used by real toolchains.
                        let sub_op7 = c >> 9;
                        match sub_op7 {
                            OP7_DSKP_MIN..=OP7_DSKP_MAX => {
                                let skip_count = rfield(c, 2, 8);
                                let reloc_count = rfield(c, 10, 6);
                                reloc_addr = reloc_addr.wrapping_add(skip_count.wrapping_mul(4));
                                for _ in 0..reloc_count {
                                    fixup_va!(reloc_addr, section_d);
                                    reloc_addr = reloc_addr.wrapping_add(4);
                                }
                                sub_ip += 1;
                            }
                            OP7_BY_SECT_C => {
                                let run = rfield(c, 7, 9) + 1;
                                for _ in 0..run {
                                    fixup_va!(reloc_addr, section_c);
                                    reloc_addr = reloc_addr.wrapping_add(4);
                                }
                                sub_ip += 1;
                            }
                            OP7_BY_SECT_D => {
                                let run = rfield(c, 7, 9) + 1;
                                for _ in 0..run {
                                    fixup_va!(reloc_addr, section_d);
                                    reloc_addr = reloc_addr.wrapping_add(4);
                                }
                                sub_ip += 1;
                            }
                            OP7_TVECTOR12 => {
                                let run = rfield(c, 7, 9) + 1;
                                for _ in 0..run {
                                    fixup_va!(reloc_addr, section_c);
                                    fixup_va!(reloc_addr.wrapping_add(4), section_d);
                                    reloc_addr = reloc_addr.wrapping_add(12);
                                }
                                sub_ip += 1;
                            }
                            OP7_TVECTOR8 => {
                                let run = rfield(c, 7, 9) + 1;
                                for _ in 0..run {
                                    fixup_va!(reloc_addr, section_c);
                                    fixup_va!(reloc_addr.wrapping_add(4), section_d);
                                    reloc_addr = reloc_addr.wrapping_add(8);
                                }
                                sub_ip += 1;
                            }
                            OP7_VTABLE8 => {
                                let run = rfield(c, 7, 9) + 1;
                                for _ in 0..run {
                                    fixup_va!(reloc_addr, section_d);
                                    reloc_addr = reloc_addr.wrapping_add(8);
                                }
                                sub_ip += 1;
                            }
                            OP7_IMPORT_RUN => {
                                let run = rfield(c, 7, 9) + 1;
                                for _ in 0..run {
                                    fixup_import!(reloc_addr, import_index);
                                    import_index = import_index.wrapping_add(1);
                                    reloc_addr = reloc_addr.wrapping_add(4);
                                }
                                sub_ip += 1;
                            }
                            OP7_INCR_POS_MIN..=OP7_INCR_POS_MAX => {
                                let off = rfield(c, 4, 12) + 1;
                                reloc_addr = reloc_addr.wrapping_add(off);
                                sub_ip += 1;
                            }
                            other => bail!(
                                "Unsupported opcode {:#x} inside SmRepeat block",
                                other << 9
                            ),
                        }
                    }
                }
                ip += 1;
            }
            // Two-chunk opcodes: consume the next chunk for the low 16 bits.
            OP7_SET_POS_MIN..=OP7_SET_POS_MAX => {
                if ip + 1 >= total_chunks {
                    bail!("SetPosition truncated at end of stream");
                }
                let chunk2 =
                    u16::from_be_bytes([instrs[(ip + 1) * 2], instrs[(ip + 1) * 2 + 1]]);
                let full = (((chunk as u32) & 0x03FF) << 16) | (chunk2 as u32);
                reloc_addr = full;
                ip += 2;
            }
            OP7_LG_BY_IMPORT_MIN..=OP7_LG_BY_IMPORT_MAX => {
                if ip + 1 >= total_chunks {
                    bail!("LgByImport truncated at end of stream");
                }
                let chunk2 =
                    u16::from_be_bytes([instrs[(ip + 1) * 2], instrs[(ip + 1) * 2 + 1]]);
                let full = (((chunk as u32) & 0x03FF) << 16) | (chunk2 as u32);
                fixup_import!(reloc_addr, full);
                import_index = full.wrapping_add(1);
                reloc_addr = reloc_addr.wrapping_add(4);
                ip += 2;
            }
            OP7_LG_REPEAT_MIN..=OP7_LG_REPEAT_MAX => {
                if ip + 1 >= total_chunks {
                    bail!("LgRepeat truncated at end of stream");
                }
                let chunk2 =
                    u16::from_be_bytes([instrs[(ip + 1) * 2], instrs[(ip + 1) * 2 + 1]]);
                let chunk_count = rfield(chunk, 6, 4) + 1;
                let repeat_count =
                    (((chunk as u32) & 0x003F) << 16) | (chunk2 as u32);
                if chunk_count as usize > ip {
                    bail!(
                        "LgRepeat at chunk {} wants {} preceding chunks but only {} exist",
                        ip,
                        chunk_count,
                        ip
                    );
                }
                let back_ip = ip - chunk_count as usize;
                for _ in 0..repeat_count {
                    let mut sub_ip = back_ip;
                    while sub_ip < ip {
                        executed += 1;
                        if executed > budget {
                            bail!("PEF reloc VM exceeded execution budget during Lg repeat");
                        }
                        let c = u16::from_be_bytes([
                            instrs[sub_ip * 2],
                            instrs[sub_ip * 2 + 1],
                        ]);
                        let sub_op7 = c >> 9;
                        match sub_op7 {
                            OP7_DSKP_MIN..=OP7_DSKP_MAX => {
                                let skip_count = rfield(c, 2, 8);
                                let reloc_count = rfield(c, 10, 6);
                                reloc_addr =
                                    reloc_addr.wrapping_add(skip_count.wrapping_mul(4));
                                for _ in 0..reloc_count {
                                    fixup_va!(reloc_addr, section_d);
                                    reloc_addr = reloc_addr.wrapping_add(4);
                                }
                                sub_ip += 1;
                            }
                            OP7_BY_SECT_C => {
                                let run = rfield(c, 7, 9) + 1;
                                for _ in 0..run {
                                    fixup_va!(reloc_addr, section_c);
                                    reloc_addr = reloc_addr.wrapping_add(4);
                                }
                                sub_ip += 1;
                            }
                            OP7_BY_SECT_D => {
                                let run = rfield(c, 7, 9) + 1;
                                for _ in 0..run {
                                    fixup_va!(reloc_addr, section_d);
                                    reloc_addr = reloc_addr.wrapping_add(4);
                                }
                                sub_ip += 1;
                            }
                            OP7_TVECTOR12 => {
                                let run = rfield(c, 7, 9) + 1;
                                for _ in 0..run {
                                    fixup_va!(reloc_addr, section_c);
                                    fixup_va!(reloc_addr.wrapping_add(4), section_d);
                                    reloc_addr = reloc_addr.wrapping_add(12);
                                }
                                sub_ip += 1;
                            }
                            OP7_TVECTOR8 => {
                                let run = rfield(c, 7, 9) + 1;
                                for _ in 0..run {
                                    fixup_va!(reloc_addr, section_c);
                                    fixup_va!(reloc_addr.wrapping_add(4), section_d);
                                    reloc_addr = reloc_addr.wrapping_add(8);
                                }
                                sub_ip += 1;
                            }
                            OP7_VTABLE8 => {
                                let run = rfield(c, 7, 9) + 1;
                                for _ in 0..run {
                                    fixup_va!(reloc_addr, section_d);
                                    reloc_addr = reloc_addr.wrapping_add(8);
                                }
                                sub_ip += 1;
                            }
                            OP7_IMPORT_RUN => {
                                let run = rfield(c, 7, 9) + 1;
                                for _ in 0..run {
                                    fixup_import!(reloc_addr, import_index);
                                    import_index = import_index.wrapping_add(1);
                                    reloc_addr = reloc_addr.wrapping_add(4);
                                }
                                sub_ip += 1;
                            }
                            OP7_INCR_POS_MIN..=OP7_INCR_POS_MAX => {
                                let off = rfield(c, 4, 12) + 1;
                                reloc_addr = reloc_addr.wrapping_add(off);
                                sub_ip += 1;
                            }
                            other => bail!(
                                "Unsupported opcode {:#x} inside LgRepeat block",
                                other << 9
                            ),
                        }
                    }
                }
                ip += 2;
            }
            OP7_LG_SET_OR_SECTION_MIN..=OP7_LG_SET_OR_SECTION_MAX => {
                if ip + 1 >= total_chunks {
                    bail!("LgSetOrBySection truncated at end of stream");
                }
                let chunk2 =
                    u16::from_be_bytes([instrs[(ip + 1) * 2], instrs[(ip + 1) * 2 + 1]]);
                let subop = rfield(chunk, 6, 4);
                let index =
                    ((((chunk as u32) & 0x003F) << 16) | (chunk2 as u32)) as usize;
                let base = *pef_section_default_addr
                    .get(index)
                    .with_context(|| format!("LgSetOrBySection index {} out of range", index))?;
                match subop {
                    LG_SUBOP_BY_SECTION => {
                        fixup_va!(reloc_addr, base);
                        reloc_addr = reloc_addr.wrapping_add(4);
                    }
                    LG_SUBOP_SET_SECT_C => section_c = base,
                    LG_SUBOP_SET_SECT_D => section_d = base,
                    other => bail!("Unknown LgSetOrBySection subopcode {}", other),
                }
                ip += 2;
            }
            other => bail!("Unknown PEF reloc opcode {:#x}", other << 9),
        }
    }

    Ok(())
}

/// One parsed CodeWarrior / AIX-style PowerPC traceback table.
#[derive(Debug, Clone)]
pub struct PpcTracebackEntry {
    /// Section-local byte offset of the first instruction of the function.
    pub func_offset: u32,
    /// Byte size of the function body (excludes the trailing zero word
    /// and the traceback table itself).
    pub func_size: u32,
    /// Symbol name extracted from the traceback table's `name` field.
    pub name: String,
}

// AIX traceback table flag masks (bit positions MSB-first per AIX spec).
// Flags live in bytes 2..=5 of the first TB word.
const TB_F1_HAS_TBOFF: u8 = 0x20;
const TB_F1_HAS_CTL: u8 = 0x08;
const TB_F2_INT_HNDL: u8 = 0x80;
const TB_F2_NAME_PRESENT: u8 = 0x40;
const TB_F2_USES_ALLOCA: u8 = 0x20;
const TB_F4_HAS_VEC_INFO: u8 = 0x40;

/// Known AIX `lang` byte values.  CodeWarrior typically emits 0 (C) or 9 (C++).
const TB_MAX_LANG: u8 = 15;

/// Try to parse a traceback table starting at `tb_start` (byte offset of the
/// version byte).  Returns None if any validation check fails or optional
/// fields overrun the buffer.  Only signals "looks like a valid TB" — the
/// caller is responsible for deciding which entries to keep.
fn try_parse_traceback(
    section_data: &[u8],
    zero_word_off: usize,
) -> Option<PpcTracebackEntry> {
    let tb_start = zero_word_off + 4;
    if tb_start + 8 > section_data.len() {
        return None;
    }
    let version = section_data[tb_start];
    let lang = section_data[tb_start + 1];
    let flags1 = section_data[tb_start + 2];
    let flags2 = section_data[tb_start + 3];
    let _flags3 = section_data[tb_start + 4];
    let flags4 = section_data[tb_start + 5];
    let fixedparms = section_data[tb_start + 6];
    let floatparms_and_stk = section_data[tb_start + 7];
    let floatparms = floatparms_and_stk >> 1;

    if version != 0 {
        return None;
    }
    if lang > TB_MAX_LANG {
        return None;
    }
    // CodeWarrior PEF for classic Mac has no AltiVec.  If the vec-info bit is
    // set, we've almost certainly matched a non-TB byte pattern.
    if flags4 & TB_F4_HAS_VEC_INFO != 0 {
        return None;
    }

    let has_tboff = flags1 & TB_F1_HAS_TBOFF != 0;
    let has_ctl = flags1 & TB_F1_HAS_CTL != 0;
    let int_hndl = flags2 & TB_F2_INT_HNDL != 0;
    let name_present = flags2 & TB_F2_NAME_PRESENT != 0;
    let uses_alloca = flags2 & TB_F2_USES_ALLOCA != 0;

    // Both name and tb_offset are required to emit a useful symbol.  If
    // either is missing, this TB doesn't help us and we skip it.
    if !has_tboff || !name_present {
        return None;
    }

    let mut p = tb_start + 8;

    // parminfo: present if fixedparms > 0 OR floatparms > 0.
    if fixedparms > 0 || floatparms > 0 {
        if p + 4 > section_data.len() {
            return None;
        }
        p += 4;
    }

    // tb_offset: distance from func start to TB start.
    if p + 4 > section_data.len() {
        return None;
    }
    let tb_offset = u32::from_be_bytes(*array_ref!(section_data, p, 4));
    p += 4;

    // Sanity: tb_offset must land inside the current section, at or below
    // the TB.  We check against tb_start (the first byte of the TB).
    let tb_start_u32 = tb_start as u32;
    if tb_offset == 0 || tb_offset > tb_start_u32 {
        return None;
    }
    let func_start_off = tb_start_u32 - tb_offset;
    // The function body spans [func_start, zero_word_off).  Require
    // at least one instruction.
    if (func_start_off as usize) >= zero_word_off {
        return None;
    }

    if int_hndl {
        if p + 4 > section_data.len() {
            return None;
        }
        p += 4; // hand_mask
    }

    if has_ctl {
        if p + 4 > section_data.len() {
            return None;
        }
        let ctl_info = u32::from_be_bytes(*array_ref!(section_data, p, 4));
        p += 4;
        // Each ctl_info_disp is a 4-byte word; cap at a sane bound so a
        // corrupted byte pattern can't run us off the end.
        if ctl_info > 1024 {
            return None;
        }
        let ctl_bytes = (ctl_info as usize).checked_mul(4)?;
        if p + ctl_bytes > section_data.len() {
            return None;
        }
        p += ctl_bytes;
    }

    // name_len + name
    if p + 2 > section_data.len() {
        return None;
    }
    let name_len =
        u16::from_be_bytes(*array_ref!(section_data, p, 2)) as usize;
    p += 2;
    if name_len == 0 || name_len > 1024 {
        return None;
    }
    if p + name_len > section_data.len() {
        return None;
    }
    let name_bytes = &section_data[p..p + name_len];
    // Require printable ASCII (plus a few CW-allowed punctuation bytes).
    if !name_bytes
        .iter()
        .all(|&b| (0x20..=0x7E).contains(&b))
    {
        return None;
    }
    let name = std::str::from_utf8(name_bytes).ok()?.to_string();
    let _p_after_name = p + name_len;

    // alloca_reg not used — only parse it for structural validation.
    if uses_alloca {
        if _p_after_name >= section_data.len() {
            return None;
        }
    }

    let func_size = zero_word_off as u32 - func_start_off;
    Some(PpcTracebackEntry { func_offset: func_start_off, func_size, name })
}

/// Scan a PEF code section for CodeWarrior / AIX-style PowerPC traceback
/// tables.  CodeWarrior embeds these after the `blr` of each function: a
/// 4-byte zero word serves as a marker, then the traceback table contains
/// the function name and a `tb_offset` pointing back to the function start.
///
/// This is the main source of function names in a stripped PEF — exports
/// only cover symbols that other fragments link against.
pub fn scan_traceback_tables(section_data: &[u8]) -> Vec<PpcTracebackEntry> {
    let mut out = Vec::new();
    let mut off: usize = 0;
    while off + 12 <= section_data.len() {
        // Only check 4-byte aligned offsets; CW aligns TBs to a word.
        let word = u32::from_be_bytes(*array_ref!(section_data, off, 4));
        if word != 0 {
            off += 4;
            continue;
        }
        match try_parse_traceback(section_data, off) {
            Some(entry) => {
                // Skip over the TB we just consumed to avoid accidentally
                // re-matching its own trailing zero padding.
                let skip_to = (entry.func_offset + entry.func_size) as usize + 4;
                out.push(entry);
                off = skip_to.max(off + 4);
            }
            None => {
                off += 4;
            }
        }
    }
    out
}

/// Reconstruct absolute relocations from the Loader section's relocation
/// opcode stream.  Walks the reloc header table, runs the VM once per
/// target section, then converts pending VA/Import fixups into `ObjReloc`s
/// resolved against the current symbol table.
fn apply_pef_relocations(
    obj: &mut ObjInfo,
    loader: &[u8],
    info: &PefLoaderInfoHeader,
    library_count: usize,
    pef_to_obj: &[Option<ObjSectionIndex>],
    pef_section_default_addr: &[u32],
    import_sym_indices: &[SymbolIndex],
    default_section_c: usize,
    default_section_d: usize,
) -> Result<u32> {
    let headers = parse_reloc_headers(loader, info, library_count)?;
    let instr_base = info.reloc_instr_offset as usize;
    if instr_base > loader.len() {
        bail!("reloc_instr_offset past loader end");
    }
    let instr_stream = &loader[instr_base..];

    let mut total_count: u32 = 0;
    for header in &headers {
        let pef_idx = header.section_index as usize;
        let Some(obj_idx) = pef_to_obj.get(pef_idx).copied().flatten() else {
            log::warn!(
                "Reloc header targets non-instantiated PEF section {pef_idx}; skipping"
            );
            continue;
        };
        let target_base = pef_section_default_addr
            .get(pef_idx)
            .copied()
            .unwrap_or(0);

        // Run VM into a scratch buffer, borrowing the section data mutably
        // just for the VM execution window.
        let mut pending: Vec<PendingFixup> = Vec::new();
        {
            let section = &mut obj.sections[obj_idx];
            execute_reloc_vm(
                instr_stream,
                header,
                &mut section.data,
                pef_section_default_addr,
                import_sym_indices,
                default_section_c,
                default_section_d,
                &mut pending,
            )
            .with_context(|| format!("Running PEF reloc VM for section {pef_idx}"))?;
        }

        // Resolve pending fixups to ObjRelocs.  For Va targets, look up
        // (or synthesise) a symbol at the target address.
        let mut misaligned = 0u32;
        for fixup in pending {
            if fixup.offset & 0x3 != 0 {
                misaligned += 1;
                continue;
            }
            let reloc_va = target_base.wrapping_add(fixup.offset);
            let (target_symbol, addend) = match fixup.target {
                PendingRelocTarget::Import(sym_idx) => {
                    (sym_idx, fixup.original_word as i64)
                }
                PendingRelocTarget::Va(va) => {
                    let (tgt_sec, _) = match obj.sections.at_address(va) {
                        Ok(r) => r,
                        Err(_) => {
                            log::warn!(
                                "Reloc at {:#x} targets unknown VA {:#x}; skipping",
                                reloc_va,
                                va
                            );
                            continue;
                        }
                    };
                    let tgt = SectionAddress::new(tgt_sec, va);
                    match obj.symbols.for_relocation(tgt, ObjRelocKind::Absolute)? {
                        Some((sym_idx, sym)) => {
                            (sym_idx, va as i64 - sym.address as i64)
                        }
                        None => {
                            let sym_idx = obj.symbols.add_direct(ObjSymbol {
                                name: format!("lbl_{:08X}", va),
                                address: va as u64,
                                section: Some(tgt_sec),
                                ..Default::default()
                            })?;
                            (sym_idx, 0i64)
                        }
                    }
                }
            };
            let section = &mut obj.sections[obj_idx];
            if section
                .relocations
                .insert(reloc_va, ObjReloc {
                    kind: ObjRelocKind::Absolute,
                    target_symbol,
                    addend,
                    module: None,
                })
                .is_ok()
            {
                total_count += 1;
            }
        }
        if misaligned > 0 {
            log::warn!(
                "PEF reloc section {pef_idx}: {misaligned} misaligned fixup(s) skipped"
            );
        }
    }
    Ok(total_count)
}
