use std::num::NonZeroU64;

use anyhow::{Context, Result, bail};
use cwdemangle::demangle;
use flagset::Flags;
use object::{
    Architecture, BinaryFormat, Endianness, Object, ObjectKind, ObjectSection, ObjectSymbol,
    RelocationEncoding, RelocationKind, SectionKind, SymbolFlags, SymbolKind, SymbolScope,
    write::{
        Object as WriteObject, Relocation, RelocationFlags,
        SectionId, Symbol, SymbolId, SymbolSection as WriteSymbolSection,
    },
};

use crate::obj::{
    ObjArchitecture, ObjInfo, ObjKind, ObjSection, ObjSectionKind, ObjSymbol, ObjSymbolFlagSet,
    ObjSymbolFlags, ObjSymbolKind, ObjRelocKind, SectionIndex as ObjSectionIndex,
};

pub fn process_coff(data: &[u8], name: &str) -> Result<ObjInfo> {
    let obj_file = object::File::parse(data).context("Failed to parse COFF/PE file")?;

    let architecture = match obj_file.architecture() {
        Architecture::I386 => ObjArchitecture::X86,
        Architecture::PowerPc => ObjArchitecture::PowerPc,
        arch => bail!("Unsupported architecture: {arch:?}"),
    };

    let kind = match obj_file.kind() {
        ObjectKind::Executable => ObjKind::Executable,
        ObjectKind::Relocatable => ObjKind::Relocatable,
        kind => bail!("Unexpected COFF type: {kind:?}"),
    };

    let mut sections: Vec<ObjSection> = vec![];
    let mut section_indexes: Vec<Option<usize>> = vec![None]; // index 0 = null section

    for section in obj_file.sections() {
        if section.size() == 0 {
            section_indexes.push(None);
            continue;
        }
        let section_name = section.name().context("Section name")?;
        let section_kind = match section.kind() {
            SectionKind::Text => ObjSectionKind::Code,
            SectionKind::Data | SectionKind::OtherString => ObjSectionKind::Data,
            SectionKind::ReadOnlyData => ObjSectionKind::ReadOnlyData,
            SectionKind::UninitializedData => ObjSectionKind::Bss,
            _ => {
                section_indexes.push(None);
                continue;
            }
        };
        section_indexes.push(Some(sections.len()));
        let data = if section_kind == ObjSectionKind::Bss {
            vec![]
        } else {
            // Only read physical (on-disk) bytes. The gap between SizeOfRawData and
            // VirtualSize is implicitly zero-initialized BSS; split_obj handles it.
            section.uncompressed_data().context("Section data")?.to_vec()
        };
        sections.push(ObjSection {
            name: section_name.to_string(),
            kind: section_kind,
            address: section.address(),
            size: section.size(), // VirtualSize — covers full address range
            data,
            align: section.align().max(1),
            elf_index: section.index().0 as ObjSectionIndex,
            relocations: Default::default(),
            virtual_address: None,
            file_offset: section.file_range().map(|(v, _)| v).unwrap_or_default(),
            section_known: true,
            splits: Default::default(),
        });
    }

    let mut symbols: Vec<ObjSymbol> = vec![];
    let mut stack_address: Option<u32> = None;
    let mut stack_end: Option<u32> = None;
    let mut db_stack_addr: Option<u32> = None;
    let mut arena_lo: Option<u32> = None;
    let mut arena_hi: Option<u32> = None;
    let mut sda_base: Option<u32> = None;
    let mut sda2_base: Option<u32> = None;

    for symbol in obj_file.symbols() {
        let symbol_name = match symbol.name() {
            Ok(n) if !n.is_empty() => n,
            _ => continue,
        };

        match symbol_name {
            "_stack_addr" => stack_address = Some(symbol.address() as u32),
            "_stack_end" => stack_end = Some(symbol.address() as u32),
            "_db_stack_addr" => db_stack_addr = Some(symbol.address() as u32),
            "__ArenaLo" => arena_lo = Some(symbol.address() as u32),
            "__ArenaHi" => arena_hi = Some(symbol.address() as u32),
            "_SDA_BASE_" => sda_base = Some(symbol.address() as u32),
            "_SDA2_BASE_" => sda2_base = Some(symbol.address() as u32),
            _ => {}
        }

        if matches!(symbol.kind(), SymbolKind::Section | SymbolKind::File) {
            continue;
        }

        let symbol_kind = match symbol.kind() {
            SymbolKind::Text => ObjSymbolKind::Function,
            SymbolKind::Data => ObjSymbolKind::Object,
            SymbolKind::Label | SymbolKind::Unknown => ObjSymbolKind::Unknown,
            _ => continue,
        };

        let section_index = symbol
            .section_index()
            .and_then(|idx| section_indexes.get(idx.0).copied())
            .flatten();

        let mut flags = ObjSymbolFlagSet(ObjSymbolFlags::none());
        if symbol.is_global() {
            flags = ObjSymbolFlagSet(flags.0 | ObjSymbolFlags::Global);
        }
        if symbol.is_local() {
            flags = ObjSymbolFlagSet(flags.0 | ObjSymbolFlags::Local);
        }

        symbols.push(ObjSymbol {
            name: symbol_name.to_string(),
            demangled_name: demangle(symbol_name, &Default::default()),
            address: symbol.address(),
            section: section_index.map(|s| s as ObjSectionIndex),
            size: symbol.size(),
            size_known: symbol.size() > 0,
            flags,
            kind: symbol_kind,
            ..Default::default()
        });
    }

    let mut obj = ObjInfo::new(kind, architecture, name.to_string(), symbols, sections);
    obj.entry = NonZeroU64::new(obj_file.entry()).map(|n| n.get());
    obj.sda2_base = sda2_base;
    obj.sda_base = sda_base;
    obj.stack_address = stack_address;
    obj.stack_end = stack_end;
    obj.db_stack_addr = db_stack_addr;
    obj.arena_lo = arena_lo;
    obj.arena_hi = arena_hi;
    Ok(obj)
}

pub fn write_coff(obj: &ObjInfo, export_all: bool) -> Result<Vec<u8>> {
    let mut out = WriteObject::new(BinaryFormat::Coff, Architecture::I386, Endianness::Little);

    // Add sections and build section id map (indexed by ObjSectionIndex)
    let mut section_ids: Vec<Option<SectionId>> = vec![None; obj.sections.len() as usize];
    for (idx, section) in obj.sections.iter() {
        let kind = match section.kind {
            ObjSectionKind::Code => SectionKind::Text,
            ObjSectionKind::Data => SectionKind::Data,
            ObjSectionKind::ReadOnlyData => SectionKind::ReadOnlyData,
            ObjSectionKind::Bss => SectionKind::UninitializedData,
        };
        let sid = out.add_section(vec![], section.name.as_bytes().to_vec(), kind);
        if section.kind == ObjSectionKind::Bss {
            out.append_section_bss(sid, section.size, section.align.max(1));
        } else {
            // Zero out bytes at relocation sites; addend is carried by the relocation record
            let mut data = section.data.clone();
            for (addr, _) in section.relocations.iter() {
                let off = (addr as u64 - section.address) as usize;
                if off + 4 <= data.len() {
                    data[off..off + 4].fill(0);
                }
            }
            out.set_section_data(sid, data, section.align.max(1));
        }
        section_ids[idx as usize] = Some(sid);
    }

    // Add symbols and build symbol id map (indexed by SymbolIndex)
    let mut symbol_ids: Vec<SymbolId> = Vec::with_capacity(obj.symbols.count() as usize);
    for (_, sym) in obj.symbols.iter() {
        let sym_section = match sym.section {
            Some(sec_idx) => match section_ids.get(sec_idx as usize).copied().flatten() {
                Some(sid) => WriteSymbolSection::Section(sid),
                None => WriteSymbolSection::Undefined,
            },
            None => WriteSymbolSection::Undefined,
        };
        let is_exported = sym.flags.0.contains(ObjSymbolFlags::Exported)
            || sym.flags.0.contains(ObjSymbolFlags::Global)
            || (export_all
                && !sym.flags.0.contains(ObjSymbolFlags::NoExport)
                && matches!(sym.kind, ObjSymbolKind::Function | ObjSymbolKind::Object));
        let scope = if sym.flags.0.contains(ObjSymbolFlags::Weak) {
            SymbolScope::Linkage
        } else if is_exported {
            SymbolScope::Linkage
        } else {
            SymbolScope::Compilation
        };
        let kind = match sym.kind {
            ObjSymbolKind::Function => SymbolKind::Text,
            ObjSymbolKind::Object => SymbolKind::Data,
            ObjSymbolKind::Section => SymbolKind::Section,
            ObjSymbolKind::Unknown => SymbolKind::Unknown,
        };
        let sid = out.add_symbol(Symbol {
            name: sym.name.as_bytes().to_vec(),
            value: sym.address,
            size: sym.size,
            kind,
            scope,
            weak: sym.flags.0.contains(ObjSymbolFlags::Weak),
            section: sym_section,
            flags: SymbolFlags::None,
        });
        symbol_ids.push(sid);
    }

    // Add relocations
    for (sec_idx, section) in obj.sections.iter() {
        let sid = match section_ids[sec_idx as usize] {
            Some(id) => id,
            None => continue,
        };
        for (addr, reloc) in section.relocations.iter() {
            let (kind, encoding, size) = match reloc.kind {
                ObjRelocKind::X86Abs32 => {
                    (RelocationKind::Absolute, RelocationEncoding::Generic, 32)
                }
                ObjRelocKind::X86Rel32 => {
                    (RelocationKind::Relative, RelocationEncoding::Generic, 32)
                }
                _ => continue,
            };
            let offset = addr as u64 - section.address;
            let sym_id = symbol_ids[reloc.target_symbol as usize];
            out.add_relocation(sid, Relocation {
                offset,
                symbol: sym_id,
                addend: reloc.addend,
                flags: RelocationFlags::Generic { kind, encoding, size },
            })
            .with_context(|| {
                format!("Adding relocation at {:#x} in section {}", addr, section.name)
            })?;
        }
    }

    out.write().map_err(|e| anyhow::anyhow!("{e:?}"))
}
