use std::num::NonZeroU64;

use anyhow::{Context, Result, bail};
use cwdemangle::demangle;
use flagset::Flags;
use object::{
    Architecture, BinaryFormat, Endianness, Object, ObjectKind, ObjectSection, ObjectSymbol,
    RelocationEncoding, RelocationKind, RelocationTarget, SectionKind, SymbolFlags, SymbolKind,
    SymbolScope,
    write::{
        Object as WriteObject, Relocation, RelocationFlags,
        SectionId, Symbol, SymbolId, SymbolSection as WriteSymbolSection,
    },
};

use crate::{
    analysis::cfa::SectionAddress,
    obj::{
        ObjArchitecture, ObjInfo, ObjKind, ObjReloc, ObjRelocKind, ObjSection, ObjSectionKind,
        ObjSplit, ObjSymbol, ObjSymbolFlagSet, ObjSymbolFlags, ObjSymbolKind,
        SectionIndex as ObjSectionIndex,
    },
};

/// Returns the parsed `ObjInfo` and, for PE executables, the ImageBase.
pub fn process_coff(data: &[u8], name: &str) -> Result<(ObjInfo, Option<u32>)> {
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
    // Maps COFF symbol index → our ObjSymbol vector index.
    // Needed to resolve COFF relocation targets for .obj files.
    let mut coff_sym_map: std::collections::BTreeMap<usize, usize> = Default::default();
    let mut stack_address: Option<u32> = None;
    let mut stack_end: Option<u32> = None;
    let mut db_stack_addr: Option<u32> = None;
    let mut arena_lo: Option<u32> = None;
    let mut arena_hi: Option<u32> = None;
    let mut sda_base: Option<u32> = None;
    let mut sda2_base: Option<u32> = None;

    for symbol in obj_file.symbols() {
        let coff_idx = symbol.index().0;
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

        coff_sym_map.insert(coff_idx, symbols.len());
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

    // For relocatable (.obj) files, read COFF section relocations so that
    // analyze_x86_functions can distinguish resolved vs unresolved operands.
    if kind == ObjKind::Relocatable {
        for section in obj_file.sections() {
            let sec_idx = match section_indexes.get(section.index().0).copied().flatten() {
                Some(idx) => idx,
                None => continue,
            };
            let sec_addr = sections[sec_idx].address;
            for (offset, reloc) in section.relocations() {
                let target_sym = match reloc.target() {
                    RelocationTarget::Symbol(idx) => {
                        match coff_sym_map.get(&idx.0) {
                            Some(&our_idx) => our_idx as u32,
                            None => continue,
                        }
                    }
                    _ => continue,
                };
                let reloc_kind = match reloc.kind() {
                    RelocationKind::Relative => ObjRelocKind::X86Rel32,
                    RelocationKind::Absolute => ObjRelocKind::X86Abs32,
                    _ => continue,
                };
                let addr = sec_addr + offset;
                sections[sec_idx].relocations.replace(addr as u32, ObjReloc {
                    kind: reloc_kind,
                    target_symbol: target_sym,
                    addend: reloc.addend(),
                    module: None,
                });
            }
        }
    }

    // Extract ImageBase from the PE optional header (x86 PE32 only)
    let image_base: Option<u32> = if kind == ObjKind::Executable {
        use object::{LittleEndian as LE, read::pe::{ImageNtHeaders, PeFile32}};
        PeFile32::parse(data)
            .ok()
            .map(|pe| pe.nt_headers().optional_header().image_base.get(LE))
    } else {
        None
    };

    let mut obj = ObjInfo::new(kind, architecture, name.to_string(), symbols, sections);
    obj.entry = NonZeroU64::new(obj_file.entry()).map(|n| n.get());
    obj.sda2_base = sda2_base;
    obj.sda_base = sda_base;
    obj.stack_address = stack_address;
    obj.stack_end = stack_end;
    obj.db_stack_addr = db_stack_addr;
    obj.arena_lo = arena_lo;
    obj.arena_hi = arena_hi;
    Ok((obj, image_base))
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
            ObjSymbolKind::Unknown => SymbolKind::Label,
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
            let offset = (addr as u64).saturating_sub(section.address) as usize;
            // Skip relocations whose 4-byte field extends past the end of the
            // section data.  This can happen when a false-positive function split
            // cuts a boundary mid-instruction; the relocation belongs to the
            // correctly-sized split of the enclosing function.
            if offset + 4 > section.data.len() {
                log::warn!(
                    "Skipping relocation at {:#010X} in section {} (offset {} + 4 > {} bytes): \
                     split boundary may be mid-instruction",
                    addr,
                    section.name,
                    offset,
                    section.data.len()
                );
                continue;
            }
            let sym_id = symbol_ids[reloc.target_symbol as usize];
            out.add_relocation(sid, Relocation {
                offset: offset as u64,
                symbol: sym_id,
                addend: reloc.addend,
                flags: RelocationFlags::Generic { kind, encoding, size },
            })
            .with_context(|| {
                format!("Adding relocation at {:#010X} in section {}", addr, section.name)
            })?;
        }
    }

    out.write().map_err(|e| anyhow::anyhow!("{e:?}"))
}

const IMAGE_REL_BASED_HIGHLOW: u16 = 3;

/// Parse the PE `.reloc` section and add [`ObjRelocKind::X86Abs32`] relocations.
pub fn apply_base_relocations(obj: &mut ObjInfo, image_base: u32) -> Result<()> {
    let reloc_data = {
        let Some((_, section)) = obj.sections.iter().find(|(_, s)| s.name == ".reloc") else {
            log::debug!("No .reloc section, skipping base relocation import");
            return Ok(());
        };
        if section.data.is_empty() {
            return Ok(());
        }
        section.data.clone()
    };

    let mut block_off = 0usize;
    let mut count = 0u32;
    while block_off + 8 <= reloc_data.len() {
        let page_rva =
            u32::from_le_bytes(reloc_data[block_off..block_off + 4].try_into().unwrap());
        let block_size =
            u32::from_le_bytes(reloc_data[block_off + 4..block_off + 8].try_into().unwrap());
        if block_size < 8 {
            break;
        }
        let num_entries = (block_size - 8) / 2;
        for i in 0..num_entries as usize {
            let e = block_off + 8 + i * 2;
            if e + 2 > reloc_data.len() {
                break;
            }
            let type_offset =
                u16::from_le_bytes(reloc_data[e..e + 2].try_into().unwrap());
            if type_offset >> 12 != IMAGE_REL_BASED_HIGHLOW {
                continue;
            }
            let reloc_va = image_base.wrapping_add(page_rva + (type_offset & 0x0FFF) as u32);

            let Ok((src_idx, _)) = obj.sections.at_address(reloc_va) else { continue };
            let src_sec = &obj.sections[src_idx];
            if src_sec.kind == ObjSectionKind::Bss || src_sec.relocations.at(reloc_va).is_some() {
                continue;
            }
            let off = (reloc_va as u64 - src_sec.address) as usize;
            if off + 4 > src_sec.data.len() {
                continue;
            }
            let target_va =
                u32::from_le_bytes(src_sec.data[off..off + 4].try_into().unwrap());
            if target_va == 0 {
                continue;
            }
            let Ok((tgt_idx, _)) = obj.sections.at_address(target_va) else { continue };
            let tgt_addr = SectionAddress::new(tgt_idx, target_va);
            let (target_symbol, addend) =
                match obj.symbols.for_relocation(tgt_addr, ObjRelocKind::X86Abs32)? {
                    Some((sym_idx, sym)) => (sym_idx, target_va as i64 - sym.address as i64),
                    None => {
                        let sym_idx = obj.symbols.add_direct(ObjSymbol {
                            name: format!("lbl_{:08X}", target_va),
                            address: target_va as u64,
                            section: Some(tgt_idx),
                            ..Default::default()
                        })?;
                        (sym_idx, 0)
                    }
                };
            let src_sec = &mut obj.sections[src_idx];
            src_sec
                .relocations
                .insert(reloc_va, ObjReloc {
                    kind: ObjRelocKind::X86Abs32,
                    target_symbol,
                    addend,
                    module: None,
                })
                .ok();
            count += 1;
        }
        block_off += block_size as usize;
    }
    log::info!("Applied {count} abs32 relocations from .reloc section");
    Ok(())
}

/// Create one `ObjSplit` per `Function`-kind symbol in code sections so that
/// each function becomes its own compilation unit, mirroring what the DOL
/// pipeline does via Tracker + CFA.
///
/// Only creates splits that don't already exist (user-defined splits in
/// `splits.txt` take precedence).
pub fn create_function_splits(obj: &mut ObjInfo) -> Result<()> {
    let code_sections: Vec<ObjSectionIndex> = obj
        .sections
        .iter()
        .filter(|(_, s)| s.kind == ObjSectionKind::Code)
        .map(|(idx, _)| idx)
        .collect();

    let mut total = 0u32;
    for sec_idx in code_sections {
        let section_end = {
            let s = &obj.sections[sec_idx];
            (s.address + s.size) as u32
        };

        // Collect (address, name) for every Function symbol in this section,
        // sorted by address.
        let fn_symbols: Vec<(u32, String)> = {
            let mut v: Vec<(u32, String)> = obj
                .symbols
                .for_section(sec_idx)
                .filter(|(_, sym)| sym.kind == ObjSymbolKind::Function)
                .map(|(_, sym)| (sym.address as u32, sym.name.clone()))
                .collect();
            v.sort_by_key(|(addr, _)| *addr);
            v
        };

        for (i, (addr, name)) in fn_symbols.iter().enumerate() {
            // Skip if a split already exists at this address.
            if obj.sections[sec_idx].splits.for_address(*addr).is_some() {
                continue;
            }
            let end = fn_symbols
                .get(i + 1)
                .map(|(next_addr, _)| *next_addr)
                .unwrap_or(section_end);

            obj.sections[sec_idx].splits.push(*addr, ObjSplit {
                unit: name.clone(),
                end,
                align: Some(1), // x86 functions have no guaranteed alignment
                common: false,
                autogenerated: true,
                skip: false,
                rename: None,
            });
            total += 1;
        }
    }

    log::info!("Created {total} function splits");
    Ok(())
}
