//! XCOFF32 PowerPC relocatable object writer.
//!
//! dtk's Nintendo-CW path emits ELF `.o`s consumed by `mwldeppc`.  The Mac CW
//! / MPW toolchains that build PEF binaries consume **XCOFF**, not ELF, so
//! `dtk pef split` cannot reuse the ELF writer.  This module emits minimal
//! XCOFF32 big-endian PowerPC relocatable files that `PPCLink` (MPW) or
//! `MWLinker PPC` (CodeWarrior Pro Mac) can ingest.
//!
//! Target linkers:
//! - MPW `PPCLink` → XCOFF executable → `MakePEF` → PEF
//! - CodeWarrior Pro Mac `MWLinker PPC` → PEF directly
//!
//! The object crate's XCOFF writer in 0.36 produced malformed output (under-
//! reported `f_nsyms`, garbled string table length), so we emit bytes by
//! hand.  Format references: IBM AIX `/usr/include/xcoff.h`,
//! "AIX Version 7.2: Files Reference" XCOFF chapter.

use anyhow::Result;
use object::xcoff;

use crate::obj::{ObjInfo, ObjRelocKind, ObjSectionKind, ObjSymbolFlags};

const SYM_SIZE: usize = 18;
const RLD_SIZE: usize = 10;
const SEC_HDR_SIZE: usize = 40;
const FILE_HDR_SIZE: usize = 20;

#[derive(Default)]
struct StrTab {
    data: Vec<u8>,
}

impl StrTab {
    fn new() -> Self {
        // First 4 bytes are the length (including these 4 bytes themselves);
        // set to 4 initially and patched at the end.
        Self { data: vec![0, 0, 0, 4] }
    }
    fn add(&mut self, s: &str) -> u32 {
        let offset = self.data.len() as u32;
        self.data.extend_from_slice(s.as_bytes());
        self.data.push(0);
        offset
    }
    fn finalize(&mut self) {
        let len = self.data.len() as u32;
        self.data[0..4].copy_from_slice(&len.to_be_bytes());
    }
}

fn write_u8(v: &mut Vec<u8>, x: u8) { v.push(x); }
fn write_u16(v: &mut Vec<u8>, x: u16) { v.extend_from_slice(&x.to_be_bytes()); }
fn write_i16(v: &mut Vec<u8>, x: i16) { v.extend_from_slice(&x.to_be_bytes()); }
fn write_u32(v: &mut Vec<u8>, x: u32) { v.extend_from_slice(&x.to_be_bytes()); }

/// Emit a dtk split object as an XCOFF32 PPC `.o`.
///
/// Layout:
/// ```text
///   FileHeader                       20 bytes
///   SectionHeader[n_sections]        40 bytes each
///   section raw data                 (aligned)
///   RLD entries (per section)        10 bytes each
///   Symbol table                     18 bytes each (primary + aux)
///   String table                     4-byte length + concatenated names
/// ```
pub fn write_xcoff(obj: &ObjInfo, _export_all: bool) -> Result<Vec<u8>> {
    // Collect emittable sections in a deterministic order (ObjSections order).
    let mut sec_infos: Vec<SecInfo> = Vec::new();
    let mut section_to_idx: Vec<Option<usize>> = vec![None; obj.sections.len() as usize];
    for (obj_idx, section) in obj.sections.iter() {
        // XCOFF section names must follow AIX convention (.text/.data/.bss) for
        // the linker to merge them.  dtk's original names (e.g. .code0, .data0)
        // are PEF section names and would be silently dropped.
        let (styp, has_data, name) = match section.kind {
            ObjSectionKind::Code => (xcoff::STYP_TEXT, true, ".text"),
            ObjSectionKind::Data => (xcoff::STYP_DATA, true, ".data"),
            ObjSectionKind::ReadOnlyData => (xcoff::STYP_TEXT, true, ".text"),
            ObjSectionKind::Bss => (xcoff::STYP_BSS, false, ".bss"),
        };
        section_to_idx[obj_idx as usize] = Some(sec_infos.len());
        sec_infos.push(SecInfo {
            obj_idx,
            name: name.to_string(),
            styp,
            has_data,
            size: section.size as u32,
            align_log2: log2_align(section.align.max(1)) as u8,
        });
    }

    // XCOFF csect model:
    //   - ONE section csect per emitted section (XTY_SD, spans whole section).
    //     Carries storage mapping class (XMC_PR/RW/BS) for the linker.
    //   - Every user-defined symbol is an XTY_LD label *inside* that csect.
    //     Its aux `x_scnlen` field is reused as the containing-csect symbol
    //     index (1-based symtab index of the section csect).
    //   - Undefined (extern) symbols stay XTY_ER with XMC_PR.
    // Without the enclosing section csect, overlapping XTY_SD labels confuse
    // BFD (xcofflink.c:5927 BFD_FAIL on unresolved R_BR during partial link)
    // and cause silent content-drop during full link.
    let mut strtab = StrTab::new();
    let mut xsyms: Vec<XSym> = Vec::with_capacity(obj.symbols.count() as usize + sec_infos.len());
    // Maps dtk SymbolIndex → XCOFF primary entry index (for RLD r_symndx).
    let mut xsym_index: Vec<u32> = vec![u32::MAX; obj.symbols.count() as usize];
    // Maps SecInfo index → symtab index of synthetic section csect (for XTY_LD aux).
    let mut section_csect_sym_idx: Vec<u32> = vec![0; sec_infos.len()];

    // Emit section csects first so user labels can reference them by index.
    for (i, si) in sec_infos.iter().enumerate() {
        let xcoff_idx = (xsyms.len() * 2) as u32;
        section_csect_sym_idx[i] = xcoff_idx;
        let smclas = match obj.sections[si.obj_idx].kind {
            ObjSectionKind::Code => xcoff::XMC_PR,
            ObjSectionKind::ReadOnlyData => xcoff::XMC_RO,
            ObjSectionKind::Data => xcoff::XMC_RW,
            ObjSectionKind::Bss => xcoff::XMC_BS,
        };
        let str_off = if si.name.len() <= 8 { 0 } else { strtab.add(&si.name) };
        xsyms.push(XSym {
            name: si.name.clone(),
            str_off,
            value: 0,
            scnum: (i as i16) + 1,
            sclass: xcoff::C_HIDEXT,
            scnlen: si.size,
            smtyp: xcoff::XTY_SD,
            smclas,
        });
    }

    for (sym_idx, sym) in obj.symbols.iter() {
        let xcoff_idx = (xsyms.len() * 2) as u32;
        xsym_index[sym_idx as usize] = xcoff_idx;

        let (n_scnum, csect_idx): (i16, Option<usize>) = match sym.section {
            Some(dtk_sec) => match section_to_idx.get(dtk_sec as usize).copied().flatten() {
                Some(xidx) => ((xidx as i16) + 1, Some(xidx)),
                None => (0, None),
            },
            None => (0, None),
        };
        let is_defined = n_scnum != 0;
        let is_exported = sym.flags.0.contains(ObjSymbolFlags::Exported)
            || sym.flags.0.contains(ObjSymbolFlags::Global);
        let is_weak = sym.flags.0.contains(ObjSymbolFlags::Weak);
        let sclass = if !is_defined {
            xcoff::C_EXT
        } else if is_weak {
            xcoff::C_WEAKEXT
        } else if sym.flags.0.contains(ObjSymbolFlags::Local) && !is_exported {
            xcoff::C_HIDEXT
        } else {
            xcoff::C_EXT
        };
        // For XTY_LD the x_scnlen field is repurposed: it holds the
        // containing csect's symbol-table index, not a length.
        let (smtyp, smclas, scnlen) = if is_defined {
            let sec = &obj.sections[sym.section.unwrap()];
            let scls = match sec.kind {
                ObjSectionKind::Code => xcoff::XMC_PR,
                ObjSectionKind::ReadOnlyData => xcoff::XMC_RO,
                ObjSectionKind::Data => xcoff::XMC_RW,
                ObjSectionKind::Bss => xcoff::XMC_BS,
            };
            (xcoff::XTY_LD, scls, section_csect_sym_idx[csect_idx.unwrap()])
        } else {
            (xcoff::XTY_ER, xcoff::XMC_PR, 0)
        };

        let str_off = if sym.name.len() <= 8 { 0 } else { strtab.add(&sym.name) };

        xsyms.push(XSym {
            name: sym.name.clone(),
            str_off,
            value: sym.address as u32,
            scnum: n_scnum,
            sclass,
            scnlen,
            smtyp,
            smclas,
        });
    }

    // Layout offsets.
    let n_sections = sec_infos.len();
    let mut offset = FILE_HDR_SIZE + n_sections * SEC_HDR_SIZE;

    // Section data regions.
    let mut sec_data_off: Vec<u32> = vec![0; n_sections];
    for (i, si) in sec_infos.iter().enumerate() {
        if si.has_data {
            offset = align_up(offset, 4);
            sec_data_off[i] = offset as u32;
            offset += si.size as usize;
        }
    }

    // RLD regions.
    let mut sec_reloc_off: Vec<u32> = vec![0; n_sections];
    let mut sec_reloc_count: Vec<u16> = vec![0; n_sections];
    for (i, si) in sec_infos.iter().enumerate() {
        let section = &obj.sections[si.obj_idx];
        let mut count = 0u32;
        for (_addr, reloc) in section.relocations.iter() {
            if mapped_reloc_type(reloc.kind).is_some() {
                count += 1;
            }
        }
        if count > 0 {
            sec_reloc_off[i] = offset as u32;
            sec_reloc_count[i] = count as u16;
            offset += count as usize * RLD_SIZE;
        }
    }

    // Symtab.
    let symtab_offset = offset as u32;
    let symtab_entries = (xsyms.len() * 2) as u32;
    offset += symtab_entries as usize * SYM_SIZE;

    // Strtab starts here; finalize so length field is correct.
    strtab.finalize();
    let _strtab_offset = offset;

    // Emit.
    let mut out = Vec::with_capacity(offset + strtab.data.len());

    // FileHeader.
    write_u16(&mut out, xcoff::MAGIC_32);
    write_u16(&mut out, n_sections as u16);
    write_u32(&mut out, 0); // f_timdat
    write_u32(&mut out, symtab_offset);
    write_u32(&mut out, symtab_entries);
    write_u16(&mut out, 0); // f_opthdr
    write_u16(&mut out, 0); // f_flags

    // Section headers.
    for (i, si) in sec_infos.iter().enumerate() {
        let mut name = [0u8; 8];
        let nbytes = si.name.as_bytes();
        let nlen = nbytes.len().min(8);
        name[..nlen].copy_from_slice(&nbytes[..nlen]);
        out.extend_from_slice(&name);
        write_u32(&mut out, 0);                        // s_paddr
        write_u32(&mut out, 0);                        // s_vaddr
        write_u32(&mut out, si.size);
        write_u32(&mut out, sec_data_off[i]);
        write_u32(&mut out, sec_reloc_off[i]);
        write_u32(&mut out, 0);                        // s_lnnoptr
        write_u16(&mut out, sec_reloc_count[i]);
        write_u16(&mut out, 0);                        // s_nlnno
        // s_flags: upper 8 bits can hold alignment (XCOFF32 convention via csect)
        write_u32(&mut out, si.styp as u32);
    }

    // Section data.
    for (i, si) in sec_infos.iter().enumerate() {
        if !si.has_data { continue; }
        while out.len() < sec_data_off[i] as usize { out.push(0); }
        let section = &obj.sections[si.obj_idx];
        let mut data = section.data.clone();
        // Pad to declared size if underfilled.
        if data.len() < si.size as usize {
            data.resize(si.size as usize, 0);
        } else if data.len() > si.size as usize {
            data.truncate(si.size as usize);
        }
        // XCOFF reloc convention (partial_inplace=true): the in-place field
        // at the reloc site holds the ADDEND, and the linker writes
        // `final = (field & ~dst_mask) | ((field & src_mask) + relocation)`.
        // dtk's section data mirrors the original linked binary, so those
        // fields currently hold pre-baked resolved values (absolute addrs,
        // shifted branch displacements, etc.) — feeding that to the linker
        // double-adds and overflows.  Strip the reloc-field bits and reinsert
        // the addend instead.
        //
        // PC-relative XCOFF quirk (see coff-rs6000.c:3192-3194): BFD's
        // xcoff_reloc_type_br computes `*relocation = val + addend + r_vaddr
        // - site_final`, which reduces to `target_absolute` when
        // input_section->vma == 0 (our case).  The linker then adds this to
        // the in-place field.  For the result to be the pc-rel displacement
        // we need `field & src_mask = -r_vaddr`, i.e. bias pc-rel fields by
        // -r_vaddr ("the original PC-relative relocation is biased by
        // -r_vaddr" per that comment).
        for (addr, reloc) in section.relocations.iter() {
            if mapped_reloc_type(reloc.kind).is_none() { continue; }
            let off = (addr as u64 - section.address) as usize;
            let r_vaddr = off as u32;
            match reloc.kind {
                ObjRelocKind::Absolute => {
                    if off + 4 <= data.len() {
                        data[off..off + 4]
                            .copy_from_slice(&(reloc.addend as u32).to_be_bytes());
                    }
                }
                ObjRelocKind::PpcRel24 => {
                    if off + 4 <= data.len() {
                        let sym_val = obj.symbols[reloc.target_symbol].address as u32;
                        let mut w = u32::from_be_bytes(data[off..off + 4].try_into().unwrap());
                        w &= !0x03fffffc;
                        let biased = sym_val
                            .wrapping_add(reloc.addend as u32)
                            .wrapping_sub(r_vaddr);
                        w |= biased & 0x03fffffc;
                        data[off..off + 4].copy_from_slice(&w.to_be_bytes());
                    }
                }
                ObjRelocKind::PpcRel14 => {
                    if off + 4 <= data.len() {
                        let sym_val = obj.symbols[reloc.target_symbol].address as u32;
                        let mut w = u32::from_be_bytes(data[off..off + 4].try_into().unwrap());
                        w &= !0x0000fffc;
                        let biased = sym_val
                            .wrapping_add(reloc.addend as u32)
                            .wrapping_sub(r_vaddr);
                        w |= biased & 0x0000fffc;
                        data[off..off + 4].copy_from_slice(&w.to_be_bytes());
                    }
                }
                ObjRelocKind::PpcAddr16Hi
                | ObjRelocKind::PpcAddr16Ha
                | ObjRelocKind::PpcAddr16Lo => {
                    if off + 4 <= data.len() {
                        let mut w = u32::from_be_bytes(data[off..off + 4].try_into().unwrap());
                        w &= !0x0000ffff;
                        let hi = matches!(
                            reloc.kind,
                            ObjRelocKind::PpcAddr16Hi | ObjRelocKind::PpcAddr16Ha
                        );
                        let imm = if hi {
                            ((reloc.addend as u32) >> 16) & 0xffff
                        } else {
                            (reloc.addend as u32) & 0xffff
                        };
                        w |= imm;
                        data[off..off + 4].copy_from_slice(&w.to_be_bytes());
                    }
                }
                _ => {}
            }
        }
        out.extend_from_slice(&data);
    }

    // RLDs (per section, in same order).
    for (i, si) in sec_infos.iter().enumerate() {
        if sec_reloc_count[i] == 0 { continue; }
        while out.len() < sec_reloc_off[i] as usize { out.push(0); }
        let section = &obj.sections[si.obj_idx];
        for (addr, reloc) in section.relocations.iter() {
            let (r_rtype, r_rsize) = match mapped_reloc_type(reloc.kind) {
                Some(v) => v,
                None => continue,
            };
            let r_vaddr = (addr as u64 - section.address) as u32;
            let r_symndx = xsym_index[reloc.target_symbol as usize];
            write_u32(&mut out, r_vaddr);
            write_u32(&mut out, r_symndx);
            write_u8(&mut out, r_rsize);
            write_u8(&mut out, r_rtype);
        }
    }

    // Symtab: primary + CsectAux per symbol.
    while out.len() < symtab_offset as usize { out.push(0); }
    for xs in &xsyms {
        // Primary.
        if xs.name.len() <= 8 {
            let mut n = [0u8; 8];
            n[..xs.name.len()].copy_from_slice(xs.name.as_bytes());
            out.extend_from_slice(&n);
        } else {
            out.extend_from_slice(&[0u8; 4]);        // n_zeroes
            out.extend_from_slice(&xs.str_off.to_be_bytes());
        }
        write_u32(&mut out, xs.value);
        write_i16(&mut out, xs.scnum);
        write_u16(&mut out, 0);                      // n_type
        write_u8(&mut out, xs.sclass);
        write_u8(&mut out, 1);                       // n_numaux

        // CsectAux32.
        write_u32(&mut out, xs.scnlen);              // x_scnlen
        write_u32(&mut out, 0);                      // x_parmhash
        write_u16(&mut out, 0);                      // x_snhash
        write_u8(&mut out, xs.smtyp);                // x_smtyp (alignment<<3 | type)
        write_u8(&mut out, xs.smclas);               // x_smclas
        write_u32(&mut out, 0);                      // x_stab
        write_u16(&mut out, 0);                      // x_snstab
    }

    // Strtab.
    out.extend_from_slice(&strtab.data);

    Ok(out)
}

struct SecInfo {
    obj_idx: crate::obj::SectionIndex,
    name: String,
    styp: u16,
    has_data: bool,
    size: u32,
    #[allow(dead_code)]
    align_log2: u8,
}

struct XSym {
    name: String,
    str_off: u32,
    value: u32,
    scnum: i16,
    sclass: u8,
    scnlen: u32,
    smtyp: u8,
    smclas: u8,
}

fn align_up(v: usize, a: usize) -> usize { (v + a - 1) & !(a - 1) }

fn log2_align(a: u64) -> u32 {
    if a <= 1 { return 0; }
    (63 - a.leading_zeros()) as u32
}

/// Map dtk reloc kind → (XCOFF r_rtype, r_rsize).  r_rsize encodes size-1.
fn mapped_reloc_type(kind: ObjRelocKind) -> Option<(u8, u8)> {
    match kind {
        ObjRelocKind::Absolute => Some((xcoff::R_POS, 31)),
        ObjRelocKind::PpcRel24 => Some((xcoff::R_BR, 25)),
        // R_BR + r_size=15 is rejected by BFD (R_BR HOWTO bitsize=26).
        // R_RBR + r_size=15 selects HOWTO[0x1d] (R_RBR_16, pc-relative, bitsize 16).
        ObjRelocKind::PpcRel14 => Some((xcoff::R_RBR, 15)),
        ObjRelocKind::PpcAddr16Hi | ObjRelocKind::PpcAddr16Ha => Some((xcoff::R_TOCU, 15)),
        ObjRelocKind::PpcAddr16Lo => Some((xcoff::R_TOCL, 15)),
        // No XCOFF equivalent for EABI SDA21 or x86 relocs.
        ObjRelocKind::PpcEmbSda21 | ObjRelocKind::X86Abs32 | ObjRelocKind::X86Rel32 => None,
    }
}

