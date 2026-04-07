use std::collections::{BTreeMap, btree_map};

use anyhow::{Result, anyhow, bail, ensure};
use base64::{Engine, engine::general_purpose::STANDARD};
use cwdemangle::{DemangleOptions, demangle};
use serde::{Deserialize, Serialize};
use sha1::{Digest, Sha1};
use typed_path::Utf8NativePath;

use crate::{
    analysis::{
        RelocationTarget,
        cfa::SectionAddress,
        tracker::{Relocation, Tracker},
        x86::analyze_x86_functions,
    },
    array_ref,
    obj::{
        ObjInfo, ObjKind, ObjReloc, ObjRelocKind, ObjSection, ObjSymbol, ObjSymbolFlagSet,
        ObjSymbolKind, SectionIndex, SymbolIndex,
    },
    util::{coff::{apply_base_relocations, process_coff}, elf::process_elf},
};

use anyhow::Context as _;

#[derive(Debug, Clone, Hash, Eq, PartialEq, Serialize, Deserialize)]
pub struct OutSymbol {
    pub kind: ObjSymbolKind,
    pub name: String,
    pub size: u32,
    pub flags: ObjSymbolFlagSet,
    pub section: Option<String>,
}

#[derive(Debug, Clone, Hash, Eq, PartialEq, Serialize, Deserialize)]
pub struct OutReloc {
    pub offset: u32,
    pub kind: ObjRelocKind,
    pub symbol: u32,
    pub addend: i32,
}

#[derive(Debug, Clone, Hash, Eq, PartialEq, Serialize, Deserialize)]
pub struct FunctionSignature {
    pub symbol: u32,
    pub hash: String,
    pub signature: String,
    pub symbols: Vec<OutSymbol>,
    pub relocations: Vec<OutReloc>,
}

pub fn check_signature(mut data: &[u8], sig: &FunctionSignature) -> Result<bool> {
    let sig_data = STANDARD.decode(&sig.signature)?;
    // println!(
    //     "\nChecking signature {} {} (size {})",
    //     sig.symbols[sig.symbol].name, sig.hash, sig.symbols[sig.symbol].size
    // );
    // for chunk in sig_data.chunks_exact(8) {
    //     let ins = u32::from_be_bytes(*array_ref!(chunk, 0, 4));
    //     let i = Ins::new(ins, 0);
    //     println!("=> {}", i.simplified());
    // }
    for chunk in sig_data.chunks_exact(8) {
        let ins = u32::from_be_bytes(*array_ref!(chunk, 0, 4));
        let pat = u32::from_be_bytes(*array_ref!(chunk, 4, 4));
        if (u32::from_be_bytes(*array_ref!(data, 0, 4)) & pat) != ins {
            return Ok(false);
        }
        data = &data[4..];
    }
    Ok(true)
}

pub fn parse_signatures(sig_str: &str) -> Result<Vec<FunctionSignature>> {
    Ok(serde_yaml::from_str(sig_str)?)
}

pub fn check_signatures_str(
    section: &ObjSection,
    addr: u32,
    sig_str: &str,
) -> Result<Option<FunctionSignature>> {
    check_signatures(section, addr, &parse_signatures(sig_str)?)
}

pub fn check_signatures(
    section: &ObjSection,
    addr: u32,
    signatures: &Vec<FunctionSignature>,
) -> Result<Option<FunctionSignature>> {
    let data = section.data_range(addr, 0)?;
    let mut name = None;
    for signature in signatures {
        if name.is_none() {
            name = Some(signature.symbols[signature.symbol as usize].name.clone());
        }
        if check_signature(data, signature)? {
            log::debug!(
                "Found {} @ {:#010X} (hash {})",
                signature.symbols[signature.symbol as usize].name,
                addr,
                signature.hash
            );
            return Ok(Some(signature.clone()));
        }
    }
    // if let Some(name) = name {
    //     log::debug!("Didn't find {} @ {:#010X}", name, addr);
    // }
    Ok(None)
}

pub fn apply_symbol(
    obj: &mut ObjInfo,
    target: SectionAddress,
    sig_symbol: &OutSymbol,
) -> Result<SymbolIndex> {
    let mut target_section_index =
        if target.section == SectionIndex::MAX { None } else { Some(target.section) };
    if let Some(target_section_index) = target_section_index {
        let target_section = &mut obj.sections[target_section_index];
        if !target_section.section_known {
            if let Some(section_name) = &sig_symbol.section {
                target_section.rename(section_name.clone())?;
            }
        }
    }
    if sig_symbol.kind == ObjSymbolKind::Unknown
        && (sig_symbol.name.starts_with("_f_") || sig_symbol.name.starts_with("_SDA"))
    {
        // Hack to mark linker generated symbols as ABS
        target_section_index = None;
    }
    let demangled_name = demangle(&sig_symbol.name, &DemangleOptions::default());
    let target_symbol_idx = obj.add_symbol(
        ObjSymbol {
            name: sig_symbol.name.clone(),
            demangled_name,
            address: target.address as u64,
            section: target_section_index,
            size: sig_symbol.size as u64,
            size_known: sig_symbol.size > 0 || sig_symbol.kind == ObjSymbolKind::Unknown,
            flags: sig_symbol.flags,
            kind: sig_symbol.kind,
            ..Default::default()
        },
        false,
    )?;
    Ok(target_symbol_idx)
}

pub fn apply_signature(
    obj: &mut ObjInfo,
    addr: SectionAddress,
    signature: &FunctionSignature,
) -> Result<()> {
    let in_symbol = &signature.symbols[signature.symbol as usize];
    let symbol_idx = apply_symbol(obj, addr, in_symbol)?;
    let mut tracker = Tracker::new(obj);
    for reloc in &signature.relocations {
        tracker.known_relocations.insert(addr + reloc.offset);
    }
    tracker.process_function(obj, &obj.symbols[symbol_idx])?;
    for (&reloc_addr, reloc) in &tracker.relocations {
        if reloc_addr < addr || reloc_addr >= addr + in_symbol.size {
            continue;
        }
        let offset = reloc_addr.address - addr.address;
        let sig_reloc = match signature.relocations.iter().find(|r| r.offset == offset) {
            Some(reloc) => reloc,
            None => continue,
        };
        let target = match (reloc, sig_reloc.kind) {
            (&Relocation::Absolute(RelocationTarget::Address(addr)), ObjRelocKind::Absolute)
            | (&Relocation::Hi(RelocationTarget::Address(addr)), ObjRelocKind::PpcAddr16Hi)
            | (&Relocation::Ha(RelocationTarget::Address(addr)), ObjRelocKind::PpcAddr16Ha)
            | (&Relocation::Lo(RelocationTarget::Address(addr)), ObjRelocKind::PpcAddr16Lo)
            | (&Relocation::Rel24(RelocationTarget::Address(addr)), ObjRelocKind::PpcRel24)
            | (&Relocation::Rel14(RelocationTarget::Address(addr)), ObjRelocKind::PpcRel14)
            | (&Relocation::Sda21(RelocationTarget::Address(addr)), ObjRelocKind::PpcEmbSda21) => {
                SectionAddress::new(
                    addr.section,
                    (addr.address as i64 - sig_reloc.addend as i64) as u32,
                )
            }
            _ => bail!("Relocation mismatch: {:?} != {:?}", reloc, sig_reloc.kind),
        };
        let sig_symbol = &signature.symbols[sig_reloc.symbol as usize];
        // log::info!("Processing relocation {:#010X} {:?} -> {:#010X} {:?}", reloc_addr, reloc, target, sig_symbol);
        let target_symbol_idx = apply_symbol(obj, target, sig_symbol)?;
        let obj_reloc = ObjReloc {
            kind: sig_reloc.kind,
            target_symbol: target_symbol_idx,
            addend: sig_reloc.addend as i64,
            module: None,
        };
        // log::info!("Applying relocation {:#010X?}", obj_reloc);
        obj.sections[addr.section].relocations.insert(reloc_addr.address, obj_reloc)?;
    }
    for reloc in &signature.relocations {
        let addr = addr + reloc.offset;
        if !tracker.relocations.contains_key(&addr) {
            let sig_symbol = &signature.symbols[reloc.symbol as usize];
            bail!("Missing relocation @ {:#010X}: {:?} -> {:?}", addr, reloc, sig_symbol);
        }
    }
    Ok(())
}

pub fn compare_signature(existing: &mut FunctionSignature, new: &FunctionSignature) -> Result<()> {
    ensure!(
        existing.symbols.len() == new.symbols.len(),
        "Mismatched symbol count: {} != {}\n{:?}\n{:?}",
        new.symbols.len(),
        existing.symbols.len(),
        new.symbols,
        existing.symbols,
    );
    ensure!(
        existing.relocations.len() == new.relocations.len(),
        "Mismatched relocation count: {} != {}",
        new.relocations.len(),
        existing.relocations.len()
    );
    for (idx, (a, b)) in existing.symbols.iter_mut().zip(&new.symbols).enumerate() {
        if a != b {
            let same_name = a.name == b.name || a.name.is_empty();
            let same_core = a.size == b.size && a.kind == b.kind;

            if same_name && same_core && a.section != b.section {
                // Section mismatch only — clear section.
                log::debug!("Clearing section for {:?} ({:?} != {:?})", a.name, a.section, b.section);
                a.section = None;
            } else if a.name != b.name && !a.name.is_empty() && same_core && a.flags == b.flags {
                // Name-only mismatch with same structure — compiler-generated label ($L*, @, _$E*).
                log::debug!("Clearing name for symbol {idx} ({:?} != {:?})", a.name, b.name);
                a.name = String::new();
                if a.section != b.section {
                    a.section = None;
                }
            } else if a.name.is_empty() || a.name.starts_with('@') {
                // Already cleared or COMDAT section symbol — ignore.
            } else {
                log::error!("Symbol {} mismatch: {:?} != {:?}", idx, a, b);
            }
        }
    }
    for (a, b) in existing.relocations.iter().zip(&new.relocations) {
        if a != b {
            log::error!("Relocation {} mismatch: {:?} != {:?}", a.offset, a, b);
        }
    }
    Ok(())
}

/// Check a byte-level x86 signature against `data`.
///
/// The signature blob is a sequence of `(value, mask)` byte pairs: a byte
/// matches if `(data[i] & mask) == value`.  Relocatable bytes have mask=0.
/// Check a byte-level x86 signature against `data`.
///
/// If `fn_size` is `Some`, reject the match unless the signature's expected
/// size equals `fn_size`.  This prevents a short signature (e.g. 6 bytes)
/// from matching a longer function that happens to start with the same bytes.
pub fn check_signature_x86(
    data: &[u8],
    sig: &FunctionSignature,
    fn_size: Option<u32>,
) -> Result<bool> {
    let sig_data = STANDARD.decode(&sig.signature)?;
    let sig_size = sig_data.len() / 2;
    if sig_data.len() % 2 != 0 || data.len() < sig_size {
        return Ok(false);
    }
    // If we know the function's actual size, require it to match the signature.
    if let Some(sz) = fn_size {
        if sz as usize != sig_size {
            return Ok(false);
        }
    }
    // Count unmasked (actually compared) bytes — reject signatures that are
    // too weak to be reliable (e.g. short thunks where most bytes are relocations).
    // Require at least 8 concrete bytes (~2-3 instructions worth).
    let unmasked = sig_data.chunks_exact(2).filter(|c| c[1] != 0).count();
    if unmasked < 8 {
        return Ok(false);
    }
    for (i, chunk) in sig_data.chunks_exact(2).enumerate() {
        let value = chunk[0];
        let mask = chunk[1];
        if data[i] & mask != value & mask {
            return Ok(false);
        }
    }
    Ok(true)
}

/// Check a list of x86 byte-level signatures against the bytes at `addr` in
/// `section`.  If `fn_size` is `Some`, only signatures whose size matches
/// exactly will be considered.
pub fn check_signatures_x86(
    section: &ObjSection,
    addr: u32,
    signatures: &[FunctionSignature],
    fn_size: Option<u32>,
) -> Result<Option<FunctionSignature>> {
    let data = section.data_range(addr, 0)?;
    for sig in signatures {
        if check_signature_x86(data, sig, fn_size)? {
            log::debug!(
                "Found x86 {} @ {:#010X} (hash {})",
                sig.symbols[sig.symbol as usize].name,
                addr,
                sig.hash,
            );
            return Ok(Some(sig.clone()));
        }
    }
    Ok(None)
}

/// Generate a byte-level x86 signature from a COFF/PE object file.
///
/// Loads the file via `process_coff`, runs `analyze_x86_functions` to populate
/// x86 relocations, then encodes each byte of the target function as a
/// `(value, mask)` pair where mask=0x00 for bytes covered by a relocation.
/// Apply an x86 signature at `addr`: rename the matched symbol, set its
/// size/flags, and rename any callees identified by the signature's relocation
/// table using the x86 relocations already present in the object
/// (populated by `analyze_x86_functions`).
pub fn apply_signature_x86(
    obj: &mut ObjInfo,
    addr: SectionAddress,
    sig: &FunctionSignature,
) -> Result<()> {
    let in_symbol = &sig.symbols[sig.symbol as usize];
    let sym_idx = apply_symbol(obj, addr, in_symbol)?;
    // Don't trust signature sizes in a PE — the linker layout may differ from
    // the .obj the signature was generated from.  Let the split system derive
    // sizes from function-entry gaps instead.
    {
        let sym = obj.symbols[sym_idx].clone();
        obj.symbols.replace(sym_idx, ObjSymbol { size: 0, size_known: false, ..sym })?;
    }

    for sig_reloc in &sig.relocations {
        let reloc_va = addr.address + sig_reloc.offset;
        let (target_sym_idx, addend) = {
            let section = &obj.sections[addr.section];
            let Some(reloc) = section.relocations.at(reloc_va) else { continue };
            (reloc.target_symbol, reloc.addend)
        };
        let sig_symbol = &sig.symbols[sig_reloc.symbol as usize];
        // Skip auto-generated callee names from .obj analysis — they are
        // meaningless in the PE context.
        if sig_symbol.name.starts_with("fn_") {
            continue;
        }
        let target_va = (obj.symbols[target_sym_idx].address as i64 + addend) as u32;
        let Some(target_sec) = obj.symbols[target_sym_idx].section else { continue };
        let callee_idx = apply_symbol(obj, SectionAddress::new(target_sec, target_va), sig_symbol)?;
        // Same: clear size_known for callees.
        let callee = obj.symbols[callee_idx].clone();
        obj.symbols.replace(callee_idx, ObjSymbol { size: 0, size_known: false, ..callee })?;
    }
    Ok(())
}

/// Build a signature for a specific function symbol (by index) from an already-analyzed [`ObjInfo`].
fn build_x86_signature(obj: &ObjInfo, sym_idx_in: SymbolIndex) -> Result<FunctionSignature> {
    let symbol = &obj.symbols[sym_idx_in];
    let symbol_name = symbol.name.clone();

    if !symbol.size_known || symbol.size == 0 {
        bail!("Symbol '{symbol_name}' has unknown size — run analysis first or set size manually");
    }

    let section_idx = match symbol.section {
            Some(idx) => idx,
            None => bail!("Symbol '{symbol_name}' has no section"),
        };
        let section = &obj.sections[section_idx];

        let sym_start = (symbol.address - section.address) as usize;
        let sym_end = sym_start + symbol.size as usize;
        let fn_bytes = section
            .data
            .get(sym_start..sym_end)
            .ok_or_else(|| anyhow!("Symbol '{symbol_name}' out of section bounds"))?;

        let mut out_symbols: Vec<OutSymbol> = Vec::new();
        let mut out_relocs: Vec<OutReloc> = Vec::new();
        let mut symbol_map: BTreeMap<SymbolIndex, u32> = BTreeMap::new();

        let sym_idx = out_symbols.len() as u32;
        out_symbols.push(OutSymbol {
            kind: symbol.kind,
            name: symbol.name.clone(),
            size: symbol.size as u32,
            flags: symbol.flags,
            section: Some(section.name.clone()),
        });

        // Build a mask array: 0xFF for fixed bytes, 0x00 for reloc-covered bytes.
        let mut masks = vec![0xFFu8; fn_bytes.len()];
        for (reloc_addr, reloc) in section.relocations.iter() {
            let offset = reloc_addr as i64 - symbol.address as i64;
            if offset < 0 || offset as usize >= fn_bytes.len() {
                continue;
            }
            let offset = offset as usize;
            let reloc_len = match reloc.kind {
                ObjRelocKind::X86Rel32 | ObjRelocKind::X86Abs32 | ObjRelocKind::Absolute => 4,
                _ => 4,
            };
            for b in &mut masks[offset..offset + reloc_len.min(fn_bytes.len() - offset)] {
                *b = 0x00;
            }

            let target = &obj.symbols[reloc.target_symbol];
            let symbol_idx = match symbol_map.entry(reloc.target_symbol) {
                btree_map::Entry::Vacant(e) => {
                    let idx = out_symbols.len() as u32;
                    e.insert(idx);
                    out_symbols.push(OutSymbol {
                        kind: target.kind,
                        name: target.name.clone(),
                        size: if target.kind == ObjSymbolKind::Function { 0 } else { target.size as u32 },
                        flags: target.flags,
                        section: target
                            .section
                            .and_then(|i| obj.sections.get(i))
                            .map(|s| s.name.clone()),
                    });
                    idx
                }
                btree_map::Entry::Occupied(e) => *e.get(),
            };
            out_relocs.push(OutReloc {
                offset: offset as u32,
                kind: reloc.kind,
                symbol: symbol_idx,
                addend: reloc.addend as i32,
            });
        }

        // Encode as (value & mask, mask) byte pairs.
        let mut encoded_bytes = Vec::with_capacity(fn_bytes.len() * 2);
        for (&byte, &mask) in fn_bytes.iter().zip(&masks) {
            encoded_bytes.push(byte & mask);
            encoded_bytes.push(mask);
        }

        let encoded = STANDARD.encode(&encoded_bytes);
        let mut hasher = Sha1::new();
        hasher.update(&encoded_bytes);
        let hash = hasher.finalize();
        let mut hash_buf = [0u8; 40];
        let hash_str = base16ct::lower::encode_str(&hash, &mut hash_buf)
            .map_err(|e| anyhow!("Failed to encode hash: {e}"))?;

    Ok(FunctionSignature {
        symbol: sym_idx,
        hash: hash_str.to_string(),
        signature: encoded,
        symbols: out_symbols,
        relocations: out_relocs,
    })
}

/// Load and analyze a COFF object from raw bytes, then generate signatures for every
/// function symbol with a known non-zero size.  Returns `(symbol_name, signature)` pairs.
pub fn generate_all_signatures_x86(
    data: &[u8],
    source_name: &str,
) -> Result<Vec<(String, FunctionSignature)>> {
    let (mut obj, image_base) = process_coff(data, source_name)?;
    if let Some(base) = image_base {
        apply_base_relocations(&mut obj, base)?;
    }
    let size_data = analyze_x86_functions(&mut obj)?;
    crate::analysis::x86::compute_x86_function_sizes(&mut obj, size_data)?;

    let candidates: Vec<(SymbolIndex, String)> = obj
        .symbols
        .by_kind(ObjSymbolKind::Function)
        .filter(|(_, s)| s.size_known && s.size > 0 && s.section.is_some())
        .map(|(idx, s)| (idx, s.name.clone()))
        .collect();

    let mut out = Vec::new();
    for (idx, name) in candidates {
        match build_x86_signature(&obj, idx) {
            Ok(sig) => out.push((name, sig)),
            Err(e) => log::warn!("  {name}: {e}"),
        }
    }
    Ok(out)
}

pub fn generate_signature_x86(
    path: &Utf8NativePath,
    symbol_name: &str,
) -> Result<Option<FunctionSignature>> {
    let data = std::fs::read(path)
        .with_context(|| format!("Failed to read '{path}'"))?;
    let (mut obj, image_base) = process_coff(&data, symbol_name)
        .with_context(|| format!("Failed to parse COFF '{path}'"))?;

    if let Some(base) = image_base {
        apply_base_relocations(&mut obj, base)?;
    }
    let size_data = analyze_x86_functions(&mut obj)?;
    crate::analysis::x86::compute_x86_function_sizes(&mut obj, size_data)?;

    // Find the matching symbol by name, preferring entries with known size.
    let found = obj
        .symbols
        .by_kind(ObjSymbolKind::Function)
        .find(|(_, s)| s.name == symbol_name && s.size_known && s.size > 0 && s.section.is_some());
    match found {
        Some((idx, _)) => build_x86_signature(&obj, idx).map(Some),
        None => {
            // Check if it exists at all (but lacks size info).
            let exists = obj
                .symbols
                .by_kind(ObjSymbolKind::Function)
                .any(|(_, s)| s.name == symbol_name);
            if exists {
                bail!(
                    "Symbol '{symbol_name}' has unknown size — run analysis first or set size manually"
                );
            }
            log::warn!("Symbol '{symbol_name}' not found in '{path}'");
            Ok(None)
        }
    }
}

pub fn generate_signature(
    path: &Utf8NativePath,
    symbol_name: &str,
) -> Result<Option<FunctionSignature>> {
    let mut out_symbols: Vec<OutSymbol> = Vec::new();
    let mut out_relocs: Vec<OutReloc> = Vec::new();
    let mut symbol_map: BTreeMap<SymbolIndex, u32> = BTreeMap::new();

    let mut obj = process_elf(path)?;
    if obj.kind == ObjKind::Executable
        && (obj.sda2_base.is_none()
            || obj.sda_base.is_none()
            || obj.stack_address.is_none()
            || obj.stack_end.is_none()
            || obj.db_stack_addr.is_none())
    {
        log::warn!(
            "Failed to locate all abs symbols {:#010X?} {:#010X?} {:#010X?} {:#010X?} {:#010X?} {:#010X?} {:#010X?}",
            obj.sda2_base,
            obj.sda_base,
            obj.stack_address,
            obj.stack_end,
            obj.db_stack_addr,
            obj.arena_hi,
            obj.arena_lo
        );
        return Ok(None);
    }
    let mut tracker = Tracker::new(&obj);
    // tracker.ignore_addresses.insert(0x80004000);
    for (_, symbol) in obj.symbols.by_kind(ObjSymbolKind::Function) {
        if symbol.name != symbol_name && symbol.name != symbol_name.replace("TRK", "TRK_") {
            continue;
        }
        tracker.process_function(&obj, symbol)?;
    }
    tracker.apply(&mut obj, true)?; // true
    for (_, symbol) in obj.symbols.by_kind(ObjSymbolKind::Function) {
        if symbol.name != symbol_name && symbol.name != symbol_name.replace("TRK", "TRK_") {
            continue;
        }
        let section_idx = symbol.section.unwrap();
        let section = &obj.sections[section_idx];
        // let out_symbol_idx = out_symbols.len();
        out_symbols.push(OutSymbol {
            kind: symbol.kind,
            name: symbol.name.clone(),
            size: symbol.size as u32,
            flags: symbol.flags,
            section: Some(section.name.clone()),
        });
        // println!(
        //     "Building signature for {} ({:#010X}-{:#010X})",
        //     symbol.name,
        //     symbol.address,
        //     symbol.address + symbol.size
        // );
        let mut instructions = section.data[(symbol.address - section.address) as usize
            ..(symbol.address - section.address + symbol.size) as usize]
            .chunks_exact(4)
            .map(|c| (u32::from_be_bytes(c.try_into().unwrap()), !0u32))
            .collect::<Vec<(u32, u32)>>();
        for (idx, (ins, pat)) in instructions.iter_mut().enumerate() {
            let addr = (symbol.address as usize + idx * 4) as u32;
            if let Some(reloc) = section.relocations.at(addr) {
                let symbol_idx = match symbol_map.entry(reloc.target_symbol) {
                    btree_map::Entry::Vacant(e) => {
                        let target = &obj.symbols[reloc.target_symbol];
                        let symbol_idx = out_symbols.len() as u32;
                        e.insert(symbol_idx);
                        out_symbols.push(OutSymbol {
                            kind: target.kind,
                            name: target.name.clone(),
                            size: if target.kind == ObjSymbolKind::Function {
                                0
                            } else {
                                target.size as u32
                            },
                            flags: target.flags,
                            section: target
                                .section
                                .and_then(|idx| obj.sections.get(idx))
                                .map(|section| section.name.clone()),
                        });
                        symbol_idx
                    }
                    btree_map::Entry::Occupied(e) => *e.get(),
                };
                match reloc.kind {
                    ObjRelocKind::Absolute => {
                        *ins = 0;
                        *pat = 0;
                    }
                    ObjRelocKind::PpcAddr16Hi
                    | ObjRelocKind::PpcAddr16Ha
                    | ObjRelocKind::PpcAddr16Lo => {
                        *ins &= !0xFFFF;
                        *pat = !0xFFFF;
                    }
                    ObjRelocKind::PpcRel24 => {
                        *ins &= !0x3FFFFFC;
                        *pat = !0x3FFFFFC;
                    }
                    ObjRelocKind::PpcRel14 => {
                        *ins &= !0xFFFC;
                        *pat = !0xFFFC;
                    }
                    ObjRelocKind::PpcEmbSda21 => {
                        *ins &= !0x1FFFFF;
                        *pat = !0x1FFFFF;
                    }
                    ObjRelocKind::X86Abs32 | ObjRelocKind::X86Rel32 => {
                        *ins = 0;
                        *pat = 0;
                    }
                }
                out_relocs.push(OutReloc {
                    offset: addr - (symbol.address as u32),
                    kind: reloc.kind,
                    symbol: symbol_idx,
                    addend: reloc.addend as i32,
                });
            }
        }

        let mut data = vec![0u8; instructions.len() * 8];
        for (idx, &(ins, pat)) in instructions.iter().enumerate() {
            data[idx * 8..idx * 8 + 4].copy_from_slice(&ins.to_be_bytes());
            data[idx * 8 + 4..idx * 8 + 8].copy_from_slice(&pat.to_be_bytes());
        }

        let encoded = STANDARD.encode(&data);
        let mut hasher = Sha1::new();
        hasher.update(&data);
        let hash = hasher.finalize();
        let mut hash_buf = [0u8; 40];
        let hash_str = base16ct::lower::encode_str(&hash, &mut hash_buf)
            .map_err(|e| anyhow!("Failed to encode hash: {e}"))?;
        return Ok(Some(FunctionSignature {
            symbol: 0,
            hash: hash_str.to_string(),
            signature: encoded,
            symbols: out_symbols,
            relocations: out_relocs,
        }));
    }
    Ok(None)
}
