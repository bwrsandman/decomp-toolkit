use std::collections::{HashMap, HashSet};

use anyhow::Result;
use flagset::Flags as _;

use crate::obj::{
    ObjInfo, ObjSectionKind, ObjSymbol, ObjSymbolFlagSet, ObjSymbolFlags, ObjSymbolKind,
};

/// Read a little-endian u32 from `data` at byte offset `off`.
/// Returns `None` if out of bounds.
#[inline]
fn read_u32_le(data: &[u8], off: usize) -> Option<u32> {
    data.get(off..off + 4).map(|b| u32::from_le_bytes(b.try_into().unwrap()))
}

/// Returns the null-terminated C string starting at `data[off..]`, or `None`
/// if there is no null terminator within the slice.
fn cstr_at(data: &[u8], off: usize) -> Option<&str> {
    let slice = data.get(off..)?;
    let end = slice.iter().position(|&b| b == 0)?;
    std::str::from_utf8(&slice[..end]).ok()
}

/// Detect MSVC RTTI structures in `.rdata` / `.data` sections and add symbols
/// for TypeDescriptors, RTTICompleteObjectLocators, and vtables.
///
/// Detection chain:
///   1. TypeDescriptors: structures with `spare=0` followed by an MSVC RTTI
///      name string starting with `.?A`.
///   2. RTTICompleteObjectLocators (COL): 20-byte structures whose
///      `pTypeDescriptor` field points to a known TypeDescriptor.
///   3. Vtables: locations in .rdata where `ptr[-1]` points to a known COL
///      and `ptr[0]` points into a code section.
pub fn detect_rtti(obj: &mut ObjInfo) -> Result<()> {
    // ── Fast VA lookup tables ────────────────────────────────────────────────
    //
    // Build a sorted (start, end, kind) array so VA-kind queries are O(log n)
    // instead of O(n_sections).  These closures are called millions of times
    // (once per 4-byte dword during section sweeps), so the constant matters.

    let mut sorted_sections: Vec<(u32, u32, ObjSectionKind)> = obj
        .sections
        .iter()
        .map(|(_, s)| (s.address as u32, (s.address + s.size) as u32, s.kind))
        .collect();
    sorted_sections.sort_unstable_by_key(|&(start, _, _)| start);

    // Returns the ObjSectionKind of the section containing `va`, or None.
    let va_kind = |va: u32| -> Option<ObjSectionKind> {
        // Find the last section whose start ≤ va.
        let idx = sorted_sections.partition_point(|&(start, _, _)| start <= va);
        if idx == 0 {
            return None;
        }
        let (_, end, kind) = sorted_sections[idx - 1];
        if va < end { Some(kind) } else { None }
    };

    let va_in_code = |va: u32| va_kind(va) == Some(ObjSectionKind::Code);
    let va_in_data = |va: u32| {
        matches!(va_kind(va), Some(k) if !matches!(k, ObjSectionKind::Code | ObjSectionKind::Bss))
    };
    let va_in_any_section = |va: u32| va_kind(va).is_some();

    // Snapshot section data for scanning (avoids borrow issues while mutating obj).
    let data_sections: Vec<(usize, u64, Vec<u8>)> = obj
        .sections
        .iter()
        .filter(|(_, s)| {
            !matches!(s.kind, ObjSectionKind::Code | ObjSectionKind::Bss) && !s.data.is_empty()
        })
        .map(|(idx, s)| (idx as usize, s.address, s.data.clone()))
        .collect();

    // Build a sorted (base, end, &data) array for O(log n) read_at_va lookups.
    // These are called for every vtable slot and every CHD base-class pointer.
    let mut sorted_data: Vec<(u32, u32, &[u8])> = data_sections
        .iter()
        .map(|(_, base, data)| (*base as u32, *base as u32 + data.len() as u32, data.as_slice()))
        .collect();
    sorted_data.sort_unstable_by_key(|&(base, _, _)| base);

    // Read a u32 from data sections by virtual address (O(log n_data_sections)).
    let read_at_va = |va: u32| -> Option<u32> {
        let idx = sorted_data.partition_point(|&(base, _, _)| base <= va);
        if idx == 0 {
            return None;
        }
        let (base, end, data) = sorted_data[idx - 1];
        if va >= end {
            return None;
        }
        read_u32_le(data, (va - base) as usize)
    };

    // ── Step 1: Find TypeDescriptors ────────────────────────────────────────
    // Layout (x86 32-bit LE):
    //   +0x00  DWORD pVFTable  (pointer to type_info vtable, must be a valid data VA)
    //   +0x04  DWORD spare = 0
    //   +0x08  char  name[]    starts with ".?A" and ends with "@@\0"
    //
    // Key: VA of TypeDescriptor → (section_idx, parsed class name fragment)
    let mut type_descriptors: HashMap<u32, String> = HashMap::new();

    for (_, base, data) in &data_sections {
        let base = *base as u32;
        let mut off = 0usize;
        while off + 12 <= data.len() {
            let pvf = read_u32_le(data, off).unwrap();
            let spare = read_u32_le(data, off + 4).unwrap();
            if spare == 0 && va_in_data(pvf) {
                if let Some(name) = cstr_at(data, off + 8) {
                    if name.starts_with(".?A") && name.ends_with("@@") {
                        let va = base + off as u32;
                        type_descriptors.insert(va, name.to_string());
                    }
                }
            }
            off += 4;
        }
    }

    log::debug!("RTTI: found {} TypeDescriptor(s)", type_descriptors.len());

    // ── Step 2: Find RTTICompleteObjectLocators ─────────────────────────────
    // Layout:
    //   +0x00  DWORD signature = 0
    //   +0x04  DWORD offset    (offset of sub-object within complete object)
    //   +0x08  DWORD cdOffset
    //   +0x0C  DWORD pTypeDescriptor → known TypeDescriptor
    //   +0x10  DWORD pClassDescriptor → valid data VA
    //
    // Key: VA of COL → rtti_name string
    let mut cols: HashMap<u32, String> = HashMap::new();

    for (_, base, data) in &data_sections {
        let base = *base as u32;
        let mut off = 0usize;
        while off + 20 <= data.len() {
            let sig = read_u32_le(data, off).unwrap();
            if sig == 0 {
                let p_td = read_u32_le(data, off + 12).unwrap();
                let p_chd = read_u32_le(data, off + 16).unwrap();
                if let Some(rtti_name) = type_descriptors.get(&p_td) {
                    if va_in_data(p_chd) || p_chd == 0 {
                        let va = base + off as u32;
                        cols.insert(va, rtti_name.clone());
                    }
                }
            }
            off += 4;
        }
    }

    log::debug!("RTTI: found {} RTTICompleteObjectLocator(s)", cols.len());

    // ── Step 3: Find vtables ────────────────────────────────────────────────
    // A vtable looks like:
    //   [va-4]  DWORD → known COL
    //   [va+0]  DWORD → code section (first virtual function)
    //
    // We scan .rdata for a pointer to a COL, then check that the following
    // dword points into code.
    let mut vtables: Vec<(u32, String)> = Vec::new();

    for (_, base, data) in &data_sections {
        let base = *base as u32;
        let mut off = 0usize;
        while off + 8 <= data.len() {
            let p_col = read_u32_le(data, off).unwrap();
            if let Some(rtti_name) = cols.get(&p_col) {
                let first_vfunc = read_u32_le(data, off + 4).unwrap_or(0);
                if va_in_code(first_vfunc) || va_in_any_section(first_vfunc) {
                    let vtable_va = base + off as u32 + 4;
                    vtables.push((vtable_va, rtti_name.clone()));
                }
            }
            off += 4;
        }
    }

    log::debug!("RTTI: found {} vtable(s)", vtables.len());

    // ── Step 4: Add symbols ─────────────────────────────────────────────────
    let mut added = 0u32;

    // Helper: look up section index for a VA.
    let section_for = |va: u32| -> Option<usize> {
        obj.sections
            .iter()
            .find(|(_, s)| va as u64 >= s.address && (va as u64) < s.address + s.size)
            .map(|(idx, _)| idx as usize)
    };

    // TypeDescriptors
    for (va, rtti_name) in &type_descriptors {
        let Some(sec_idx) = section_for(*va) else { continue };
        if obj.symbols.at_section_address(sec_idx as u32, *va).next().is_some() {
            continue;
        }
        let inner = rtti_name.strip_prefix('.').unwrap_or(rtti_name);
        let sym_name = format!("??_R0{}@8", inner);
        let size = 8 + rtti_name.len() + 1;
        obj.symbols.add_direct(ObjSymbol {
            name: sym_name,
            address: *va as u64,
            section: Some(sec_idx as u32),
            size: size as u64,
            size_known: true,
            kind: ObjSymbolKind::Object,
            flags: ObjSymbolFlagSet(ObjSymbolFlags::none()),
            ..Default::default()
        })?;
        added += 1;
    }

    // RTTICompleteObjectLocators
    for (va, rtti_name) in &cols {
        let Some(sec_idx) = section_for(*va) else { continue };
        if obj.symbols.at_section_address(sec_idx as u32, *va).next().is_some() {
            continue;
        }
        let col_name = rtti_col_symbol(rtti_name);
        obj.symbols.add_direct(ObjSymbol {
            name: col_name,
            address: *va as u64,
            section: Some(sec_idx as u32),
            size: 20,
            size_known: true,
            kind: ObjSymbolKind::Object,
            flags: ObjSymbolFlagSet(ObjSymbolFlags::none()),
            ..Default::default()
        })?;
        added += 1;
    }

    // Vtables
    for (va, rtti_name) in &vtables {
        let Some(sec_idx) = section_for(*va) else { continue };
        if obj.symbols.at_section_address(sec_idx as u32, *va).next().is_some() {
            continue;
        }
        let vt_name = rtti_vtable_symbol(rtti_name);
        obj.symbols.add_direct(ObjSymbol {
            name: vt_name,
            address: *va as u64,
            section: Some(sec_idx as u32),
            kind: ObjSymbolKind::Object,
            flags: ObjSymbolFlagSet(ObjSymbolFlags::none()),
            ..Default::default()
        })?;
        added += 1;
    }

    if added > 0 {
        log::info!("RTTI: added {added} symbols ({} TypeDescriptors, {} COLs, {} vtables)",
            type_descriptors.len(), cols.len(), vtables.len());
    }

    // ── Step 5: Virtual function naming ──────────────────────────────────────
    //
    // For each vtable entry, determine which class first introduced that virtual
    // function slot and name the function accordingly:  `ClassName_vfuncN`.
    //
    // "Most base class" means the class that appears in the base-class list of
    // the greatest number of the other vtable owners of the same function.
    // This correctly attributes an unoverridden function to the class that
    // first declared it virtual, rather than to every derived class that
    // inherits the same pointer.

    // 5a. Parse RTTIClassHierarchyDescriptor for every COL.
    //
    // RTTICompleteObjectLocator layout (x86, MSVC):
    //   +0x0C  DWORD pTypeDescriptor
    //   +0x10  DWORD pClassDescriptor  ← RTTIClassHierarchyDescriptor*
    //
    // RTTIClassHierarchyDescriptor:
    //   +0x00  DWORD signature = 0
    //   +0x08  DWORD numBaseClasses
    //   +0x0C  DWORD pBaseClassArray   ← array of RTTIBaseClassDescriptor*
    //
    // RTTIBaseClassDescriptor:
    //   +0x00  DWORD pTypeDescriptor   ← identifies the base class
    //
    // Base-class array is DFS pre-order (most-derived first), so index 0
    // is the class itself; every subsequent entry is a (transitive) base.
    //
    // Result: class_inner_name → Vec of base class inner names (excl. self).
    let mut class_all_bases: HashMap<String, Vec<String>> = HashMap::new();

    for (col_va, rtti_name) in &cols {
        let this_class = class_inner(rtti_name).to_string();

        let p_chd = match read_at_va(col_va + 16) {
            Some(v) if va_in_data(v) => v,
            _ => continue,
        };
        if read_at_va(p_chd).unwrap_or(1) != 0 { continue; } // signature must be 0
        let num_bases = match read_at_va(p_chd + 8) {
            Some(n) if n > 0 && n <= 512 => n,
            _ => continue,
        };
        let p_base_array = match read_at_va(p_chd + 12) {
            Some(v) if va_in_data(v) => v,
            _ => continue,
        };

        let mut bases = Vec::new();
        for i in 0..num_bases {
            let p_bcd = match read_at_va(p_base_array + i * 4) {
                Some(v) if va_in_data(v) => v,
                _ => break,
            };
            let p_td = match read_at_va(p_bcd) {
                Some(v) => v,
                None => break,
            };
            if let Some(td_name) = type_descriptors.get(&p_td) {
                let base_inner = class_inner(td_name).to_string();
                if base_inner != this_class {
                    bases.push(base_inner);
                }
            }
        }
        class_all_bases.insert(this_class, bases);
    }

    log::debug!("RTTI: parsed class hierarchy for {} class(es)", class_all_bases.len());

    // Build a reverse map: base_class → set of classes that (directly or
    // transitively) derive from it.  This turns the O(k × bases_len) scoring
    // loop in step 5c from Vec linear scans into O(1) HashSet lookups.
    let mut is_base_of: HashMap<&str, HashSet<&str>> = HashMap::new();
    for (derived, bases) in &class_all_bases {
        for base in bases {
            is_base_of.entry(base.as_str()).or_default().insert(derived.as_str());
        }
    }

    // 5b. Scan each vtable to collect all (class, slot) appearances per function VA.
    let mut fn_to_vtable: HashMap<u32, Vec<(String, usize)>> = HashMap::new();

    for (vtable_va, rtti_name) in &vtables {
        let class_name = class_inner(rtti_name).to_string();
        let mut ptr = *vtable_va;
        let mut slot = 0usize;
        loop {
            let fn_va = match read_at_va(ptr) {
                Some(v) if va_in_code(v) => v,
                _ => break,
            };
            fn_to_vtable.entry(fn_va).or_default().push((class_name.clone(), slot));
            ptr += 4;
            slot += 1;
            if slot >= 512 { break; }
        }
    }

    log::debug!("RTTI: found {} unique virtual function(s) across all vtables", fn_to_vtable.len());

    // 5c. For each function VA, choose the most-base owner class.
    //
    // Score(cname) = number of other appearance-classes that list cname as a
    // base.  Using the pre-built `is_base_of` reverse map, each lookup is O(1)
    // instead of O(bases_len).
    let mut vfunc_to_name: Vec<(u32, String)> = Vec::new();
    let mut used_names: HashSet<String> = HashSet::new();

    for (fn_va, appearances) in &fn_to_vtable {
        if appearances.is_empty() { continue; }

        let (owner_class, owner_slot) = if appearances.len() == 1 {
            (appearances[0].0.clone(), appearances[0].1)
        } else {
            let best = appearances
                .iter()
                .max_by_key(|(cname, _)| {
                    // How many of the other appearance classes derive from cname?
                    let deriveds = is_base_of.get(cname.as_str());
                    appearances
                        .iter()
                        .filter(|(other, _)| {
                            other != cname
                                && deriveds.map_or(false, |s| s.contains(other.as_str()))
                        })
                        .count()
                })
                .unwrap();
            (best.0.clone(), best.1)
        };

        // Build a C-identifier-safe name from the mangled class fragment.
        // class_inner returns e.g. "Foo@@" or "Bar@ns@@"; strip trailing "@@"
        // and replace remaining "@" (namespace separators) with "_".
        let class_safe = owner_class
            .strip_suffix("@@")
            .unwrap_or(&owner_class)
            .replace('@', "_");
        let mut sym_name = format!("{class_safe}_vfunc{owner_slot}");

        // Disambiguate collisions (rare, multiple-inheritance vtables).
        if used_names.contains(&sym_name) {
            sym_name = format!("{class_safe}_vfunc{owner_slot}_{fn_va:#010X}");
        }
        used_names.insert(sym_name.clone());

        vfunc_to_name.push((*fn_va, sym_name));
    }

    // 5d. Apply symbols: replace auto-generated `fn_XXXX` names; preserve
    //     any symbol that has already been given a user-defined name.
    let mut vfunc_named = 0u32;

    for (fn_va, sym_name) in &vfunc_to_name {
        let Some(sec_idx) = section_for(*fn_va) else { continue };

        let existing = obj
            .symbols
            .at_section_address(sec_idx as u32, *fn_va)
            .find(|(_, s)| s.kind == ObjSymbolKind::Function)
            .map(|(idx, s)| (idx, s.name.starts_with("fn_"), s.clone()));

        match existing {
            Some((_, false, _)) => continue, // user-defined name — preserve
            Some((idx, true, existing_sym)) => {
                obj.symbols.replace(idx, ObjSymbol {
                    name: sym_name.clone(),
                    // Clear size_known: detect_rtti may add new function symbols
                    // after x86 analysis, invalidating the previously computed
                    // size caps.  The split system derives extents from entry gaps.
                    size: 0,
                    size_known: false,
                    ..existing_sym
                })?;
                vfunc_named += 1;
            }
            None => {
                obj.symbols.add_direct(ObjSymbol {
                    name: sym_name.clone(),
                    address: *fn_va as u64,
                    section: Some(sec_idx as u32),
                    kind: ObjSymbolKind::Function,
                    flags: ObjSymbolFlagSet(ObjSymbolFlags::none()),
                    ..Default::default()
                })?;
                vfunc_named += 1;
            }
        }
    }

    if vfunc_named > 0 {
        log::info!("RTTI: named {vfunc_named} virtual function(s)");
    }

    Ok(())
}

/// Generate the MSVC-standard symbol name for an RTTICompleteObjectLocator.
/// Input: RTTI name e.g. `.?AVFoo@@`  → output: `??_R4Foo@@6B@`
fn rtti_col_symbol(rtti_name: &str) -> String {
    let inner = class_inner(rtti_name);
    format!("??_R4{}6B@", inner)
}

/// Generate the MSVC-standard vtable symbol name.
/// Input: RTTI name e.g. `.?AVFoo@@`  → output: `??_7Foo@@6B@`
fn rtti_vtable_symbol(rtti_name: &str) -> String {
    let inner = class_inner(rtti_name);
    format!("??_7{}6B@", inner)
}

/// Extract the mangled class name fragment from an RTTI name.
/// `.?AVFoo@@` → `Foo@@`
/// `.?AVBar@ns@@` → `Bar@ns@@`
/// Falls back to the whole string if the expected prefix is absent.
fn class_inner(rtti_name: &str) -> &str {
    // Pattern: `.?A<type_char><name>@@`
    // Strip `.?A` (3 chars) + one type char (1 char) = 4 chars from the start.
    let s = rtti_name.strip_prefix('.').unwrap_or(rtti_name);
    let s = s.strip_prefix("?A").unwrap_or(s);
    if s.len() > 1 && s.as_bytes()[0].is_ascii_alphabetic() {
        &s[1..]
    } else {
        s
    }
}
