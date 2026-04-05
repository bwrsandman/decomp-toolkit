use std::collections::HashMap;

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
    // Build a fast VA-to-section lookup for pointer validation.
    let sections: Vec<(u64, u64, ObjSectionKind)> = obj
        .sections
        .iter()
        .map(|(_, s)| (s.address, s.address + s.size, s.kind))
        .collect();

    let va_in_any_section = |va: u32| -> bool {
        sections.iter().any(|&(start, end, _)| va as u64 >= start && (va as u64) < end)
    };
    let va_in_code = |va: u32| -> bool {
        sections
            .iter()
            .any(|&(start, end, kind)| va as u64 >= start && (va as u64) < end && kind == ObjSectionKind::Code)
    };
    let va_in_data = |va: u32| -> bool {
        sections.iter().any(|&(start, end, kind)| {
            va as u64 >= start
                && (va as u64) < end
                && !matches!(kind, ObjSectionKind::Code | ObjSectionKind::Bss)
        })
    };

    // Snapshot section data for scanning (avoids borrow issues while mutating obj).
    let data_sections: Vec<(usize, u64, Vec<u8>)> = obj
        .sections
        .iter()
        .filter(|(_, s)| {
            !matches!(s.kind, ObjSectionKind::Code | ObjSectionKind::Bss) && !s.data.is_empty()
        })
        .map(|(idx, s)| (idx as usize, s.address, s.data.clone()))
        .collect();

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
            // pVFTable must point into a data section (type_info vtable lives in .rdata).
            let pvf = read_u32_le(data, off).unwrap();
            // spare must be zero.
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
    //   [va+4]  DWORD → code section (second virtual function, optional)
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
                // The next dword should be the first vfunc — must point into code.
                let first_vfunc = read_u32_le(data, off + 4).unwrap_or(0);
                if va_in_code(first_vfunc) || va_in_any_section(first_vfunc) {
                    // vtable starts 4 bytes after the COL pointer.
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
        // Skip if a symbol already exists here.
        if obj.symbols.at_section_address(sec_idx as u32, *va).next().is_some() {
            continue;
        }
        // Symbol name: ??_R0?AVFoo@@8  (drop leading dot, append 8)
        let inner = rtti_name.strip_prefix('.').unwrap_or(rtti_name);
        let sym_name = format!("??_R0{}@8", inner);
        // Size: 8 (header) + name string length + 1 (null)
        let name_len = rtti_name.len() + 1;
        let size = 8 + name_len;
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
        // Symbol name: ??_R4Foo@@6B@  (strip .?AV prefix, append 6B@)
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
    Ok(())
}

/// Generate the MSVC-standard symbol name for an RTTICompleteObjectLocator.
/// Input: RTTI name e.g. `.?AVFoo@@`  → output: `??_R4Foo@@6B@`
fn rtti_col_symbol(rtti_name: &str) -> String {
    // Strip leading '.', '?', 'A', type char (V/U/W/T...) to get "Foo@@".
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
    // Skip the type character (V = class, U = struct, W = enum, etc.)
    if s.len() > 1 && s.as_bytes()[0].is_ascii_alphabetic() {
        &s[1..]
    } else {
        s
    }
}
