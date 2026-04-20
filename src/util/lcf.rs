use anyhow::Result;
use itertools::Itertools;
use typed_path::{Utf8NativePathBuf, Utf8UnixPath};

use crate::obj::{ObjInfo, ObjKind};

const LCF_TEMPLATE: &str = include_str!("../../assets/ldscript.lcf");
const LCF_PARTIAL_TEMPLATE: &str = include_str!("../../assets/ldscript_partial.lcf");

pub fn generate_ldscript(
    obj: &ObjInfo,
    template: Option<&str>,
    force_active: &[String],
) -> Result<String> {
    if obj.kind == ObjKind::Relocatable {
        return generate_ldscript_partial(obj, template, force_active);
    }

    let origin = obj.sections.iter().map(|(_, s)| s.address).min().unwrap();
    let stack_size = match (obj.stack_address, obj.stack_end) {
        (Some(stack_address), Some(stack_end)) => stack_address - stack_end,
        _ => 65535, // default
    };

    let section_defs = obj
        .sections
        .iter()
        .map(|(_, s)| format!("{} ALIGN({:#X}):{{}}", s.name, s.align))
        .join("\n        ");

    let mut force_files = Vec::with_capacity(obj.link_order.len());
    for unit in &obj.link_order {
        let obj_path = obj_path_for_unit(&unit.name);
        force_files.push(obj_path.file_name().unwrap().to_string());
    }

    let mut force_active = force_active.to_vec();
    for (_, symbol) in obj.symbols.iter() {
        if symbol.flags.is_exported() && symbol.flags.is_global() && !symbol.flags.is_no_write() {
            force_active.push(symbol.name.clone());
        }
    }

    // Hack to handle missing .sbss2 section... what's the proper way?
    let last_section_name = obj.sections.iter().next_back().unwrap().1.name.clone();
    let last_section_symbol = format!("_f_{}", last_section_name.trim_start_matches('.'));

    let out = template
        .unwrap_or(LCF_TEMPLATE)
        .replace("$ORIGIN", &format!("{origin:#X}"))
        .replace("$SECTIONS", &section_defs)
        .replace("$LAST_SECTION_SYMBOL", &last_section_symbol)
        .replace("$LAST_SECTION_NAME", &last_section_name)
        .replace("$STACKSIZE", &format!("{stack_size:#X}"))
        .replace("$FORCEACTIVE", &force_active.join("\n    "))
        .replace("$ARENAHI", &format!("{:#X}", obj.arena_hi.unwrap_or(0x81700000)));
    Ok(out)
}

pub fn generate_ldscript_partial(
    obj: &ObjInfo,
    template: Option<&str>,
    force_active: &[String],
) -> Result<String> {
    let mut section_defs = obj
        .sections
        .iter()
        .map(|(_, s)| {
            let inner = if s.name == ".data" { " *(.data) *(extabindex) *(extab) " } else { "" };
            format!("{} ALIGN({:#X}):{{{}}}", s.name, s.align, inner)
        })
        .join("\n        ");

    // Some RELs have no entry point (`.text` was stripped) so mwld requires at least an empty
    // `.init` section to be present in the linker script, for some reason.
    if obj.entry.is_none() {
        section_defs = format!(".init :{{}}\n        {section_defs}");
    }

    let mut force_files = Vec::with_capacity(obj.link_order.len());
    for unit in &obj.link_order {
        let obj_path = obj_path_for_unit(&unit.name);
        force_files.push(obj_path.file_name().unwrap().to_string());
    }

    let mut force_active = force_active.to_vec();
    for (_, symbol) in obj.symbols.iter() {
        if symbol.flags.is_exported() && symbol.flags.is_global() && !symbol.flags.is_no_write() {
            force_active.push(symbol.name.clone());
        }
    }

    let out = template
        .unwrap_or(LCF_PARTIAL_TEMPLATE)
        .replace("$SECTIONS", &section_defs)
        .replace("$FORCEACTIVE", &force_active.join("\n    "));
    Ok(out)
}

/// Sanitize a unit name into a filesystem- and build-system-safe path component.
/// Uses `_`-prefixed letter codes to encode characters that are special to ninja
/// (treats `$` as a variable sigil; quotes paths with `@`, `~`, etc. in rsp files)
/// or to shells (`?` glob wildcard). `_` is self-escaped as `__` to avoid collisions.
fn sanitize_unit_name(unit: &str) -> String {
    let mut out = String::with_capacity(unit.len() * 2);
    for c in unit.chars() {
        match c {
            '_' => out.push_str("__"),
            '$' => out.push_str("_d"),
            '?' => out.push_str("_q"),
            '@' => out.push_str("_a"),
            c => out.push(c),
        }
    }
    out
}

/// Truncate `stem` so that `stem + ext` fits within 255 bytes (Linux NAME_MAX).
/// When truncation is needed, appends a 64-bit FNV-1a hash of the full stem so
/// the result is unique even when two long names share the same prefix.
fn fit_filename(stem: String, ext: &str) -> String {
    const NAME_MAX: usize = 255;
    if stem.len() + ext.len() <= NAME_MAX {
        return stem;
    }
    // FNV-1a 64-bit of the full stem
    let mut hash: u64 = 0xcbf29ce484222325;
    for b in stem.bytes() {
        hash ^= b as u64;
        hash = hash.wrapping_mul(0x100000001b3);
    }
    let suffix = format!("_{hash:016x}");
    let max_stem = NAME_MAX - ext.len() - suffix.len();
    format!("{}{suffix}", &stem[..max_stem])
}

pub fn obj_path_for_unit(unit: &str) -> Utf8NativePathBuf {
    let stem = fit_filename(sanitize_unit_name(unit), ".o");
    Utf8UnixPath::new(&stem).with_encoding().with_extension("o")
}

pub fn asm_path_for_unit(unit: &str) -> Utf8NativePathBuf {
    let stem = fit_filename(sanitize_unit_name(unit), ".s");
    Utf8UnixPath::new(&stem).with_encoding().with_extension("s")
}
