use std::collections::HashMap;

use anyhow::Result;
use typed_path::Utf8UnixPathBuf;

use crate::{obj::ObjInfo, util::lcf::obj_path_for_unit};

/// PE optional-header and per-section data needed to generate a linker response file.
#[derive(Debug, Default)]
pub struct PeHeaderInfo {
    pub image_base: u32,
    pub stack_reserve: u32,
    pub stack_commit: u32,
    pub heap_reserve: u32,
    pub heap_commit: u32,
    pub subsystem: u16,
    pub major_os_version: u16,
    pub minor_os_version: u16,
    pub major_subsystem_version: u16,
    pub minor_subsystem_version: u16,
    /// Set when IMAGE_FILE_RELOCS_STRIPPED is present in the file header.
    pub relocs_stripped: bool,
    /// Raw `Characteristics` field from IMAGE_SECTION_HEADER, keyed by section name.
    pub section_characteristics: HashMap<String, u32>,
}

impl PeHeaderInfo {
    pub fn parse(data: &[u8]) -> Option<Self> {
        use object::{LittleEndian as LE, read::pe::{ImageNtHeaders, PeFile32}};
        let pe = PeFile32::parse(data).ok()?;
        let nt = pe.nt_headers();
        let opt = nt.optional_header();
        let relocs_stripped =
            nt.file_header().characteristics.get(LE) & object::pe::IMAGE_FILE_RELOCS_STRIPPED != 0;
        let section_characteristics = pe
            .section_table()
            .iter()
            .filter_map(|s| {
                // name is a fixed 8-byte field; strip null padding and any leading '/'
                let raw = s.name.as_ref();
                let name = std::str::from_utf8(raw)
                    .ok()?
                    .trim_end_matches('\0')
                    .to_string();
                if name.is_empty() { return None; }
                Some((name, s.characteristics.get(LE)))
            })
            .collect();
        Some(Self {
            image_base: opt.image_base.get(LE),
            stack_reserve: opt.size_of_stack_reserve.get(LE),
            stack_commit: opt.size_of_stack_commit.get(LE),
            heap_reserve: opt.size_of_heap_reserve.get(LE),
            heap_commit: opt.size_of_heap_commit.get(LE),
            subsystem: opt.subsystem.get(LE),
            major_os_version: opt.major_operating_system_version.get(LE),
            minor_os_version: opt.minor_operating_system_version.get(LE),
            major_subsystem_version: opt.major_subsystem_version.get(LE),
            minor_subsystem_version: opt.minor_subsystem_version.get(LE),
            relocs_stripped,
            section_characteristics,
        })
    }

    fn subsystem_name(&self) -> &'static str {
        use object::pe::*;
        match self.subsystem {
            IMAGE_SUBSYSTEM_WINDOWS_GUI => "WINDOWS",
            IMAGE_SUBSYSTEM_WINDOWS_CUI => "CONSOLE",
            IMAGE_SUBSYSTEM_NATIVE => "NATIVE",
            IMAGE_SUBSYSTEM_WINDOWS_CE_GUI => "WINDOWSCE",
            IMAGE_SUBSYSTEM_EFI_APPLICATION => "EFI_APPLICATION",
            IMAGE_SUBSYSTEM_EFI_BOOT_SERVICE_DRIVER => "EFI_BOOT_SERVICE_DRIVER",
            IMAGE_SUBSYSTEM_EFI_RUNTIME_DRIVER => "EFI_RUNTIME_DRIVER",
            IMAGE_SUBSYSTEM_EFI_ROM => "EFI_ROM",
            IMAGE_SUBSYSTEM_XBOX => "XBOX",
            IMAGE_SUBSYSTEM_POSIX_CUI => "POSIX",
            _ => "WINDOWS",
        }
    }

    fn section_flags_str(&self, section_name: &str) -> &'static str {
        use object::pe::*;
        let chars = self.section_characteristics.get(section_name).copied().unwrap_or(0);
        let r = chars & IMAGE_SCN_MEM_READ != 0;
        let w = chars & IMAGE_SCN_MEM_WRITE != 0;
        let x = chars & IMAGE_SCN_MEM_EXECUTE != 0;
        // lld-link/link.exe syntax: R=read, W=write, E=execute (single letters, no commas)
        match (r, w, x) {
            (true, true, true) => "RWE",
            (true, false, true) => "RE",
            (true, true, false) => "RW",
            (true, false, false) => "R",
            (false, true, false) => "W",
            _ => "R",
        }
    }
}

/// Generate an MSVC/lld-link response file (`link.rsp`) for a PE executable.
/// Pass to the linker as `lld-link @link.rsp` or `link.exe @link.rsp`.
pub fn generate_link_rsp(
    obj: &ObjInfo,
    pe: &PeHeaderInfo,
    obj_dir: &Utf8UnixPathBuf,
    force_includes: &[String],
) -> Result<String> {
    let mut lines: Vec<String> = Vec::new();

    lines.push(format!("/BASE:{:#x}", pe.image_base));

    // Resolve entry symbol name from the entry VA
    if let Some(entry_sym) = obj.entry.and_then(|e| {
        let (sec_idx, _) = obj.sections.at_address(e as u32).ok()?;
        obj.symbols
            .at_section_address(sec_idx, e as u32)
            .find(|(_, s)| s.kind == crate::obj::ObjSymbolKind::Function)
            .map(|(_, s)| s.name.clone())
    }) {
        lines.push(format!("/ENTRY:{entry_sym}"));
    }

    lines.push(format!(
        "/SUBSYSTEM:{},{}.{}",
        pe.subsystem_name(),
        pe.major_subsystem_version,
        pe.minor_subsystem_version,
    ));
    lines.push(format!("/STACK:{:#x},{:#x}", pe.stack_reserve, pe.stack_commit));
    lines.push(format!("/HEAP:{:#x},{:#x}", pe.heap_reserve, pe.heap_commit));
    lines.push(format!("/VERSION:{}.{}", pe.major_os_version, pe.minor_os_version));
    lines.push("/NODEFAULTLIB".to_string());
    if pe.relocs_stripped {
        lines.push("/FIXED".to_string());
    }

    // Per-section flags derived from original PE section characteristics
    for (_, section) in obj.sections.iter() {
        lines.push(format!("/SECTION:{},{}", section.name, pe.section_flags_str(&section.name)));
    }

    for sym in force_includes {
        lines.push(format!("/INCLUDE:{sym}"));
    }

    // Object files sorted by their lowest address across all sections (original segment order)
    let mut unit_min_addr: HashMap<&str, u64> = HashMap::new();
    for (_, section) in obj.sections.iter() {
        for (addr, split) in section.splits.iter() {
            let entry = unit_min_addr.entry(split.unit.as_str()).or_insert(u64::MAX);
            *entry = (*entry).min(section.address + addr as u64);
        }
    }

    let mut ordered_units: Vec<&str> = obj.link_order.iter().map(|u| u.name.as_str()).collect();
    ordered_units.sort_by_key(|u| unit_min_addr.get(u).copied().unwrap_or(u64::MAX));

    for unit_name in ordered_units {
        let obj_path = obj_path_for_unit(unit_name);
        lines.push(obj_dir.join(&obj_path).to_string());
    }

    Ok(lines.join("\n"))
}
