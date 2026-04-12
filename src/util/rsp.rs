use std::collections::HashMap;

use anyhow::Result;
use typed_path::Utf8UnixPathBuf;

use crate::{obj::ObjInfo, util::lcf::obj_path_for_unit};

/// PE optional-header and per-section data needed to generate linker response files.
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
    pub major_image_version: u16,
    pub minor_image_version: u16,
    pub major_subsystem_version: u16,
    pub minor_subsystem_version: u16,
    /// `FileAlignment` from the optional header (e.g. 0x1000 for MSVC 6).
    pub file_alignment: u32,
    /// Set when IMAGE_FILE_RELOCS_STRIPPED is present in the file header.
    pub relocs_stripped: bool,
    /// Set when the PE has no Safe Exception Handler table (Load Config SEHandlerTable == 0).
    /// When true the linker must be told /SAFESEH:NO.
    pub no_seh: bool,
    /// Raw `Characteristics` field from IMAGE_SECTION_HEADER, keyed by section name.
    pub section_characteristics: HashMap<String, u32>,
    /// `VirtualSize` from each IMAGE_SECTION_HEADER, keyed by section name.
    pub section_vsizes: HashMap<String, u32>,
}

impl PeHeaderInfo {
    pub fn parse(data: &[u8]) -> Option<Self> {
        use object::{
            LittleEndian as LE,
            pe::{IMAGE_DIRECTORY_ENTRY_LOAD_CONFIG, ImageLoadConfigDirectory32},
            read::pe::{ImageNtHeaders, PeFile32},
        };
        let pe = PeFile32::parse(data).ok()?;
        let nt = pe.nt_headers();
        let opt = nt.optional_header();
        let relocs_stripped =
            nt.file_header().characteristics.get(LE) & object::pe::IMAGE_FILE_RELOCS_STRIPPED != 0;
        let file_alignment = opt.file_alignment.get(LE);

        let mut section_characteristics: HashMap<String, u32> = HashMap::new();
        let mut section_vsizes: HashMap<String, u32> = HashMap::new();
        for s in pe.section_table().iter() {
            let raw = s.name.as_ref();
            let Ok(name_str) = std::str::from_utf8(raw) else { continue };
            let name = name_str.trim_end_matches('\0').to_string();
            if name.is_empty() { continue; }
            section_characteristics.insert(name.clone(), s.characteristics.get(LE));
            section_vsizes.insert(name, s.virtual_size.get(LE));
        }

        // Detect Safe Exception Handler table from the Load Config directory.
        // If absent, too small, or SEHandlerTable == 0, emit /SAFESEH:NO.
        let no_seh = 'seh: {
            let Some(lc_dir) = pe.data_directory(IMAGE_DIRECTORY_ENTRY_LOAD_CONFIG) else {
                break 'seh true;
            };
            let lc_va = lc_dir.virtual_address.get(LE);
            if lc_va == 0 {
                break 'seh true;
            }
            // Minimum struct size to reach sehandler_table (offset 72 + 4 bytes)
            const MIN_SIZE: usize = 76;
            let lc_rva = lc_va.wrapping_sub(opt.image_base.get(LE));
            let Some(sec) = pe.section_table().iter().find(|s| {
                let va = s.virtual_address.get(LE);
                let sz = s.virtual_size.get(LE);
                lc_rva >= va && lc_rva < va.saturating_add(sz)
            }) else {
                break 'seh true;
            };
            let raw_off = sec.pointer_to_raw_data.get(LE) as usize;
            let file_off = raw_off + (lc_rva - sec.virtual_address.get(LE)) as usize;
            if file_off + MIN_SIZE > data.len() {
                break 'seh true;
            }
            match object::pod::from_bytes::<ImageLoadConfigDirectory32>(&data[file_off..]) {
                Ok((cfg, _)) => cfg.sehandler_table.get(LE) == 0,
                Err(_) => true,
            }
        };

        Some(Self {
            image_base: opt.image_base.get(LE),
            stack_reserve: opt.size_of_stack_reserve.get(LE),
            stack_commit: opt.size_of_stack_commit.get(LE),
            heap_reserve: opt.size_of_heap_reserve.get(LE),
            heap_commit: opt.size_of_heap_commit.get(LE),
            subsystem: opt.subsystem.get(LE),
            major_os_version: opt.major_operating_system_version.get(LE),
            minor_os_version: opt.minor_operating_system_version.get(LE),
            major_image_version: opt.major_image_version.get(LE),
            minor_image_version: opt.minor_image_version.get(LE),
            major_subsystem_version: opt.major_subsystem_version.get(LE),
            minor_subsystem_version: opt.minor_subsystem_version.get(LE),
            file_alignment,
            relocs_stripped,
            no_seh,
            section_characteristics,
            section_vsizes,
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

/// Generate the flags-only response file (`args.rsp`).
/// Contains all linker options but no object files.
/// Usage: `lld-link @args.rsp @objs.rsp /OUT:foo.exe`
pub fn generate_args_rsp(
    obj: &ObjInfo,
    pe: &PeHeaderInfo,
    force_includes: &[String],
) -> Result<String> {
    let mut lines: Vec<String> = Vec::new();

    lines.push("/includeglob:*".to_string());
    lines.push("/errorlimit:0".to_string());
    lines.push("/demangle:no".to_string());
    lines.push("/OPT:NOREF".to_string());
    lines.push("/OPT:NOICF".to_string());
    lines.push("/NODEFAULTLIB".to_string());

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
        "/SUBSYSTEM:{},{}",
        pe.subsystem_name(),
        pe.major_subsystem_version,
    ));
    lines.push(format!("/STACK:{:#x},{:#x}", pe.stack_reserve, pe.stack_commit));
    lines.push(format!("/HEAP:{:#x},{:#x}", pe.heap_reserve, pe.heap_commit));
    lines.push(format!("/VERSION:{}.{}", pe.major_image_version, pe.minor_image_version));

    if pe.file_alignment != 0 {
        lines.push(format!("/FILEALIGN:{:#x}", pe.file_alignment));
    }
    if pe.relocs_stripped {
        lines.push("/FIXED".to_string());
    }
    if pe.no_seh {
        lines.push("/SAFESEH:NO".to_string());
    }

    // Per-section permission flags
    for (_, section) in obj.sections.iter() {
        lines.push(format!("/SECTION:{},{}", section.name, pe.section_flags_str(&section.name)));
    }

    // Per-section virtual sizes (to preserve BSS regions and exact layout)
    for (_, section) in obj.sections.iter() {
        if let Some(&vsize) = pe.section_vsizes.get(&section.name) {
            lines.push(format!("/SECTIONVSIZE:{},{:#x}", section.name, vsize));
        }
    }

    for sym in force_includes {
        lines.push(format!("/INCLUDE:{sym}"));
    }

    Ok(lines.join("\n"))
}

/// Generate the objects-only response file (`objs.rsp`).
/// Contains one object file path per line, in link order.
/// Usage: `lld-link @args.rsp @objs.rsp /OUT:foo.exe`
pub fn generate_objs_rsp(
    obj: &ObjInfo,
    obj_dir: &Utf8UnixPathBuf,
) -> Result<String> {
    // Sort units by their lowest address so link order matches the original.
    let mut unit_min_addr: HashMap<&str, u64> = HashMap::new();
    for (_, section) in obj.sections.iter() {
        for (addr, split) in section.splits.iter() {
            let entry = unit_min_addr.entry(split.unit.as_str()).or_insert(u64::MAX);
            *entry = (*entry).min(section.address + addr as u64);
        }
    }

    let mut ordered_units: Vec<&str> = obj.link_order.iter().map(|u| u.name.as_str()).collect();
    ordered_units.sort_by_key(|u| unit_min_addr.get(u).copied().unwrap_or(u64::MAX));

    let lines: Vec<String> = ordered_units
        .into_iter()
        .map(|unit_name| {
            let obj_path = obj_path_for_unit(unit_name);
            obj_dir.join(&obj_path).to_string()
        })
        .collect();

    Ok(lines.join("\n"))
}
