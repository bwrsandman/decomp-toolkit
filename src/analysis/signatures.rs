use anyhow::{Result, anyhow};
use itertools::Itertools;

use crate::{
    analysis::{
        cfa::{AnalyzerState, SectionAddress},
        read_address,
    },
    obj::{
        ObjInfo, ObjSectionKind, ObjSplit, ObjSymbol, ObjSymbolFlagSet, ObjSymbolFlags,
        ObjSymbolKind,
    },
    util::signatures::{
        apply_signature, apply_signature_x86, check_signatures, check_signatures_str,
        check_signatures_x86, parse_signatures,
    },
};

const SIGNATURES: &[(&str, &str)] = &[
    ("__init_registers", include_str!("../../assets/signatures/__init_registers.yml")),
    ("__init_hardware", include_str!("../../assets/signatures/__init_hardware.yml")),
    ("__init_data", include_str!("../../assets/signatures/__init_data.yml")),
    ("__set_debug_bba", include_str!("../../assets/signatures/__set_debug_bba.yml")),
    ("__OSPSInit", include_str!("../../assets/signatures/__OSPSInit.yml")),
    ("__OSFPRInit", include_str!("../../assets/signatures/__OSFPRInit.yml")),
    ("__OSCacheInit", include_str!("../../assets/signatures/__OSCacheInit.yml")),
    ("DMAErrorHandler", include_str!("../../assets/signatures/DMAErrorHandler.yml")),
    ("DBInit", include_str!("../../assets/signatures/DBInit.yml")),
    ("OSInit", include_str!("../../assets/signatures/OSInit.yml")),
    ("__OSThreadInit", include_str!("../../assets/signatures/__OSThreadInit.yml")),
    ("__OSInitIPCBuffer", include_str!("../../assets/signatures/__OSInitIPCBuffer.yml")),
    ("EXIInit", include_str!("../../assets/signatures/EXIInit.yml")),
    ("EXIGetID", include_str!("../../assets/signatures/EXIGetID.yml")),
    ("exit", include_str!("../../assets/signatures/exit.yml")),
    ("_ExitProcess", include_str!("../../assets/signatures/_ExitProcess.yml")),
    ("__fini_cpp", include_str!("../../assets/signatures/__fini_cpp.yml")),
    // ("__destroy_global_chain", include_str!("../../assets/signatures/__destroy_global_chain.yml")),
    ("InitMetroTRK", include_str!("../../assets/signatures/InitMetroTRK.yml")),
    ("InitMetroTRKCommTable", include_str!("../../assets/signatures/InitMetroTRKCommTable.yml")),
    ("OSExceptionInit", include_str!("../../assets/signatures/OSExceptionInit.yml")),
    (
        "OSDefaultExceptionHandler",
        include_str!("../../assets/signatures/OSDefaultExceptionHandler.yml"),
    ),
    ("__OSUnhandledException", include_str!("../../assets/signatures/__OSUnhandledException.yml")),
    ("OSDisableScheduler", include_str!("../../assets/signatures/OSDisableScheduler.yml")),
    ("__OSReschedule", include_str!("../../assets/signatures/__OSReschedule.yml")),
    ("__OSInitSystemCall", include_str!("../../assets/signatures/__OSInitSystemCall.yml")),
    ("OSInitAlarm", include_str!("../../assets/signatures/OSInitAlarm.yml")),
    ("__OSInitAlarm", include_str!("../../assets/signatures/__OSInitAlarm.yml")),
    ("__OSEVStart", include_str!("../../assets/signatures/OSExceptionVector.yml")),
    ("__OSDBINTSTART", include_str!("../../assets/signatures/__OSDBIntegrator.yml")),
    ("__OSDBJUMPSTART", include_str!("../../assets/signatures/__OSDBJump.yml")),
    ("SIInit", include_str!("../../assets/signatures/SIInit.yml")),
    ("SIGetType", include_str!("../../assets/signatures/SIGetType.yml")),
    ("SISetSamplingRate", include_str!("../../assets/signatures/SISetSamplingRate.yml")),
    ("SISetXY", include_str!("../../assets/signatures/SISetXY.yml")),
    ("VIGetTvFormat", include_str!("../../assets/signatures/VIGetTvFormat.yml")),
    ("DVDInit", include_str!("../../assets/signatures/DVDInit.yml")),
    (
        "DVDSetAutoFatalMessaging",
        include_str!("../../assets/signatures/DVDSetAutoFatalMessaging.yml"),
    ),
    ("OSSetArenaLo", include_str!("../../assets/signatures/OSSetArenaLo.yml")),
    ("OSSetArenaHi", include_str!("../../assets/signatures/OSSetArenaHi.yml")),
    ("OSSetMEM1ArenaLo", include_str!("../../assets/signatures/OSSetMEM1ArenaLo.yml")),
    ("OSSetMEM1ArenaHi", include_str!("../../assets/signatures/OSSetMEM1ArenaHi.yml")),
    ("OSSetMEM2ArenaLo", include_str!("../../assets/signatures/OSSetMEM2ArenaLo.yml")),
    ("OSSetMEM2ArenaHi", include_str!("../../assets/signatures/OSSetMEM2ArenaHi.yml")),
    ("__OSInitAudioSystem", include_str!("../../assets/signatures/__OSInitAudioSystem.yml")),
    (
        "__OSInitMemoryProtection",
        include_str!("../../assets/signatures/__OSInitMemoryProtection.yml"),
    ),
    // ("BATConfig", include_str!("../../assets/signatures/BATConfig.yml")), TODO
    ("ReportOSInfo", include_str!("../../assets/signatures/ReportOSInfo.yml")),
    ("__check_pad3", include_str!("../../assets/signatures/__check_pad3.yml")),
    ("OSResetSystem", include_str!("../../assets/signatures/OSResetSystem.yml")),
    ("OSReturnToMenu", include_str!("../../assets/signatures/OSReturnToMenu.yml")),
    ("__OSReturnToMenu", include_str!("../../assets/signatures/__OSReturnToMenu.yml")),
    ("__OSShutdownDevices", include_str!("../../assets/signatures/__OSShutdownDevices.yml")),
    ("__OSInitSram", include_str!("../../assets/signatures/__OSInitSram.yml")),
    ("__OSSyncSram", include_str!("../../assets/signatures/__OSSyncSram.yml")),
    (
        "__OSGetExceptionHandler",
        include_str!("../../assets/signatures/__OSGetExceptionHandler.yml"),
    ),
    (
        "OSRegisterResetFunction",
        include_str!("../../assets/signatures/OSRegisterResetFunction.yml"),
    ),
    (
        "OSRegisterShutdownFunction",
        include_str!("../../assets/signatures/OSRegisterShutdownFunction.yml"),
    ),
    (
        "DecrementerExceptionHandler",
        include_str!("../../assets/signatures/DecrementerExceptionHandler.yml"),
    ),
    (
        "DecrementerExceptionCallback",
        include_str!("../../assets/signatures/DecrementerExceptionCallback.yml"),
    ),
    ("__OSInterruptInit", include_str!("../../assets/signatures/__OSInterruptInit.yml")),
    ("__OSContextInit", include_str!("../../assets/signatures/__OSContextInit.yml")),
    ("OSSwitchFPUContext", include_str!("../../assets/signatures/OSSwitchFPUContext.yml")),
    ("OSReport", include_str!("../../assets/signatures/OSReport.yml")),
    ("TRK_main", include_str!("../../assets/signatures/TRK_main.yml")),
    ("TRKNubWelcome", include_str!("../../assets/signatures/TRKNubWelcome.yml")),
    ("TRKInitializeNub", include_str!("../../assets/signatures/TRKInitializeNub.yml")),
    (
        "TRKInitializeIntDrivenUART",
        include_str!("../../assets/signatures/TRKInitializeIntDrivenUART.yml"),
    ),
    ("TRKEXICallBack", include_str!("../../assets/signatures/TRKEXICallBack.yml")),
    ("TRKLoadContext", include_str!("../../assets/signatures/TRKLoadContext.yml")),
    ("TRKInterruptHandler", include_str!("../../assets/signatures/TRKInterruptHandler.yml")),
    ("TRKExceptionHandler", include_str!("../../assets/signatures/TRKExceptionHandler.yml")),
    ("TRKSaveExtended1Block", include_str!("../../assets/signatures/TRKSaveExtended1Block.yml")),
    ("TRKNubMainLoop", include_str!("../../assets/signatures/TRKNubMainLoop.yml")),
    ("TRKTargetContinue", include_str!("../../assets/signatures/TRKTargetContinue.yml")),
    ("TRKSwapAndGo", include_str!("../../assets/signatures/TRKSwapAndGo.yml")),
    (
        "TRKRestoreExtended1Block",
        include_str!("../../assets/signatures/TRKRestoreExtended1Block.yml"),
    ),
    (
        "TRKInterruptHandlerEnableInterrupts",
        include_str!("../../assets/signatures/TRKInterruptHandlerEnableInterrupts.yml"),
    ),
    ("memset", include_str!("../../assets/signatures/memset.yml")),
    (
        "__msl_runtime_constraint_violation_s",
        include_str!("../../assets/signatures/__msl_runtime_constraint_violation_s.yml"),
    ),
    ("ClearArena", include_str!("../../assets/signatures/ClearArena.yml")),
    ("IPCCltInit", include_str!("../../assets/signatures/IPCCltInit.yml")),
    ("__OSInitSTM", include_str!("../../assets/signatures/__OSInitSTM.yml")),
    ("IOS_Open", include_str!("../../assets/signatures/IOS_Open.yml")),
    ("__ios_Ipc2", include_str!("../../assets/signatures/__ios_Ipc2.yml")),
    ("IPCiProfQueueReq", include_str!("../../assets/signatures/IPCiProfQueueReq.yml")),
    ("SCInit", include_str!("../../assets/signatures/SCInit.yml")),
    ("SCReloadConfFileAsync", include_str!("../../assets/signatures/SCReloadConfFileAsync.yml")),
    ("NANDPrivateOpenAsync", include_str!("../../assets/signatures/NANDPrivateOpenAsync.yml")),
    ("nandIsInitialized", include_str!("../../assets/signatures/nandIsInitialized.yml")),
    ("nandOpen", include_str!("../../assets/signatures/nandOpen.yml")),
    ("nandGenerateAbsPath", include_str!("../../assets/signatures/nandGenerateAbsPath.yml")),
    ("nandGetHeadToken", include_str!("../../assets/signatures/nandGetHeadToken.yml")),
    ("ISFS_OpenAsync", include_str!("../../assets/signatures/ISFS_OpenAsync.yml")),
    ("nandConvertErrorCode", include_str!("../../assets/signatures/nandConvertErrorCode.yml")),
    (
        "NANDLoggingAddMessageAsync",
        include_str!("../../assets/signatures/NANDLoggingAddMessageAsync.yml"),
    ),
    (
        "__NANDPrintErrorMessage",
        include_str!("../../assets/signatures/__NANDPrintErrorMessage.yml"),
    ),
    ("__OSInitNet", include_str!("../../assets/signatures/__OSInitNet.yml")),
    ("__DVDCheckDevice", include_str!("../../assets/signatures/__DVDCheckDevice.yml")),
    ("__OSInitPlayTime", include_str!("../../assets/signatures/__OSInitPlayTime.yml")),
    ("__OSStartPlayRecord", include_str!("../../assets/signatures/__OSStartPlayRecord.yml")),
    ("NANDInit", include_str!("../../assets/signatures/NANDInit.yml")),
    ("ISFS_OpenLib", include_str!("../../assets/signatures/ISFS_OpenLib.yml")),
    ("ESP_GetTitleId", include_str!("../../assets/signatures/ESP_GetTitleId.yml")),
    (
        "NANDSetAutoErrorMessaging",
        include_str!("../../assets/signatures/NANDSetAutoErrorMessaging.yml"),
    ),
    ("__DVDFSInit", include_str!("../../assets/signatures/__DVDFSInit.yml")),
    ("__DVDClearWaitingQueue", include_str!("../../assets/signatures/__DVDClearWaitingQueue.yml")),
    ("__DVDInitWA", include_str!("../../assets/signatures/__DVDInitWA.yml")),
    ("__DVDLowSetWAType", include_str!("../../assets/signatures/__DVDLowSetWAType.yml")),
    ("__fstLoad", include_str!("../../assets/signatures/__fstLoad.yml")),
    ("DVDReset", include_str!("../../assets/signatures/DVDReset.yml")),
    ("DVDLowReset", include_str!("../../assets/signatures/DVDLowReset.yml")),
    ("DVDReadDiskID", include_str!("../../assets/signatures/DVDReadDiskID.yml")),
    ("stateReady", include_str!("../../assets/signatures/stateReady.yml")),
    ("DVDLowWaitCoverClose", include_str!("../../assets/signatures/DVDLowWaitCoverClose.yml")),
    ("__DVDStoreErrorCode", include_str!("../../assets/signatures/__DVDStoreErrorCode.yml")),
    ("DVDLowStopMotor", include_str!("../../assets/signatures/DVDLowStopMotor.yml")),
    ("DVDGetDriveStatus", include_str!("../../assets/signatures/DVDGetDriveStatus.yml")),
    ("printf", include_str!("../../assets/signatures/printf.yml")),
    ("sprintf", include_str!("../../assets/signatures/sprintf.yml")),
    ("vprintf", include_str!("../../assets/signatures/vprintf.yml")),
    ("vsprintf", include_str!("../../assets/signatures/vsprintf.yml")),
    ("vsnprintf", include_str!("../../assets/signatures/vsnprintf.yml")),
    ("__pformatter", include_str!("../../assets/signatures/__pformatter.yml")),
    ("longlong2str", include_str!("../../assets/signatures/longlong2str.yml")),
    ("__mod2u", include_str!("../../assets/signatures/__mod2u.yml")),
    ("__FileWrite", include_str!("../../assets/signatures/__FileWrite.yml")),
    ("fwrite", include_str!("../../assets/signatures/fwrite.yml")),
    ("__fwrite", include_str!("../../assets/signatures/__fwrite.yml")),
    ("__stdio_atexit", include_str!("../../assets/signatures/__stdio_atexit.yml")),
    ("__StringWrite", include_str!("../../assets/signatures/__StringWrite.yml")),
];
const POST_SIGNATURES: &[(&str, &str)] = &[
    ("RSOStaticLocateObject", include_str!("../../assets/signatures/RSOStaticLocateObject.yml")),
    ("GXInit", include_str!("../../assets/signatures/GXInit.yml")),
    ("__register_fragment", include_str!("../../assets/signatures/__register_fragment.yml")),
    ("__unregister_fragment", include_str!("../../assets/signatures/__unregister_fragment.yml")),
    ("__register_atexit", include_str!("../../assets/signatures/__register_atexit.yml")),
    (
        "__register_global_object",
        include_str!("../../assets/signatures/__register_global_object.yml"),
    ),
];

fn apply_signature_for_symbol(obj: &mut ObjInfo, name: &str, sig_str: &str) -> Result<()> {
    for symbol_idx in obj.symbols.for_name(name).map(|(i, _)| i).collect_vec() {
        let symbol = &obj.symbols[symbol_idx];
        let Some(section_index) = symbol.section else {
            continue;
        };
        let addr = symbol.address as u32;
        let section = &obj.sections[section_index];
        if let Some(signature) = check_signatures_str(section, addr, sig_str)? {
            apply_signature(obj, SectionAddress::new(section_index, addr), &signature)?;
        }
    }
    Ok(())
}

fn apply_ctors_signatures(obj: &mut ObjInfo) -> Result<()> {
    let Some((_, symbol)) = obj.symbols.by_name("_ctors")? else {
        return Ok(());
    };
    // First entry of ctors is __init_cpp_exceptions
    let ctors_section_index =
        symbol.section.ok_or_else(|| anyhow!("Missing _ctors symbol section"))?;
    let ctors_section = &obj.sections[ctors_section_index];
    // __init_cpp_exceptions_reference + null pointer
    if ctors_section.size < 8 {
        return Ok(());
    }
    let Some(target) = read_address(obj, ctors_section, symbol.address as u32).ok() else {
        return Ok(());
    };
    let Some(signature) = check_signatures_str(
        &obj.sections[target.section],
        target.address,
        include_str!("../../assets/signatures/__init_cpp_exceptions.yml"),
    )?
    else {
        return Ok(());
    };
    let address = symbol.address;
    apply_signature(obj, target, &signature)?;
    obj.symbols.add(
        ObjSymbol {
            name: "__init_cpp_exceptions_reference".to_string(),
            address,
            section: Some(ctors_section_index),
            size: 4,
            size_known: true,
            flags: ObjSymbolFlagSet(ObjSymbolFlags::Global | ObjSymbolFlags::RelocationIgnore),
            kind: ObjSymbolKind::Object,
            ..Default::default()
        },
        true,
    )?;
    if obj.sections[ctors_section_index].splits.for_address(address as u32).is_none() {
        obj.add_split(ctors_section_index, address as u32, ObjSplit {
            unit: "__init_cpp_exceptions.cpp".to_string(),
            end: address as u32 + 4,
            align: None,
            common: false,
            autogenerated: true,
            skip: false,
            rename: None,
        })?;
    }
    Ok(())
}

fn apply_dtors_signatures(obj: &mut ObjInfo) -> Result<()> {
    let (dtors_section_index, dtors_section) =
        if let Some((_, symbol)) = obj.symbols.by_name("_dtors")? {
            let section_index =
                symbol.section.ok_or_else(|| anyhow!("Missing _dtors symbol section"))?;
            (section_index, &obj.sections[section_index])
        } else if let Some((section_index, section)) = obj.sections.by_name(".dtors")? {
            (section_index, section)
        } else {
            return Ok(());
        };
    // __destroy_global_chain_reference + null pointer
    if dtors_section.size < 8 {
        return Ok(());
    }
    let address = dtors_section.address;
    let dgc_target = read_address(obj, dtors_section, address as u32).ok();
    let fce_target = read_address(obj, dtors_section, address as u32 + 4).ok();
    let mut found_dgc = false;
    let mut found_fce = false;

    // First entry of dtors is __destroy_global_chain
    if let Some(dgc_target) = dgc_target {
        if let Some(signature) = check_signatures_str(
            &obj.sections[dgc_target.section],
            dgc_target.address,
            include_str!("../../assets/signatures/__destroy_global_chain.yml"),
        )? {
            apply_signature(obj, dgc_target, &signature)?;
            obj.add_symbol(
                ObjSymbol {
                    name: "__destroy_global_chain_reference".to_string(),
                    address,
                    section: Some(dtors_section_index),
                    size: 4,
                    size_known: true,
                    flags: ObjSymbolFlagSet(
                        ObjSymbolFlags::Global | ObjSymbolFlags::RelocationIgnore,
                    ),
                    kind: ObjSymbolKind::Object,
                    ..Default::default()
                },
                true,
            )?;
            found_dgc = true;
        } else {
            log::debug!("Failed to match __destroy_global_chain signature ({:#010X})", dgc_target);
        }
    }

    // Second entry of dtors is __fini_cpp_exceptions
    if let Some(fce_target) = fce_target {
        if let Some(signature) = check_signatures_str(
            &obj.sections[fce_target.section],
            fce_target.address,
            include_str!("../../assets/signatures/__fini_cpp_exceptions.yml"),
        )? {
            apply_signature(obj, fce_target, &signature)?;
            obj.add_symbol(
                ObjSymbol {
                    name: "__fini_cpp_exceptions_reference".to_string(),
                    address: address + 4,
                    section: Some(dtors_section_index),
                    size: 4,
                    size_known: true,
                    flags: ObjSymbolFlagSet(
                        ObjSymbolFlags::Global | ObjSymbolFlags::RelocationIgnore,
                    ),
                    kind: ObjSymbolKind::Object,
                    ..Default::default()
                },
                true,
            )?;
            found_fce = true;
        }
    }

    if found_dgc {
        let mut end = address as u32 + 4;
        if found_fce {
            end += 4;
        }
        if obj.sections[dtors_section_index].splits.for_address(address as u32).is_none() {
            obj.add_split(dtors_section_index, address as u32, ObjSplit {
                unit: "__init_cpp_exceptions.cpp".to_string(),
                end,
                align: None,
                common: false,
                autogenerated: true,
                skip: false,
                rename: None,
            })?;
        }
    }
    Ok(())
}

fn apply_init_user_signatures(obj: &mut ObjInfo) -> Result<()> {
    let Some((_, symbol)) = obj.symbols.by_name("__init_user")? else {
        return Ok(());
    };
    let Some(section_index) = symbol.section else {
        return Ok(());
    };
    // __init_user can be overridden, but we can still look for __init_cpp from it
    let mut analyzer = AnalyzerState::default();
    analyzer.process_function_at(obj, SectionAddress::new(section_index, symbol.address as u32))?;
    for (addr, _) in analyzer.functions {
        let section = &obj.sections[addr.section];
        if let Some(signature) = check_signatures_str(
            section,
            addr.address,
            include_str!("../../assets/signatures/__init_cpp.yml"),
        )? {
            apply_signature(obj, SectionAddress::new(section_index, addr.address), &signature)?;
            break;
        }
    }
    Ok(())
}

pub fn apply_signatures(obj: &mut ObjInfo) -> Result<()> {
    if let Some(entry) = obj.entry.map(|n| n as u32) {
        let (entry_section_index, entry_section) = obj.sections.at_address(entry)?;
        if let Some(signature) = check_signatures_str(
            entry_section,
            entry,
            include_str!("../../assets/signatures/__start.yml"),
        )? {
            apply_signature(obj, SectionAddress::new(entry_section_index, entry), &signature)?;
        }
    }

    for &(name, sig_str) in SIGNATURES {
        apply_signature_for_symbol(obj, name, sig_str)?
    }

    apply_init_user_signatures(obj)?;
    apply_ctors_signatures(obj)?;
    apply_dtors_signatures(obj)?;
    Ok(())
}

pub fn apply_signatures_post(obj: &mut ObjInfo) -> Result<()> {
    log::debug!("Checking post CFA signatures");
    for &(_name, sig_str) in POST_SIGNATURES {
        let signatures = parse_signatures(sig_str)?;
        let mut found_signature = None;
        'outer: for (section_index, section) in obj.sections.by_kind(ObjSectionKind::Code) {
            for (symbol_index, symbol) in obj
                .symbols
                .for_section(section_index)
                .filter(|(_, sym)| sym.kind == ObjSymbolKind::Function)
            {
                if let Some(signature) =
                    check_signatures(section, symbol.address as u32, &signatures)?
                {
                    found_signature = Some((symbol_index, signature));
                    break 'outer;
                }
            }
        }
        if let Some((symbol_index, signature)) = found_signature {
            let symbol = &obj.symbols[symbol_index];
            let symbol_addr = SectionAddress::new(symbol.section.unwrap(), symbol.address as u32);
            apply_signature(obj, symbol_addr, &signature)?;
        }
    }
    Ok(())
}

/// Create _ctors and _dtors symbols if missing
pub fn update_ctors_dtors(obj: &mut ObjInfo) -> Result<()> {
    if obj.symbols.by_name("_ctors")?.is_none() {
        if let Some((section_index, section)) = obj.sections.by_name(".ctors")? {
            obj.symbols.add_direct(ObjSymbol {
                name: "_ctors".to_string(),
                address: section.address,
                section: Some(section_index),
                size_known: true,
                flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
                ..Default::default()
            })?;
        }
    }
    if obj.symbols.by_name("_dtors")?.is_none() {
        if let Some((section_index, section)) = obj.sections.by_name(".dtors")? {
            obj.symbols.add_direct(ObjSymbol {
                name: "_dtors".to_string(),
                address: section.address,
                section: Some(section_index),
                size_known: true,
                flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
                ..Default::default()
            })?;
        }
    }
    Ok(())
}

// ── x86 / COFF / PE signatures ───────────────────────────────────────────────
//
// Mirrors the PPC SIGNATURES / POST_SIGNATURES tables above, but for x86 PE
// targets.  Signature files live under assets/signatures/x86/**/*.yml and are
// compiled in automatically by build.rs — add a .yml file and rebuild.
//
// An optional runtime directory can also be passed for project-specific sigs.

include!(concat!(env!("OUT_DIR"), "/x86_signatures_generated.rs"));


/// Load all *.yml files from `dir` and return them as `(stem, content)` pairs.
/// Errors reading individual files are logged and skipped.
fn load_sig_dir(dir: &std::path::Path) -> Vec<(String, String)> {
    let mut out = Vec::new();
    let entries = match std::fs::read_dir(dir) {
        Ok(e) => e,
        Err(e) => {
            log::warn!("x86 signatures dir '{}': {e}", dir.display());
            return out;
        }
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.extension().and_then(|e| e.to_str()) != Some("yml") {
            continue;
        }
        let stem = path
            .file_stem()
            .and_then(|s| s.to_str())
            .unwrap_or("")
            .to_string();
        match std::fs::read_to_string(&path) {
            Ok(content) => out.push((stem, content)),
            Err(e) => log::warn!("Failed to read '{}': {e}", path.display()),
        }
    }
    out
}

fn apply_signature_x86_for_symbol(obj: &mut ObjInfo, name: &str, sig_str: &str) -> Result<()> {
    let sigs = parse_signatures(sig_str)?;
    for symbol_idx in obj.symbols.for_name(name).map(|(i, _)| i).collect_vec() {
        let symbol = &obj.symbols[symbol_idx];
        let Some(section_index) = symbol.section else { continue };
        let addr = symbol.address as u32;
        let section = &obj.sections[section_index];
        if let Some(sig) = check_signatures_x86(section, addr, &sigs, None)? {
            apply_signature_x86(obj, SectionAddress::new(section_index, addr), &sig)?;
        }
    }
    Ok(())
}

/// Check the PE entry point and every already-named symbol against all
/// compiled-in x86 signatures, plus any extra .yml files in `sig_dir`.
pub fn apply_signatures_x86(obj: &mut ObjInfo, sig_dir: Option<&std::path::Path>) -> Result<()> {
    let dir_sigs = sig_dir.map(load_sig_dir).unwrap_or_default();
    let all: Vec<(&str, &str)> = SIGNATURES_X86
        .iter()
        .map(|&(n, s)| (n, s))
        .chain(dir_sigs.iter().map(|(n, s)| (n.as_str(), s.as_str())))
        .collect();

    if all.is_empty() { return Ok(()); }

    // Check entry point.
    if let Some(entry) = obj.entry.map(|n| n as u32) {
        if let Ok((entry_sec_idx, entry_sec)) = obj.sections.at_address(entry) {
            for (_, sig_str) in &all {
                let parsed = parse_signatures(sig_str)?;
                if let Some(sig) = check_signatures_x86(entry_sec, entry, &parsed, None)? {
                    apply_signature_x86(obj, SectionAddress::new(entry_sec_idx, entry), &sig)?;
                    break;
                }
            }
        }
    }

    // Check every already-named symbol.
    for (name, sig_str) in &all {
        apply_signature_x86_for_symbol(obj, name, sig_str)?;
    }
    Ok(())
}

/// Scan all code functions against all compiled-in x86 signatures plus any
/// extra .yml files in `sig_dir`.
pub fn apply_signatures_post_x86(
    obj: &mut ObjInfo,
    sig_dir: Option<&std::path::Path>,
) -> Result<()> {
    let dir_sigs = sig_dir.map(load_sig_dir).unwrap_or_default();
    let all_strs: Vec<&str> = SIGNATURES_X86
        .iter()
        .map(|&(_, s)| s)
        .chain(dir_sigs.iter().map(|(_, s)| s.as_str()))
        .collect();

    if all_strs.is_empty() { return Ok(()); }
    log::debug!("Checking post-analysis x86 signatures ({} file(s))", all_strs.len());

    // Pre-compute function sizes per section (gap to next function entry).
    // This is used to reject false-positive matches where a short signature
    // happens to match the start of a longer, unrelated function.
    use std::collections::BTreeMap;
    let mut fn_sizes: BTreeMap<u32, u32> = BTreeMap::new(); // fn_va → size
    for (section_index, _) in obj.sections.by_kind(ObjSectionKind::Code) {
        let sec = &obj.sections[section_index];
        let sec_end = (sec.address + sec.size) as u32;
        let mut addrs: Vec<u32> = obj
            .symbols
            .for_section(section_index)
            .filter(|(_, s)| s.kind == ObjSymbolKind::Function)
            .map(|(_, s)| s.address as u32)
            .collect();
        addrs.sort_unstable();
        addrs.dedup();
        for (i, &addr) in addrs.iter().enumerate() {
            let next = addrs.get(i + 1).copied().unwrap_or(sec_end);
            fn_sizes.insert(addr, next - addr);
        }
    }

    for sig_str in &all_strs {
        let parsed = parse_signatures(sig_str)?;
        let mut matches: Vec<(u32, crate::util::signatures::FunctionSignature)> = Vec::new();
        for (section_index, section) in obj.sections.by_kind(ObjSectionKind::Code) {
            for (symbol_index, symbol) in obj
                .symbols
                .for_section(section_index)
                .filter(|(_, s)| s.kind == ObjSymbolKind::Function)
            {
                let addr = symbol.address as u32;
                // Prefer the symbol's own size (from compute_x86_function_sizes, which strips
                // NOP/INT3 padding) over the gap-to-next-function, which includes padding and
                // would cause the size check in check_signature_x86 to reject valid matches.
                let size = if symbol.size_known && symbol.size > 0 {
                    Some(symbol.size as u32)
                } else {
                    fn_sizes.get(&addr).copied()
                };
                if let Some(sig) = check_signatures_x86(section, addr, &parsed, size)? {
                    matches.push((symbol_index, sig));
                }
            }
        }
        // If a signature matches multiple functions it's ambiguous — skip it.
        if matches.len() > 1 {
            let name = &parsed[0].symbols[parsed[0].symbol as usize].name;
            log::debug!(
                "Skipping ambiguous x86 signature '{}' ({} matches)",
                name,
                matches.len()
            );
            continue;
        }
        for (symbol_index, sig) in matches {
            let symbol = &obj.symbols[symbol_index];
            let addr = SectionAddress::new(symbol.section.unwrap(), symbol.address as u32);
            apply_signature_x86(obj, addr, &sig)?;
        }
    }
    Ok(())
}
