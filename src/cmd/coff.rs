use std::{
    collections::{BTreeMap, HashMap},
    fs,
    fs::DirBuilder,
    io::Write,
    time::Instant,
};
use rayon::prelude::*;

use anyhow::{Context, Result, bail};
use argp::FromArgs;
use itertools::Itertools;
use tracing::{debug, info};
use typed_path::{Utf8NativePath, Utf8NativePathBuf};
use xxhash_rust::xxh3::xxh3_64;

use crate::{
    analysis::{
        objects::{detect_objects, detect_strings},
        pe::detect_pe_symbols,
        rtti::detect_rtti,
        signatures::{apply_signatures_post_x86, apply_signatures_x86},
        x86::{analyze_x86_functions, compute_x86_function_sizes},
    },
    cmd::{
        dol::{
            ModuleConfig, ObjectBase, OutputConfig, OutputLink, OutputModule, OutputUnit,
            ProjectConfig, find_object_base,
        },
        shasum::file_sha1_string,
    },
    obj::{
        ObjInfo, ObjKind, ObjRelocKind, ObjSymbol, ObjSymbolFlags, ObjSymbolKind, ObjSymbolScope,
        SymbolIndex, best_match_for_reloc,
    },
    util::{
        coff::{apply_base_relocations, create_function_splits, process_coff, write_coff},
        config::{apply_splits_file, apply_symbols_file, is_auto_symbol, write_splits_file, write_symbols_file},
        dep::DepFile,
        file::{FileReadInfo, buf_writer, process_rsp, touch, verify_hash},
        lcf::obj_path_for_unit,
        rsp::{PeHeaderInfo, generate_args_rsp, generate_objs_rsp},
        signatures::{
            FunctionSignature, compare_signature, generate_all_signatures_x86,
            generate_signature_x86,
        },
        split::{split_obj, update_splits},
    },
    vfs::open_file,
};

#[derive(FromArgs, PartialEq, Debug)]
/// Commands for processing COFF/PE files.
#[argp(subcommand, name = "coff")]
pub struct Args {
    #[argp(subcommand)]
    command: SubCommand,
}

#[derive(FromArgs, PartialEq, Debug)]
#[argp(subcommand)]
enum SubCommand {
    Split(SplitArgs),
    Diff(DiffArgs),
    Apply(ApplyArgs),
    Sigs(SignaturesArgs),
    SigsLib(SigsLibArgs),
}

#[derive(FromArgs, PartialEq, Eq, Debug)]
/// Generate x86 byte-pattern signatures from COFF/PE object files.
#[argp(subcommand, name = "sigs")]
pub struct SignaturesArgs {
    #[argp(positional, from_str_fn(crate::util::path::native_path))]
    /// input COFF/PE files (or @response files)
    files: Vec<Utf8NativePathBuf>,
    #[argp(option, short = 's')]
    /// symbol name
    symbol: String,
    #[argp(option, short = 'o', from_str_fn(crate::util::path::native_path))]
    /// output .yml file
    out_file: Utf8NativePathBuf,
}

#[derive(FromArgs, PartialEq, Eq, Debug)]
/// Generate x86 signatures for every defined function across all .obj members of one or
/// more static libraries (.lib), writing one .yml per symbol into an output directory.
/// Multiple .lib files (e.g. different compiler versions) are merged: symbols with
/// differing byte patterns produce multiple entries in the same .yml.
#[argp(subcommand, name = "sigs-lib")]
pub struct SigsLibArgs {
    #[argp(positional, from_str_fn(crate::util::path::native_path))]
    /// input static library (.lib) files
    lib_files: Vec<Utf8NativePathBuf>,
    #[argp(option, short = 'o', from_str_fn(crate::util::path::native_path))]
    /// output directory for .yml signature files
    out_dir: Utf8NativePathBuf,
}

#[derive(FromArgs, PartialEq, Eq, Debug)]
/// Applies updated symbols from a linked PE to the project configuration.
#[argp(subcommand, name = "apply")]
pub struct ApplyArgs {
    #[argp(positional, from_str_fn(crate::util::path::native_path))]
    /// input configuration file
    config: Utf8NativePathBuf,
    #[argp(positional, from_str_fn(crate::util::path::native_path))]
    /// linked PE (.exe) to read symbols from
    exe_file: Utf8NativePathBuf,
}

#[derive(FromArgs, PartialEq, Eq, Debug)]
/// Diffs symbols in a linked PE against the original.
#[argp(subcommand, name = "diff")]
pub struct DiffArgs {
    #[argp(positional, from_str_fn(crate::util::path::native_path))]
    /// input configuration file
    config: Utf8NativePathBuf,
    #[argp(positional, from_str_fn(crate::util::path::native_path))]
    /// linked PE (.exe) to compare against
    exe_file: Utf8NativePathBuf,
}

#[derive(FromArgs, PartialEq, Eq, Debug)]
/// Splits a COFF/PE binary into relocatable objects.
#[argp(subcommand, name = "split")]
pub struct SplitArgs {
    #[argp(positional, from_str_fn(crate::util::path::native_path))]
    /// input configuration file
    config: Utf8NativePathBuf,
    #[argp(positional, from_str_fn(crate::util::path::native_path))]
    /// output directory
    out_dir: Utf8NativePathBuf,
    #[argp(switch)]
    /// skip updating splits & symbol files (for build systems)
    no_update: bool,
    #[argp(option, short = 'j')]
    /// number of threads to use (default: number of logical CPUs)
    jobs: Option<usize>,
}

pub fn run(args: Args) -> Result<()> {
    match args.command {
        SubCommand::Split(c_args) => split(c_args),
        SubCommand::Diff(c_args) => diff(c_args),
        SubCommand::Apply(c_args) => apply(c_args),
        SubCommand::Sigs(c_args) => signatures(c_args),
        SubCommand::SigsLib(c_args) => sigs_lib(c_args),
    }
}

fn sigs_lib(args: SigsLibArgs) -> Result<()> {
    use object::read::archive::ArchiveFile;

    let out_dir = args.out_dir.with_encoding();
    fs::DirBuilder::new().recursive(true).create(&out_dir)?;

    let mut by_symbol: HashMap<String, HashMap<String, FunctionSignature>> = HashMap::new();
    let mut total_members = 0u32;

    for lib_path in &args.lib_files {
        let lib_path_native = lib_path.with_encoding();
        info!("Processing {}", lib_path_native);
        let lib_data = fs::read(&lib_path_native)
            .with_context(|| format!("Failed to read '{lib_path_native}'"))?;
        let archive = ArchiveFile::parse(lib_data.as_slice())
            .with_context(|| format!("Failed to parse archive '{lib_path_native}'"))?;
        let mut member_count = 0u32;

        for member in archive.members() {
            let member: object::read::archive::ArchiveMember =
                member.with_context(|| format!("Error reading member in '{lib_path_native}'"))?;
            let member_name = String::from_utf8_lossy(member.name()).into_owned();

            // Copy into a fresh Vec so the data starts at a heap-aligned address.
            // Without the `unaligned` object crate feature, parsing fails if the member
            // happens to sit at an odd offset within the archive buffer.
            let data: Vec<u8> = member
                .data(lib_data.as_slice())
                .with_context(|| format!("Failed to read member '{member_name}'"))?
                .to_vec();

            let sigs = match generate_all_signatures_x86(&data, &member_name) {
                Ok(s) => s,
                Err(e) => {
                    log::debug!("Skipping '{member_name}': {e:?}");
                    continue;
                }
            };
            if sigs.is_empty() {
                continue;
            }
            member_count += 1;
            for (sym_name, sig) in sigs {
                let entry = by_symbol.entry(sym_name).or_default();
                if let Some(existing) = entry.get_mut(&sig.hash) {
                    compare_signature(existing, &sig).ok();
                } else {
                    entry.insert(sig.hash.clone(), sig);
                }
            }
        }

        info!("  {} object member(s) with signatures", member_count);
        total_members += member_count;
    }

    info!(
        "Processed {} total member(s), writing signatures for {} symbol(s)",
        total_members,
        by_symbol.len()
    );
    let mut written = 0u32;
    for (sym_name, hash_map) in &by_symbol {
        let mut sigs: Vec<_> = hash_map.values().cloned().collect();
        sigs.sort_by_key(|s| s.signature.len());

        let safe_name = sym_name.replace(['/', '\\', ':', '*', '?', '"', '<', '>', '|'], "_");
        let out_path = out_dir.join(format!("{safe_name}.yml"));
        let mut f = buf_writer(&out_path)?;
        serde_yaml::to_writer(&mut f, &sigs)?;
        f.flush()?;
        written += 1;
    }
    info!("Wrote {written} .yml file(s) to '{out_dir}'");
    Ok(())
}

fn signatures(args: SignaturesArgs) -> Result<()> {
    let files = process_rsp(&args.files)?;

    let mut sigs: HashMap<String, FunctionSignature> = HashMap::new();
    for path in files {
        info!("Processing {}", path);
        let sig = match generate_signature_x86(&path, &args.symbol) {
            Ok(Some(s)) => s,
            Ok(None) => continue,
            Err(e) => {
                eprintln!("Failed: {e:?}");
                continue;
            }
        };
        info!("Hash {}", sig.hash);
        if let Some(existing) = sigs.get_mut(&sig.hash) {
            compare_signature(existing, &sig)?;
        } else {
            sigs.insert(sig.hash.clone(), sig);
        }
    }

    let mut sigs: Vec<FunctionSignature> = sigs.into_values().collect();
    info!("{} unique signature(s)", sigs.len());
    sigs.sort_by_key(|s| s.signature.len());

    let mut out = buf_writer(&args.out_file)?;
    serde_yaml::to_writer(&mut out, &sigs)?;
    out.flush()?;
    Ok(())
}

fn diff(args: DiffArgs) -> Result<()> {
    log::info!("Loading {}", args.config);
    let mut config_file = open_file(&args.config, true)?;
    let config: ProjectConfig = serde_yaml::from_reader(config_file.as_mut())?;
    let object_base = find_object_base(&config)?;

    let (mut obj, image_base, _, _) = load_coff_module(&config.base, &object_base)?;
    if let Some(base) = image_base {
        apply_base_relocations(&mut obj, base)?;
    }
    if let Some(symbols_path) = &config.base.symbols {
        apply_symbols_file(&symbols_path.with_encoding(), &mut obj)?;
    }

    log::info!("Loading {}", args.exe_file);
    let linked_data =
        fs::read(args.exe_file.with_encoding()).context("Failed to read linked PE")?;
    let (linked_obj, _) = process_coff(&linked_data, "linked")?;

    let mut mismatches = 0u32;

    for (_, orig_sym) in obj.symbols.iter().filter(|(_, s)| {
        s.size > 0
            && s.section.is_some()
            && !matches!(s.kind, ObjSymbolKind::Unknown | ObjSymbolKind::Section)
            && !s.flags.is_stripped()
            && !is_auto_symbol(s)
    }) {
        let orig_section_index = orig_sym.section.unwrap();
        let orig_section = &obj.sections[orig_section_index];

        // BSS has no raw data to compare
        if orig_section.kind == crate::obj::ObjSectionKind::Bss {
            continue;
        }

        let orig_start = orig_sym.address as u32;
        let orig_end = orig_start + orig_sym.size as u32;
        let orig_data = match orig_section.data_range(orig_start, orig_end) {
            Ok(d) => d,
            Err(_) => {
                log::warn!(
                    "Symbol {} at {:#010X} extends past section boundary, skipping",
                    orig_sym.name,
                    orig_sym.address
                );
                continue;
            }
        };

        let Ok((linked_section_index, linked_section)) =
            linked_obj.sections.at_address(orig_start)
        else {
            log::error!(
                "Symbol {} (size {:#X}) at {:#010X}: no section in linked PE covers this address",
                orig_sym.name,
                orig_sym.size,
                orig_sym.address
            );
            mismatches += 1;
            continue;
        };
        let _ = linked_section_index;

        let linked_data = match linked_section.data_range(orig_start, orig_end) {
            Ok(d) => d,
            Err(_) => {
                log::error!(
                    "Symbol {} (size {:#X}) at {:#010X}: extends past linked section boundary",
                    orig_sym.name,
                    orig_sym.size,
                    orig_sym.address
                );
                mismatches += 1;
                continue;
            }
        };

        if orig_data != linked_data {
            log::error!(
                "Data mismatch for {} (type {:?}, size {:#X}) at {:#010X}",
                orig_sym.name,
                orig_sym.kind,
                orig_sym.size,
                orig_sym.address
            );
            log::error!("Original: {}", hex::encode_upper(orig_data));
            log::error!("Linked:   {}", hex::encode_upper(linked_data));
            mismatches += 1;
        }
    }

    if mismatches > 0 {
        log::error!("{} mismatch(es) found", mismatches);
        std::process::exit(1);
    }
    log::info!("OK");
    Ok(())
}

fn apply(args: ApplyArgs) -> Result<()> {
    log::info!("Loading {}", args.config);
    let mut config_file = open_file(&args.config, true)?;
    let config: ProjectConfig = serde_yaml::from_reader(config_file.as_mut())?;
    let object_base = find_object_base(&config)?;

    let (mut obj, image_base, _, _) = load_coff_module(&config.base, &object_base)?;
    if let Some(base) = image_base {
        apply_base_relocations(&mut obj, base)?;
    }

    let Some(symbols_path) = &config.base.symbols else {
        bail!("No symbols file specified in config");
    };
    let symbols_path = symbols_path.with_encoding();
    let Some(symbols_cache) = apply_symbols_file(&symbols_path, &mut obj)? else {
        bail!("Symbols file '{}' does not exist", symbols_path);
    };

    log::info!("Loading {}", args.exe_file);
    let linked_data =
        fs::read(args.exe_file.with_encoding()).context("Failed to read linked PE")?;
    let (linked_obj, _) = process_coff(&linked_data, "linked")?;

    let mut replacements: Vec<(SymbolIndex, ObjSymbol)> = vec![];
    for (orig_idx, orig_sym) in obj.symbols.iter() {
        if orig_sym.section.is_none() {
            continue;
        }
        if matches!(orig_sym.kind, ObjSymbolKind::Section) {
            continue;
        }

        let Ok((linked_section_index, _)) =
            linked_obj.sections.at_address(orig_sym.address as u32)
        else {
            log::warn!(
                "Symbol {} (type {:?}, size {:#X}) at {:#010X}: no section in linked PE",
                orig_sym.name,
                orig_sym.kind,
                orig_sym.size,
                orig_sym.address
            );
            continue;
        };

        // Find by name first, then fall back to matching kind at same address.
        let linked_sym = linked_obj
            .symbols
            .at_section_address(linked_section_index, orig_sym.address as u32)
            .find(|(_, s)| s.name == orig_sym.name)
            .or_else(|| {
                linked_obj
                    .symbols
                    .at_section_address(linked_section_index, orig_sym.address as u32)
                    .find(|(_, s)| s.kind == orig_sym.kind)
            });

        let Some((_, linked_sym)) = linked_sym else {
            log::warn!(
                "Symbol not in linked PE: {} (type {:?}, size {:#X}) at {:#010X}",
                orig_sym.name,
                orig_sym.kind,
                orig_sym.size,
                orig_sym.address
            );
            continue;
        };

        let mut updated = orig_sym.clone();
        if linked_sym.name != orig_sym.name {
            log::info!(
                "Renaming {} → {} (type {:?}) at {:#010X}",
                orig_sym.name,
                linked_sym.name,
                orig_sym.kind,
                orig_sym.address
            );
            updated.name.clone_from(&linked_sym.name);
        }
        if linked_sym.size != orig_sym.size {
            log::info!(
                "Resizing {} (type {:?}) {:#X} → {:#X} at {:#010X}",
                orig_sym.name,
                orig_sym.kind,
                orig_sym.size,
                linked_sym.size,
                orig_sym.address
            );
            updated.size = linked_sym.size;
            updated.size_known = true;
        }
        let linked_scope = linked_sym.flags.scope();
        if linked_scope != ObjSymbolScope::Unknown
            && linked_scope != orig_sym.flags.scope()
            // Don't promote an explicit Local to Global just because lld exported it
            && !(linked_scope == ObjSymbolScope::Global
                && orig_sym.flags.scope() == ObjSymbolScope::Local)
        {
            log::info!(
                "Changing scope of {} (type {:?}) {:?} → {:?} at {:#010X}",
                orig_sym.name,
                orig_sym.kind,
                orig_sym.flags.scope(),
                linked_scope,
                orig_sym.address
            );
            updated.flags.set_scope(linked_scope);
        }
        if updated != *orig_sym {
            replacements.push((orig_idx, updated));
        }
    }

    // Add symbols present in the linked PE but missing from the original.
    for (_, linked_sym) in linked_obj.symbols.iter() {
        if matches!(linked_sym.kind, ObjSymbolKind::Section | ObjSymbolKind::Unknown)
            || is_auto_symbol(linked_sym)
            || linked_sym.section.is_none()
        {
            continue;
        }
        let Ok((orig_section_index, _)) = obj.sections.at_address(linked_sym.address as u32)
        else {
            continue;
        };
        let already_present = obj
            .symbols
            .at_section_address(orig_section_index, linked_sym.address as u32)
            .any(|(_, s)| s.name == linked_sym.name || s.kind == linked_sym.kind);
        if !already_present {
            log::info!(
                "Adding {} (type {:?}, size {:#X}) at {:#010X}",
                linked_sym.name,
                linked_sym.kind,
                linked_sym.size,
                linked_sym.address
            );
            obj.symbols.add_direct(ObjSymbol {
                name: linked_sym.name.clone(),
                demangled_name: linked_sym.demangled_name.clone(),
                address: linked_sym.address,
                section: Some(orig_section_index),
                size: linked_sym.size,
                size_known: linked_sym.size_known,
                flags: linked_sym.flags,
                kind: linked_sym.kind,
                align: linked_sym.align,
                data_kind: linked_sym.data_kind,
                name_hash: linked_sym.name_hash,
                demangled_name_hash: linked_sym.demangled_name_hash,
            })?;
        }
    }

    for (idx, updated) in replacements {
        obj.symbols.replace(idx, updated)?;
    }

    write_symbols_file(&symbols_path, &obj, Some(symbols_cache))?;
    log::info!("OK");
    Ok(())
}

struct ModuleState<'a> {
    obj: ObjInfo,
    size_data: Option<crate::analysis::x86::X86FunctionSizeData>,
    pe_header: Option<PeHeaderInfo>,
    config: &'a ModuleConfig,
    symbols_cache: Option<FileReadInfo>,
    splits_cache: Option<FileReadInfo>,
    dep: Vec<Utf8NativePathBuf>,
}

fn load_coff_module(
    config: &ModuleConfig,
    object_base: &ObjectBase,
) -> Result<(ObjInfo, Option<u32>, Option<PeHeaderInfo>, Utf8NativePathBuf)> {
    let object_path = object_base.join(&config.object);
    log::debug!("Loading {}", object_path);
    let (obj, image_base, pe_header) = {
        let mut file = object_base.open(&config.object)?;
        let data = file.map()?;
        if let Some(hash_str) = &config.hash {
            verify_hash(data, hash_str)?;
        }
        let pe_header = PeHeaderInfo::parse(data);
        let (mut obj, image_base) = process_coff(data, config.name())?;
        detect_pe_symbols(&mut obj, data)?;
        (obj, image_base, pe_header)
    };
    Ok((obj, image_base, pe_header, object_path))
}

fn load_analyze_coff(
    config: &ProjectConfig,
    object_base: &ObjectBase,
) -> Result<(ObjInfo, crate::analysis::x86::X86FunctionSizeData, Option<PeHeaderInfo>, Vec<Utf8NativePathBuf>, Option<FileReadInfo>, Option<FileReadInfo>)> {
    let (mut obj, image_base, pe_header, object_path) = load_coff_module(&config.base, object_base)?;
    let mut dep = vec![object_path];

    info!("Loading and analyzing COFF/PE binary");

    // Reconstruct abs32 relocations from the PE base relocation table
    if let Some(base) = image_base {
        apply_base_relocations(&mut obj, base)?;
    }

    // Discover functions and rel32 relocations by scanning code.
    // Returns size data to be applied after RTTI runs.
    let size_data = analyze_x86_functions(&mut obj)?;

    // Apply x86 signatures for already-known symbols (entry point, named stubs).
    let sig_dir_buf: Option<Utf8NativePathBuf> = config.x86_signatures.as_ref().map(|p| p.with_encoding());
    apply_signatures_x86(&mut obj, sig_dir_buf.as_ref().map(|p| std::path::Path::new(p.as_str())))?;

    if let Some(map_path) = &config.base.map {
        let map_path = map_path.with_encoding();
        crate::util::map::apply_map_file(&map_path, &mut obj, config.common_start, config.mw_comment_version)?;
        dep.push(map_path);
    }

    let splits_cache = if let Some(splits_path) = &config.base.splits {
        let splits_path = splits_path.with_encoding();
        let cache = apply_splits_file(&splits_path, &mut obj)?;
        dep.push(splits_path);
        cache
    } else {
        None
    };

    let symbols_cache = if let Some(symbols_path) = &config.base.symbols {
        let symbols_path = symbols_path.with_encoding();
        let cache = apply_symbols_file(&symbols_path, &mut obj)?;
        dep.push(symbols_path);
        cache
    } else {
        None
    };

    // Apply block relocations from config
    for reloc in &config.base.block_relocations {
        let end = reloc.end.as_ref().map(|end| end.resolve(&obj)).transpose()?;
        match (&reloc.source, &reloc.target) {
            (Some(_), Some(_)) => bail!("Cannot specify both source and target for blocked relocation"),
            (Some(source), None) => {
                let start = source.resolve(&obj)?;
                obj.blocked_relocation_sources.insert(start, end.unwrap_or(start + 1));
            }
            (None, Some(target)) => {
                let start = target.resolve(&obj)?;
                obj.blocked_relocation_targets.insert(start, end.unwrap_or(start + 1));
            }
            (None, None) => bail!("Blocked relocation must specify either source or target"),
        }
    }

    // Apply add_relocations from config
    for reloc in &config.base.add_relocations {
        let crate::analysis::cfa::SectionAddress { section, address } =
            reloc.source.resolve(&obj)?;
        let (target_symbol, _) = match obj.symbols.by_ref(&obj.sections, &reloc.target)? {
            Some(v) => v,
            None => {
                let symbol_index = obj.symbols.add_direct(crate::obj::ObjSymbol {
                    name: reloc.target.clone(),
                    demangled_name: cwdemangle::demangle(&reloc.target, &Default::default()),
                    ..Default::default()
                })?;
                (symbol_index, &obj.symbols[symbol_index])
            }
        };
        obj.sections[section].relocations.replace(
            address,
            crate::obj::ObjReloc {
                kind: reloc.kind,
                target_symbol,
                addend: reloc.addend,
                module: None,
            },
        );
    }

    Ok((obj, size_data, pe_header, dep, splits_cache, symbols_cache))
}

fn write_if_changed(path: &Utf8NativePath, contents: &[u8]) -> Result<()> {
    if fs::metadata(path).is_ok_and(|m| m.is_file()) {
        let mut old_file = open_file(path, true)?;
        let old_data = old_file.map()?;
        if old_data.len() == contents.len() && xxh3_64(old_data) == xxh3_64(contents) {
            return Ok(());
        }
    }
    fs::write(path, contents).with_context(|| format!("Failed to write file '{path}'"))?;
    Ok(())
}

fn split_write_coff(
    module: &mut ModuleState,
    config: &ProjectConfig,
    out_dir: &Utf8NativePath,
    no_update: bool,
) -> Result<OutputModule> {
    // No relocation analysis for COFF (no PPC tracker)

    if !config.symbols_known && config.detect_objects {
        debug!("Detecting object boundaries");
        detect_objects(&mut module.obj)?;
    }

    if config.detect_strings {
        debug!("Detecting strings");
        detect_strings(&mut module.obj)?;
    }

    detect_rtti(&mut module.obj)?;

    // Apply function sizes now that all symbol-discovery passes have run.
    if let Some(size_data) = module.size_data.take() {
        compute_x86_function_sizes(&mut module.obj, size_data)?;
    }

    // Post-analysis signature scan: check all functions against the sig dir.
    let sig_dir_buf: Option<Utf8NativePathBuf> = config.x86_signatures.as_ref().map(|p| p.with_encoding());
    apply_signatures_post_x86(&mut module.obj, sig_dir_buf.as_ref().map(|p| std::path::Path::new(p.as_str())))?;

    // Deduplicate public symbol names before creating function splits.
    // Two identical functions (e.g. CRT statics) or COMDAT-folded RTTI data
    // can end up with the same public name at different addresses.  Keep the
    // first occurrence and rename duplicates so each split object has unique
    // public symbols.  Relocations use symbol indices, so the renamed symbol
    // is still reachable from all callers.
    //
    // This must run BEFORE create_function_splits so that split units use the
    // already-deduplicated names.  If it ran after, two split ranges would be
    // assigned to the same unit (creating two .text sections in one object)
    // and the renamed unit would be missing from the link order.
    {
        use std::collections::HashMap;
        let mut name_to_addr: HashMap<String, u64> = HashMap::new();
        let mut renames: Vec<(u32, String)> = Vec::new();
        for (idx, sym) in module.obj.symbols.iter() {
            match sym.kind {
                ObjSymbolKind::Section => continue,
                _ => {}
            }
            if sym.name.is_empty() {
                continue;
            }
            if sym.flags.0.contains(ObjSymbolFlags::NoExport)
                || sym.flags.0.contains(ObjSymbolFlags::Local)
            {
                continue;
            }
            match name_to_addr.entry(sym.name.clone()) {
                std::collections::hash_map::Entry::Vacant(e) => {
                    e.insert(sym.address);
                }
                std::collections::hash_map::Entry::Occupied(e) => {
                    if *e.get() != sym.address {
                        let prefix =
                            if sym.kind == ObjSymbolKind::Object { "data" } else { "fn" };
                        let generated = format!("{prefix}_{:#010x}", sym.address);
                        log::warn!(
                            "Duplicate {} name '{}' at {:#010X} (already at {:#010X}); \
                             renaming to '{generated}'",
                            prefix, sym.name, sym.address, e.get()
                        );
                        renames.push((idx, generated));
                    }
                }
            }
        }
        for (idx, new_name) in renames {
            let mut sym = module.obj.symbols[idx].clone();
            sym.name = new_name;
            sym.demangled_name = None;
            module.obj.symbols.replace(idx, sym)?;
        }
    }

    // Convert Function-kind symbols into per-function splits (mirrors DOL Tracker behaviour)
    if !config.symbols_known {
        debug!("Creating function splits");
        create_function_splits(&mut module.obj)?;
    }

    debug!("Adjusting splits");
    update_splits(&mut module.obj, config.common_start, config.fill_gaps)?;

    if !no_update {
        debug!("Writing configuration");
        if let Some(symbols_path) = &module.config.symbols {
            write_symbols_file(&symbols_path.with_encoding(), &module.obj, module.symbols_cache)?;
        }
        if let Some(splits_path) = &module.config.splits {
            write_splits_file(&splits_path.with_encoding(), &module.obj, false, module.splits_cache)?;
        }
    }

    debug!("Splitting {} objects", module.obj.link_order.len());
    let module_name = module.config.name().to_string();
    let split_objs =
        split_obj(&module.obj, Some(module_name.as_str()), config.globalize_symbols)?;

    debug!("Writing object files");
    DirBuilder::new()
        .recursive(true)
        .create(out_dir)
        .with_context(|| format!("Failed to create out dir '{out_dir}'"))?;
    let obj_dir = out_dir.join("obj");

    let entry = if module.obj.kind == ObjKind::Executable {
        module.obj.entry.and_then(|e| {
            let (section_index, _) = module.obj.sections.at_address(e as u32).ok()?;
            let symbols =
                module.obj.symbols.at_section_address(section_index, e as u32).collect_vec();
            best_match_for_reloc(symbols, ObjRelocKind::Absolute).map(|(_, s)| s.name.clone())
        })
    } else {
        None
    };

    let mut out_config = OutputModule {
        name: module_name,
        module_id: module.obj.module_id,
        ldscript: out_dir.join("args.rsp").with_unix_encoding(),
        units: Vec::with_capacity(split_objs.len()),
        entry,
        extract: Vec::with_capacity(module.config.extract.len()),
    };

    // Serialize all split objects in parallel (CPU-bound), then write serially.
    let serialized: Vec<Result<Vec<u8>>> = split_objs
        .par_iter()
        .map(|split_obj| write_coff(split_obj, config.export_all))
        .collect();

    let mut object_paths = BTreeMap::new();
    for ((unit, split_obj), out_obj) in
        module.obj.link_order.iter().zip(&split_objs).zip(serialized)
    {
        let out_obj = out_obj?;
        let obj_path = obj_path_for_unit(&unit.name);
        let out_path = obj_dir.join(&obj_path);
        if let Some(existing) = object_paths.insert(obj_path, unit) {
            bail!(
                "Duplicate object path: {} and {} both resolve to {}",
                existing.name,
                unit.name,
                out_path,
            );
        }
        out_config.units.push(OutputUnit {
            object: out_path.with_unix_encoding(),
            name: unit.name.clone(),
            autogenerated: unit.autogenerated,
            code_size: split_obj.code_size(),
            data_size: split_obj.data_size(),
        });
        if let Some(parent) = out_path.parent() {
            DirBuilder::new().recursive(true).create(parent)?;
        }
        write_if_changed(&out_path, &out_obj)?;
    }

    // Generate args.rsp (flags) and objs.rsp (object file list)
    let force_includes = module.config.force_active.clone();
    let out_dir_path = out_config.ldscript.parent().unwrap();
    let obj_dir = out_dir_path.join("obj").with_unix_encoding();
    let pe_default = PeHeaderInfo::default();
    let pe = module.pe_header.as_ref().unwrap_or(&pe_default);

    let args_string = generate_args_rsp(&module.obj, pe, &force_includes)?;
    let args_path = out_config.ldscript.with_encoding();
    write_if_changed(&args_path, args_string.as_bytes())?;

    let objs_string = generate_objs_rsp(&module.obj, &obj_dir)?;
    let objs_path = out_dir_path.join("objs.rsp").with_encoding();
    write_if_changed(&objs_path, objs_string.as_bytes())?;

    Ok(out_config)
}

fn split(args: SplitArgs) -> Result<()> {
    if let Some(jobs) = args.jobs {
        rayon::ThreadPoolBuilder::new().num_threads(jobs).build_global()?;
    }

    let command_start = Instant::now();
    info!("Loading {}", args.config);
    let mut config: ProjectConfig = {
        let mut config_file = open_file(&args.config, true)?;
        serde_yaml::from_reader(config_file.as_mut())?
    };

    let mut object_base = find_object_base(&config)?;
    if config.extract_objects && matches!(object_base, ObjectBase::Vfs(..)) {
        // For COFF, just resolve to directory base
        let target_dir = match &config.object_base {
            Some(p) => p.with_encoding(),
            None => bail!("No object base specified for VFS extraction"),
        };
        object_base = ObjectBase::Directory(target_dir);
    }

    if let Some(hash_str) = &config.base.hash {
        let mut file = object_base.open(&config.base.object)?;
        let data = file.map()?;
        verify_hash(data, hash_str)?;
    } else {
        let mut file = object_base.open(&config.base.object)?;
        let mut data = file.map()?;
        config.base.hash = Some(file_sha1_string(&mut data)?);
    }

    let out_config_path = args.out_dir.join("config.json");
    let mut dep = DepFile::new(out_config_path.clone());

    let start = Instant::now();
    let (obj, size_data, pe_header, obj_dep, splits_cache, symbols_cache) =
        load_analyze_coff(&config, &object_base)
            .with_context(|| format!("While loading '{}'", config.base.file_name()))?;
    dep.extend(obj_dep);

    let function_count = obj.symbols.by_kind(crate::obj::ObjSymbolKind::Function).count();
    let duration = start.elapsed();
    info!(
        "Analysis completed in {}.{:03}s (found {} functions)",
        duration.as_secs(),
        duration.subsec_millis(),
        function_count
    );

    // Create output directories
    DirBuilder::new().recursive(true).create(&args.out_dir)?;
    touch(&args.out_dir)?;
    let include_dir = args.out_dir.join("include");
    DirBuilder::new().recursive(true).create(&include_dir)?;
    fs::write(include_dir.join("macros.inc"), include_str!("../../assets/macros.inc"))?;

    info!("Splitting objects");
    let start = Instant::now();
    let mut module = ModuleState {
        obj,
        size_data: Some(size_data),
        pe_header,
        config: &config.base,
        symbols_cache,
        splits_cache,
        dep: Default::default(),
    };

    let out_module = split_write_coff(&mut module, &config, &args.out_dir, args.no_update)
        .with_context(|| format!("While processing '{}'", config.base.file_name()))?;

    let object_count = out_module.units.len();
    let duration = start.elapsed();
    info!(
        "Splitting completed in {}.{:03}s (wrote {} objects)",
        duration.as_secs(),
        duration.subsec_millis(),
        object_count
    );

    let out_config = OutputConfig {
        version: env!("CARGO_PKG_VERSION").to_string(),
        base: out_module,
        modules: vec![],
        links: vec![OutputLink { modules: vec![config.base.name().to_string()] }],
    };

    // Write config.json
    {
        let mut out_file = buf_writer(&out_config_path)?;
        serde_json::to_writer_pretty(&mut out_file, &out_config)?;
        out_file.flush()?;
    }

    // Write dep file
    dep.extend(module.dep);
    {
        let dep_path = args.out_dir.join("dep");
        let mut dep_file = buf_writer(&dep_path)?;
        dep.write(&mut dep_file)?;
        dep_file.flush()?;
    }

    let duration = command_start.elapsed();
    info!("Total time: {}.{:03}s", duration.as_secs(), duration.subsec_millis());
    Ok(())
}
