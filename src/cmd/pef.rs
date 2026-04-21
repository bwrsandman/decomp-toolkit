use std::{
    collections::BTreeMap,
    fs::{self, DirBuilder},
    io::Write,
    time::Instant,
};

use anyhow::{Context, Result, bail};
use argp::FromArgs;
use itertools::Itertools;
use rayon::prelude::*;
use tracing::{debug, info};
use typed_path::{Utf8NativePath, Utf8NativePathBuf};
use xxhash_rust::xxh3::xxh3_64;

use crate::{
    analysis::{
        cfa::AnalyzerState,
        objects::{detect_objects, detect_strings},
        pass::{AnalysisPass, FindSaveRestSleds, FindTRKInterruptVectorTable},
        signatures::{apply_signatures, apply_signatures_post, update_ctors_dtors},
        tracker::Tracker,
    },
    cmd::{
        dol::{
            ModuleConfig, ObjectBase, OutputConfig, OutputLink, OutputModule, OutputUnit,
            ProjectConfig, find_object_base,
        },
        shasum::file_sha1_string,
    },
    obj::{
        ObjInfo, ObjKind, ObjRelocKind, ObjSectionKind, ObjSymbol, ObjSymbolKind,
        ObjSymbolScope, SymbolIndex, best_match_for_reloc,
    },
    util::{
        config::{
            apply_splits_file, apply_symbols_file, is_auto_symbol, write_splits_file,
            write_symbols_file,
        },
        dep::DepFile,
        elf::write_elf,
        file::{FileReadInfo, buf_writer, touch, verify_hash},
        lcf::obj_path_for_unit,
        map::apply_map_file,
        pef::{
            PEF_ARCH_PPC, PefContainer, PefSectionKind, parse_loader_section, process_pef,
        },
        split::{split_obj, update_splits},
    },
    vfs::open_file,
};

#[derive(FromArgs, PartialEq, Debug)]
/// Commands for processing Classic Mac OS PowerPC PEF executables.
#[argp(subcommand, name = "pef")]
pub struct Args {
    #[argp(subcommand)]
    command: SubCommand,
}

#[derive(FromArgs, PartialEq, Debug)]
#[argp(subcommand)]
enum SubCommand {
    Info(InfoArgs),
    Split(SplitArgs),
    Diff(DiffArgs),
    Apply(ApplyArgs),
    Config(ConfigArgs),
}

#[derive(FromArgs, PartialEq, Eq, Debug)]
/// Dumps PEF file + section header table.
#[argp(subcommand, name = "info")]
pub struct InfoArgs {
    #[argp(positional, from_str_fn(crate::util::path::native_path))]
    /// input PEF file
    pef_file: Utf8NativePathBuf,
}

#[derive(FromArgs, PartialEq, Eq, Debug)]
/// Splits a PEF binary into relocatable objects.
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

#[derive(FromArgs, PartialEq, Eq, Debug)]
/// Diffs symbols in a linked PEF against the original.
#[argp(subcommand, name = "diff")]
pub struct DiffArgs {
    #[argp(positional, from_str_fn(crate::util::path::native_path))]
    /// input configuration file
    config: Utf8NativePathBuf,
    #[argp(positional, from_str_fn(crate::util::path::native_path))]
    /// linked PEF to compare against
    pef_file: Utf8NativePathBuf,
}

#[derive(FromArgs, PartialEq, Eq, Debug)]
/// Applies updated symbols from a linked PEF back to the project config.
#[argp(subcommand, name = "apply")]
pub struct ApplyArgs {
    #[argp(positional, from_str_fn(crate::util::path::native_path))]
    /// input configuration file
    config: Utf8NativePathBuf,
    #[argp(positional, from_str_fn(crate::util::path::native_path))]
    /// linked PEF to read symbols from
    pef_file: Utf8NativePathBuf,
}

#[derive(FromArgs, PartialEq, Eq, Debug)]
/// Generates a project configuration file from a PEF.
#[argp(subcommand, name = "config")]
pub struct ConfigArgs {
    #[argp(positional, from_str_fn(crate::util::path::native_path))]
    /// input PEF file
    pef_file: Utf8NativePathBuf,
    #[argp(option, short = 'o', from_str_fn(crate::util::path::native_path))]
    /// output config YAML file
    out_file: Utf8NativePathBuf,
}

pub fn run(args: Args) -> Result<()> {
    match args.command {
        SubCommand::Info(c_args) => info(c_args),
        SubCommand::Split(c_args) => split(c_args),
        SubCommand::Diff(c_args) => diff(c_args),
        SubCommand::Apply(c_args) => apply(c_args),
        SubCommand::Config(c_args) => config(c_args),
    }
}

fn info(args: InfoArgs) -> Result<()> {
    let mut file = open_file(&args.pef_file, true)?;
    let data = file.map()?;
    let container = PefContainer::parse(data)?;
    let header = &container.header;

    println!("PEF file: {}", args.pef_file);
    println!(
        "  magic:           {}{}",
        u32_to_tag(header.tag1),
        u32_to_tag(header.tag2)
    );
    let arch = match header.architecture {
        PEF_ARCH_PPC => "PowerPC (pwpc)",
        0x6D36_386B => "68K (m68k)",
        _ => "<unknown>",
    };
    println!("  architecture:    {} ({:08X})", arch, header.architecture);
    println!("  format version:  {}", header.format_version);
    println!("  date/time stamp: {:#010X}", header.date_time_stamp);
    println!("  old def version: {:#010X}", header.old_def_version);
    println!("  old imp version: {:#010X}", header.old_imp_version);
    println!("  current version: {:#010X}", header.current_version);
    println!("  section count:   {}", header.section_count);
    println!("  instantiated:    {}", header.inst_section_count);
    println!();
    println!(
        "  {:>3}  {:<16} {:<8} {:>10} {:>10} {:>10} {:>10} {:>5} {:>5}",
        "idx", "name", "kind", "defaultAddr", "totalSize", "unpackSize", "contSize", "cOff", "align"
    );
    let mut loader_range: Option<(usize, usize)> = None;
    for (idx, sh) in container.sections.iter().enumerate() {
        let name = container
            .section_names
            .get(idx)
            .and_then(|n| n.clone())
            .unwrap_or_else(|| "<unnamed>".to_string());
        let kind = sh.kind().map(PefSectionKind::short_name).unwrap_or("?");
        println!(
            "  {:>3}  {:<16} {:<8} {:>#10X} {:>#10X} {:>#10X} {:>#10X} {:>#5X} {:>5}",
            idx,
            name,
            kind,
            sh.default_address,
            sh.total_size,
            sh.unpacked_size,
            sh.container_size,
            sh.container_offset,
            sh.alignment,
        );
        if matches!(sh.kind(), Some(PefSectionKind::Loader)) {
            loader_range = Some((
                sh.container_offset as usize,
                sh.container_offset as usize + sh.container_size as usize,
            ));
        }
    }

    if let Some((lo, hi)) = loader_range {
        let (info, libs, imports, exports) = parse_loader_section(&data[lo..hi])?;
        println!();
        println!("Loader:");
        println!("  mainSection={} mainOffset={:#X}", info.main_section, info.main_offset);
        println!("  initSection={} initOffset={:#X}", info.init_section, info.init_offset);
        println!("  termSection={} termOffset={:#X}", info.term_section, info.term_offset);
        println!("  importedLibraryCount: {}", libs.len());
        println!("  totalImportedSymbolCount: {}", imports.len());
        println!("  exportedSymbolCount: {}", exports.len());
        println!();
        println!("  Imported libraries:");
        for (i, lib) in libs.iter().enumerate() {
            println!(
                "    [{:>2}] {:<32} syms={:>4} first={:>5} oldImp={:#010X} cur={:#010X} opts={:#04X}",
                i,
                lib.name,
                lib.imported_symbol_count,
                lib.first_imported_symbol,
                lib.old_imp_version,
                lib.current_version,
                lib.options
            );
        }
    }
    Ok(())
}

// -------------------- split --------------------

struct ModuleState<'a> {
    obj: ObjInfo,
    config: &'a ModuleConfig,
    symbols_cache: Option<FileReadInfo>,
    splits_cache: Option<FileReadInfo>,
    dep: Vec<Utf8NativePathBuf>,
}

fn load_pef_module(
    config: &ModuleConfig,
    object_base: &ObjectBase,
) -> Result<(ObjInfo, Utf8NativePathBuf)> {
    let object_path = object_base.join(&config.object);
    log::debug!("Loading {}", object_path);
    let obj = {
        let mut file = object_base.open(&config.object)?;
        let data = file.map()?;
        if let Some(hash_str) = &config.hash {
            verify_hash(data, hash_str)?;
        }
        let (obj, _) = process_pef(data, config.name())?;
        obj
    };
    Ok((obj, object_path))
}

fn load_analyze_pef(
    config: &ProjectConfig,
    object_base: &ObjectBase,
) -> Result<(ObjInfo, Vec<Utf8NativePathBuf>, Option<FileReadInfo>, Option<FileReadInfo>)> {
    let (mut obj, object_path) = load_pef_module(&config.base, object_base)?;
    let mut dep = vec![object_path];

    if let Some(map_path) = &config.base.map {
        let map_path = map_path.with_encoding();
        apply_map_file(&map_path, &mut obj, config.common_start, config.mw_comment_version)?;
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

    // Apply block/add relocations from config
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

    if !config.symbols_known {
        debug!("Performing signature analysis");
        apply_signatures(&mut obj)?;

        if !config.quick_analysis {
            let skip_ranges =
                config.base.skip_cfa_ranges(&obj).context("Resolving skip CFA ranges")?;
            let mut state = AnalyzerState::new(skip_ranges);
            debug!("Detecting function boundaries");
            FindSaveRestSleds::execute(&mut state, &obj)?;
            state.detect_functions(&obj)?;
            FindTRKInterruptVectorTable::execute(&mut state, &obj)?;
            state.apply(&mut obj)?;
        }

        apply_signatures_post(&mut obj)?;
    }

    update_ctors_dtors(&mut obj)?;

    Ok((obj, dep, symbols_cache, splits_cache))
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

fn split_write_pef(
    module: &mut ModuleState,
    config: &ProjectConfig,
    out_dir: &Utf8NativePath,
    no_update: bool,
) -> Result<OutputModule> {
    debug!("Performing relocation analysis");
    let mut tracker = Tracker::new(&module.obj);
    tracker.process(&module.obj)?;
    debug!("Applying relocations");
    tracker.apply(&mut module.obj, false)?;

    if !config.symbols_known && config.detect_objects {
        debug!("Detecting object boundaries");
        detect_objects(&mut module.obj)?;
    }

    if config.detect_strings {
        debug!("Detecting strings");
        detect_strings(&mut module.obj)?;
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
            best_match_for_reloc(symbols, ObjRelocKind::PpcRel24).map(|(_, s)| s.name.clone())
        })
    } else {
        None
    };

    let mut out_config = OutputModule {
        name: module_name,
        module_id: module.obj.module_id,
        // PEF linker toolchain integration is still TODO — placeholder path.
        ldscript: out_dir.join("args.rsp").with_unix_encoding(),
        units: Vec::with_capacity(split_objs.len()),
        entry,
        extract: Vec::with_capacity(module.config.extract.len()),
    };

    // Serialize all split objects in parallel (CPU-bound), then write serially.
    let serialized: Vec<Result<Vec<u8>>> = split_objs
        .par_iter()
        .map(|split_obj| write_elf(split_obj, config.export_all))
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
    let (obj, obj_dep, symbols_cache, splits_cache) =
        load_analyze_pef(&config, &object_base)
            .with_context(|| format!("While loading '{}'", config.base.file_name()))?;
    dep.extend(obj_dep);

    let function_count = obj.symbols.by_kind(ObjSymbolKind::Function).count();
    let duration = start.elapsed();
    info!(
        "Analysis completed in {}.{:03}s (found {} functions)",
        duration.as_secs(),
        duration.subsec_millis(),
        function_count
    );

    DirBuilder::new().recursive(true).create(&args.out_dir)?;
    touch(&args.out_dir)?;

    info!("Splitting objects");
    let start = Instant::now();
    let mut module = ModuleState {
        obj,
        config: &config.base,
        symbols_cache,
        splits_cache,
        dep: Default::default(),
    };

    let out_module = split_write_pef(&mut module, &config, &args.out_dir, args.no_update)
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

    {
        let mut out_file = buf_writer(&out_config_path)?;
        serde_json::to_writer_pretty(&mut out_file, &out_config)?;
        out_file.flush()?;
    }

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

// -------------------- diff / apply --------------------

fn diff(args: DiffArgs) -> Result<()> {
    log::info!("Loading {}", args.config);
    let mut config_file = open_file(&args.config, true)?;
    let config: ProjectConfig = serde_yaml::from_reader(config_file.as_mut())?;
    let object_base = find_object_base(&config)?;

    let (mut obj, _) = load_pef_module(&config.base, &object_base)?;
    if let Some(symbols_path) = &config.base.symbols {
        apply_symbols_file(&symbols_path.with_encoding(), &mut obj)?;
    }

    log::info!("Loading {}", args.pef_file);
    let mut linked_file = open_file(&args.pef_file, true)?;
    let linked_data = linked_file.map()?;
    let (linked_obj, _) = process_pef(linked_data, "linked").context("Parsing linked PEF")?;

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

        if orig_section.kind == ObjSectionKind::Bss {
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

        let Ok((_, linked_section)) = linked_obj.sections.at_address(orig_start) else {
            log::error!(
                "Symbol {} (size {:#X}) at {:#010X}: no section in linked PEF covers this address",
                orig_sym.name,
                orig_sym.size,
                orig_sym.address
            );
            mismatches += 1;
            continue;
        };

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

    let (mut obj, _) = load_pef_module(&config.base, &object_base)?;

    let Some(symbols_path) = &config.base.symbols else {
        bail!("No symbols file specified in config");
    };
    let symbols_path = symbols_path.with_encoding();
    let Some(symbols_cache) = apply_symbols_file(&symbols_path, &mut obj)? else {
        bail!("Symbols file '{}' does not exist", symbols_path);
    };

    log::info!("Loading {}", args.pef_file);
    let mut linked_file = open_file(&args.pef_file, true)?;
    let linked_data = linked_file.map()?;
    let (linked_obj, _) = process_pef(linked_data, "linked").context("Parsing linked PEF")?;

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
                "Symbol {} (type {:?}, size {:#X}) at {:#010X}: no section in linked PEF",
                orig_sym.name,
                orig_sym.kind,
                orig_sym.size,
                orig_sym.address
            );
            continue;
        };

        // CFM exports are name-based, not ordinal — prefer name match.
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
                "Symbol not in linked PEF: {} (type {:?}, size {:#X}) at {:#010X}",
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

    // Add symbols present in the linked PEF but missing from the original.
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

fn config(args: ConfigArgs) -> Result<()> {
    let mut config = ProjectConfig::default();
    let mut file = open_file(&args.pef_file, true)?;
    config.base.object = args.pef_file.with_unix_encoding();
    config.base.hash = Some(file_sha1_string(&mut file)?);
    let mut out = buf_writer(&args.out_file)?;
    serde_yaml::to_writer(&mut out, &config)?;
    out.flush()?;
    Ok(())
}

fn u32_to_tag(v: u32) -> String {
    let b = v.to_be_bytes();
    if b.iter().all(|&c| (0x20..0x7F).contains(&c)) {
        String::from_utf8_lossy(&b).into_owned()
    } else {
        format!("{v:08X}")
    }
}
