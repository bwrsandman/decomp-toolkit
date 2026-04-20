use anyhow::{Context, Result, bail};
use argp::FromArgs;
use typed_path::Utf8NativePathBuf;

use crate::{
    util::pef::{
        PEF_ARCH_PPC, PefContainer, PefSectionKind, parse_loader_section, process_pef,
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

pub fn run(args: Args) -> Result<()> {
    match args.command {
        SubCommand::Info(c_args) => info(c_args),
        SubCommand::Split(c_args) => split(c_args),
        SubCommand::Diff(c_args) => diff(c_args),
        SubCommand::Apply(c_args) => apply(c_args),
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

fn split(args: SplitArgs) -> Result<()> {
    // Validate input early so build systems catch config mismatches before
    // the analyser lands.
    let _ = args;
    bail!(
        "`dtk pef split` is not yet implemented. Stubs only: PEF loader section \
         (imports/exports/relocations) and PatternInitData decompression still to do."
    )
}

fn diff(args: DiffArgs) -> Result<()> {
    // Sanity: make sure the file parses.
    let mut file = open_file(&args.pef_file, true)?;
    let data = file.map()?;
    let (_obj, _) = process_pef(data, "linked").context("Parsing linked PEF")?;
    let _ = args.config;
    bail!(
        "`dtk pef diff` is not yet implemented. PEF container parse succeeded but \
         symbol comparison requires the loader-section parser."
    )
}

fn apply(args: ApplyArgs) -> Result<()> {
    let mut file = open_file(&args.pef_file, true)?;
    let data = file.map()?;
    let (_obj, _) = process_pef(data, "linked").context("Parsing linked PEF")?;
    let _ = args.config;
    bail!(
        "`dtk pef apply` is not yet implemented. PEF container parse succeeded but \
         symbol extraction requires the loader-section parser."
    )
}

fn u32_to_tag(v: u32) -> String {
    let b = v.to_be_bytes();
    if b.iter().all(|&c| (0x20..0x7F).contains(&c)) {
        String::from_utf8_lossy(&b).into_owned()
    } else {
        format!("{v:08X}")
    }
}

