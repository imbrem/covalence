//! `cov hol` — OpenTheory article and package verification on the native HOL
//! kernel backend ([`covalence_opentheory::NativeOt`]).

use std::path::PathBuf;
use std::time::Instant;

use clap::Subcommand;
use covalence_hol::traits::HolLightKernel;
use covalence_opentheory::{
    ArticleInterp, CachingUrlResolver, FileResolver, NameTable, NativeOt, OPENTHEORY_REPO,
    TheoryCache, check_theory, register_select,
};

#[derive(clap::Args)]
pub struct HolArgs {
    #[command(subcommand)]
    pub command: Option<HolCommand>,
}

#[derive(Subcommand)]
pub enum HolCommand {
    /// Check standalone OpenTheory article (`.art`) files.
    Check(CheckArgs),
    /// Check OpenTheory packages (with transitive dependencies).
    Pkg(PkgArgs),
}

#[derive(clap::Args)]
pub struct CheckArgs {
    /// Print summary statistics (theorem / assumption counts).
    #[arg(long)]
    stats: bool,

    /// Continue checking remaining files after the first failure.
    #[arg(long)]
    keep_going: bool,

    /// Article files to check (`.art`).
    files: Vec<PathBuf>,
}

#[derive(clap::Args)]
pub struct PkgArgs {
    /// Offline package directories (searched in order). Repeatable.
    #[arg(long = "dir")]
    dirs: Vec<PathBuf>,

    /// OpenTheory repository URL to fetch missing packages from.
    #[arg(long)]
    repo: Option<String>,

    /// On-disk cache directory for fetched packages.
    #[arg(long)]
    cache: Option<PathBuf>,

    /// Print per-package unsatisfied assumptions.
    #[arg(long)]
    stats: bool,

    /// Continue checking remaining packages after the first failure.
    #[arg(long)]
    keep_going: bool,

    /// Discharge OpenTheory's axiom of infinity natively (map `ind → nat` and
    /// prove it over the native naturals), so it is not left as an assumption.
    #[arg(long)]
    native_infinity: bool,

    /// Packages to check (names, with or without version suffix).
    packages: Vec<String>,
}

pub fn run(args: HolArgs) {
    match args.command {
        None => println!("cov hol (OpenTheory verification on the native HOL kernel)"),
        Some(HolCommand::Check(a)) => check(a),
        Some(HolCommand::Pkg(a)) => pkg(a),
    }
}

/// Check standalone `.art` files, each against a fresh kernel.
fn check(args: CheckArgs) {
    if args.files.is_empty() {
        eprintln!("cov hol check: no article files given");
        std::process::exit(2);
    }

    let mut failures = 0usize;
    for file in &args.files {
        let started = Instant::now();
        let text = match std::fs::read_to_string(file) {
            Ok(t) => t,
            Err(e) => {
                eprintln!("FAIL  {}  (read error: {e})", file.display());
                failures += 1;
                if args.keep_going {
                    continue;
                }
                break;
            }
        };

        let mut kernel = NativeOt::new();
        let mut names = NameTable::new();
        let interp = ArticleInterp::new(&mut kernel, &mut names);
        match interp.interpret(&text) {
            Ok(result) => {
                if args.stats {
                    println!(
                        "OK    {}  theorems={} assumptions={} ({:.2?})",
                        file.display(),
                        result.theorems.len(),
                        result.assumptions.len(),
                        started.elapsed(),
                    );
                } else {
                    println!("OK    {}", file.display());
                }
            }
            Err(e) => {
                eprintln!("FAIL  {}  {e}", file.display());
                failures += 1;
                if !args.keep_going {
                    break;
                }
            }
        }
    }

    if failures > 0 {
        eprintln!("{failures} file(s) failed");
        std::process::exit(1);
    }
}

/// Check packages (with transitive dependencies) against one shared kernel.
fn pkg(args: PkgArgs) {
    if args.packages.is_empty() {
        eprintln!("cov hol pkg: no packages given");
        std::process::exit(2);
    }

    let mut kernel = if args.native_infinity {
        NativeOt::new().with_overrides(covalence_opentheory::nat_infinity_override())
    } else {
        NativeOt::new()
    };
    let mut names = NameTable::new();
    register_select(&mut kernel, &mut names);
    let mut cache: TheoryCache<NativeOt> = TheoryCache::new();

    // A dirs-first resolver when directories are given, otherwise a fetching
    // resolver against the (default) OpenTheory repo. Combining both is not yet
    // supported by the resolver surface — dirs take precedence when present.
    let use_dirs = !args.dirs.is_empty();
    let file_resolver = FileResolver::with_dirs(args.dirs.clone());
    let url_resolver = {
        let repo = args
            .repo
            .clone()
            .unwrap_or_else(|| OPENTHEORY_REPO.to_string());
        let cache_dir = args.cache.clone().unwrap_or_else(default_cache_dir);
        CachingUrlResolver::new(cache_dir, repo)
    };

    let overall = Instant::now();
    let mut total_theorems = 0usize;
    let mut failures = 0usize;

    for package in &args.packages {
        let started = Instant::now();
        let result = if use_dirs {
            check_theory(&mut kernel, &mut names, &file_resolver, package, &mut cache)
        } else {
            check_theory(&mut kernel, &mut names, &url_resolver, package, &mut cache)
        };
        match result {
            Ok(theory) => {
                total_theorems += theory.theorems.len();
                println!(
                    "OK    {package:<24} theorems={} assumptions={} ({:.2?})",
                    theory.theorems.len(),
                    theory.assumptions.len(),
                    started.elapsed(),
                );
                if args.stats {
                    for ax in &theory.assumptions {
                        println!("        assume: {:?}", kernel.concl(ax.clone()));
                    }
                }
            }
            Err(e) => {
                eprintln!("FAIL  {package}  {e}");
                failures += 1;
                if !args.keep_going {
                    break;
                }
            }
        }
    }

    println!(
        "-- {} package(s) ok, {} theorem(s), {:.2?} total",
        args.packages.len() - failures,
        total_theorems,
        overall.elapsed(),
    );
    if failures > 0 {
        std::process::exit(1);
    }
}

/// Default cache directory for fetched OpenTheory packages.
fn default_cache_dir() -> PathBuf {
    std::env::var_os("COV_OPENTHEORY_CACHE")
        .map(PathBuf::from)
        .unwrap_or_else(|| std::env::temp_dir().join("covalence-opentheory"))
}
