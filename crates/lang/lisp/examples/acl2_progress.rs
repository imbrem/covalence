//! Untrusted ACL2 corpus progress driver.
//!
//! Usage:
//! `cargo run -p covalence-lisp --features hol --example acl2_progress -- [--inventory] [--manifest] ROOT CORPUS-ID BOOK...`
//!
//! `CORPUS-ID` should pin upstream content (for example, a git revision).
//! Both ordinary includes and ACL2 `:dir :system` includes resolve within
//! `ROOT`. `--inventory` traverses and classifies without attempting proof
//! replay; its theorem counts are coverage observations, not theorem evidence.
//! Output is the deterministic `acl2-progress-v1` TSV protocol, whose `mode`
//! row prevents inventory and replay results from being conflated.

use std::path::Path;

use covalence_lisp::acl2::Acl2Session;
use covalence_lisp::book::{BookConfig, run_book_with_config};
use covalence_lisp::progress::CorpusProgress;

fn usage(program: &str) -> ! {
    eprintln!("usage: {program} [--inventory] [--manifest] ROOT CORPUS-ID BOOK [BOOK ...]");
    std::process::exit(2);
}

fn main() {
    let mut raw: Vec<_> = std::env::args().collect();
    let program = raw
        .first()
        .cloned()
        .unwrap_or_else(|| "acl2_progress".into());
    let mut inventory = false;
    let mut manifest = false;
    while let Some(option) = raw.get(1).filter(|arg| arg.starts_with("--")) {
        match option.as_str() {
            "--inventory" => inventory = true,
            "--manifest" => manifest = true,
            _ => usage(&program),
        }
        raw.remove(1);
    }
    let mut args = raw.into_iter().skip(1);
    let root = args.next().unwrap_or_else(|| usage(&program));
    let corpus = args.next().unwrap_or_else(|| usage(&program));
    let books: Vec<_> = args.collect();
    if books.is_empty() {
        usage(&program);
    }

    let root = Path::new(&root);
    let mut config = BookConfig::new(root).with_dir_root("system", root);
    let mut progress = CorpusProgress::new(corpus);
    if inventory {
        config = config.inventory_only();
        progress = progress.inventory_only();
    }
    for book in books {
        match Acl2Session::new() {
            Ok(mut session) => match run_book_with_config(&mut session, &config, &book) {
                Ok(report) => progress.record_owned_report(report),
                Err(error) => progress.record_load_error(book, error.to_string()),
            },
            Err(error) => progress.record_load_error(book, error.to_string()),
        }
    }
    if manifest {
        print!("{}", progress.to_manifest_tsv());
    } else {
        print!("{}", progress.to_tsv());
    }
}
