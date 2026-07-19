//! Offline RFC 8259 corpus and scaling benchmark.
//!
//! ```text
//! cargo run --release -p covalence-json-api --bin json-corpus -- \
//!   --corpus path/to/JSONTestSuite/test_parsing --json
//! cargo run --release -p covalence-json-api --bin json-corpus -- \
//!   --generated 1024,16384,262144,4194304 --repetitions 10
//! ```
//!
//! Corpus names use JSONTestSuite's `y_`/`n_`/`i_` convention. This command
//! performs no downloads and excludes filesystem I/O from parser timings.

use covalence_json_api::{
    JsonNestingLimit,
    corpus::{CorpusConfig, CorpusReport, generated_corpus, load_corpus, run_corpus},
};
use std::{env, path::PathBuf, process::ExitCode};

struct Args {
    corpus: Option<PathBuf>,
    generated: Option<Vec<usize>>,
    repetitions: usize,
    nesting_limit: JsonNestingLimit,
    json: bool,
}

fn main() -> ExitCode {
    match parse_args().and_then(run) {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("json-corpus: {error}");
            ExitCode::FAILURE
        }
    }
}

fn run(args: Args) -> Result<(), String> {
    let cases = match (args.corpus, args.generated) {
        (Some(path), None) => load_corpus(&path)
            .map_err(|error| format!("cannot load {}: {error}", path.display()))?,
        (None, Some(sizes)) => generated_corpus(&sizes),
        _ => return Err("choose exactly one of --corpus DIR or --generated SIZES".into()),
    };
    if cases.is_empty() {
        return Err("the corpus contains no .json files".into());
    }
    let report = run_corpus(
        &cases,
        CorpusConfig {
            repetitions: args.repetitions,
            nesting_limit: args.nesting_limit,
        },
    );
    if args.json {
        println!("{}", report.to_json());
    } else {
        print_human(&report);
    }
    if report.mismatches == 0 {
        Ok(())
    } else {
        Err(format!("{} conformance mismatch(es)", report.mismatches))
    }
}

fn parse_args() -> Result<Args, String> {
    let mut args = env::args().skip(1);
    let mut parsed = Args {
        corpus: None,
        generated: None,
        repetitions: 5,
        nesting_limit: JsonNestingLimit::DEFAULT,
        json: false,
    };
    while let Some(argument) = args.next() {
        match argument.as_str() {
            "--corpus" => {
                parsed.corpus = Some(PathBuf::from(value(&mut args, "--corpus")?));
            }
            "--generated" => {
                let text = value(&mut args, "--generated")?;
                let sizes = text
                    .split(',')
                    .map(parse_size)
                    .collect::<Result<Vec<_>, _>>()?;
                if sizes.is_empty() {
                    return Err("--generated requires at least one size".into());
                }
                parsed.generated = Some(sizes);
            }
            "--repetitions" => {
                parsed.repetitions = value(&mut args, "--repetitions")?
                    .parse()
                    .map_err(|_| "--repetitions must be a positive integer".to_owned())?;
                if parsed.repetitions == 0 {
                    return Err("--repetitions must be positive".into());
                }
            }
            "--nesting-limit" => {
                let limit = value(&mut args, "--nesting-limit")?
                    .parse()
                    .map_err(|_| "--nesting-limit must be an integer".to_owned())?;
                parsed.nesting_limit = JsonNestingLimit::new(limit).ok_or_else(|| {
                    format!(
                        "--nesting-limit exceeds supported maximum {}",
                        JsonNestingLimit::MAX_SUPPORTED
                    )
                })?;
            }
            "--json" => parsed.json = true,
            "--help" | "-h" => return Err(usage().into()),
            other => return Err(format!("unknown argument {other:?}\n{}", usage())),
        }
    }
    Ok(parsed)
}

fn value(args: &mut impl Iterator<Item = String>, option: &str) -> Result<String, String> {
    args.next()
        .ok_or_else(|| format!("{option} requires a value"))
}

fn parse_size(text: &str) -> Result<usize, String> {
    let (digits, multiplier) = match text.as_bytes().last().copied() {
        Some(b'k' | b'K') => (&text[..text.len() - 1], 1024),
        Some(b'm' | b'M') => (&text[..text.len() - 1], 1024 * 1024),
        _ => (text, 1),
    };
    digits
        .parse::<usize>()
        .ok()
        .and_then(|value| value.checked_mul(multiplier))
        .filter(|value| *value > 0)
        .ok_or_else(|| format!("invalid generated size {text:?}"))
}

fn usage() -> &'static str {
    "usage: json-corpus (--corpus DIR | --generated 1K,16K,1M) \
     [--repetitions N] [--nesting-limit N] [--json]"
}

fn print_human(report: &CorpusReport) {
    println!(
        "JSON corpus: {} files, {} bytes, {} decoded values",
        report.files, report.bytes, report.values
    );
    println!(
        "accept/reject/mismatch: {}/{}/{}",
        report.accepted, report.rejected, report.mismatches
    );
    println!(
        "parser throughput: {:.2} MiB/s ({} repetitions)",
        report.throughput_mib_s(),
        report.repetitions
    );
    println!(
        "latency ns: min={} p50={} p95={} p99={} max={}",
        report.latency_ns.min,
        report.latency_ns.p50,
        report.latency_ns.p95,
        report.latency_ns.p99,
        report.latency_ns.max
    );
    for (expectation, class) in &report.classes {
        println!(
            "  {:14} files={} accepted={} rejected={} mismatches={}",
            expectation.as_str(),
            class.files,
            class.accepted,
            class.rejected,
            class.mismatches
        );
    }
    if !report.mismatch_files.is_empty() {
        println!("mismatches:");
        for file in &report.mismatch_files {
            println!("  {file}");
        }
    }
    println!("scaling:");
    for case in &report.cases {
        println!(
            "  {:>10} bytes  {:>8.2} MiB/s  p50 {:>10} ns  {}",
            case.bytes,
            case.throughput_mib_s(report.repetitions),
            case.latency_ns.p50,
            case.name
        );
    }
}
