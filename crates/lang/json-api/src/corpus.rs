//! Reproducible RFC 8259 conformance and performance corpus runner.
//!
//! The runner recognizes the naming convention used by JSONTestSuite:
//! `y_*.json` must be accepted, `n_*.json` must be rejected, and `i_*.json`
//! has implementation-defined expectations. Other `.json` files are measured
//! without a conformance expectation. Corpus traversal is lexical and does not
//! follow symlinks, making repeated reports stable.
//!
//! This is host-side measurement code. Acceptance is an observation by
//! [`crate::JsonSyntaxParser`], never proof authority.

use crate::{JsonNestingLimit, JsonParseErrorKind, JsonSyntaxParser, ParsedJsonValue};
use std::{
    collections::BTreeMap,
    fs,
    hint::black_box,
    io,
    path::{Path, PathBuf},
    time::{Duration, Instant},
};

/// JSONTestSuite-style expectation inferred from a filename.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Expectation {
    Accept,
    Reject,
    Indeterminate,
    Unclassified,
}

impl Expectation {
    pub fn from_path(path: &Path) -> Self {
        match path.file_name().and_then(|name| name.to_str()) {
            Some(name) if name.starts_with("y_") => Self::Accept,
            Some(name) if name.starts_with("n_") => Self::Reject,
            Some(name) if name.starts_with("i_") => Self::Indeterminate,
            _ => Self::Unclassified,
        }
    }

    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Accept => "accept",
            Self::Reject => "reject",
            Self::Indeterminate => "indeterminate",
            Self::Unclassified => "unclassified",
        }
    }
}

/// Input collected before timed parsing.
#[derive(Clone, Debug)]
pub struct CorpusCase {
    pub name: String,
    pub bytes: Vec<u8>,
    pub expectation: Expectation,
}

/// Measurement settings.
#[derive(Clone, Copy, Debug)]
pub struct CorpusConfig {
    /// Timed parses per input. The first untimed parse determines conformance.
    pub repetitions: usize,
    pub nesting_limit: JsonNestingLimit,
}

impl Default for CorpusConfig {
    fn default() -> Self {
        Self {
            repetitions: 5,
            nesting_limit: JsonNestingLimit::DEFAULT,
        }
    }
}

#[derive(Clone, Debug, Default)]
pub struct ClassReport {
    pub files: u64,
    pub bytes: u64,
    pub accepted: u64,
    pub rejected: u64,
    pub mismatches: u64,
}

/// A deterministic aggregate report. Durations contain only parser execution;
/// directory walking and file I/O happen before measurement.
#[derive(Clone, Debug)]
pub struct CorpusReport {
    pub repetitions: usize,
    pub files: u64,
    pub bytes: u64,
    pub values: u64,
    pub accepted: u64,
    pub rejected: u64,
    pub mismatches: u64,
    pub elapsed: Duration,
    pub latency_ns: LatencyReport,
    pub classes: BTreeMap<Expectation, ClassReport>,
    pub size_buckets: BTreeMap<&'static str, BucketReport>,
    pub depth_buckets: BTreeMap<&'static str, BucketReport>,
    pub errors: BTreeMap<String, u64>,
    pub mismatch_files: Vec<String>,
    /// Per-input scaling observations in deterministic corpus order.
    pub cases: Vec<CaseReport>,
}

#[derive(Clone, Copy, Debug, Default)]
pub struct BucketReport {
    pub files: u64,
    pub bytes: u64,
    pub values: u64,
}

#[derive(Clone, Copy, Debug, Default)]
pub struct LatencyReport {
    pub min: u64,
    pub p50: u64,
    pub p95: u64,
    pub p99: u64,
    pub max: u64,
}

#[derive(Clone, Debug)]
pub struct CaseReport {
    pub name: String,
    pub expectation: Expectation,
    pub bytes: u64,
    pub values: u64,
    pub depth: usize,
    pub accepted: bool,
    pub elapsed: Duration,
    pub latency_ns: LatencyReport,
}

impl CaseReport {
    pub fn throughput_mib_s(&self, repetitions: usize) -> f64 {
        self.bytes as f64 * repetitions as f64
            / (1024.0 * 1024.0)
            / self.elapsed.as_secs_f64().max(f64::MIN_POSITIVE)
    }
}

impl CorpusReport {
    pub fn throughput_mib_s(&self) -> f64 {
        let measured_bytes = self.bytes as f64 * self.repetitions as f64;
        measured_bytes / (1024.0 * 1024.0) / self.elapsed.as_secs_f64().max(f64::MIN_POSITIVE)
    }

    /// Stable machine-readable output without adding a serialization dependency.
    pub fn to_json(&self) -> String {
        let mut out = String::new();
        out.push('{');
        field_usize(&mut out, "repetitions", self.repetitions, false);
        field_u64(&mut out, "files", self.files, true);
        field_u64(&mut out, "bytes", self.bytes, true);
        field_u64(&mut out, "values", self.values, true);
        field_u64(&mut out, "accepted", self.accepted, true);
        field_u64(&mut out, "rejected", self.rejected, true);
        field_u64(&mut out, "mismatches", self.mismatches, true);
        field_u64(&mut out, "elapsed_ns", duration_ns(self.elapsed), true);
        out.push_str(",\"throughput_mib_s\":");
        out.push_str(&format!("{:.6}", self.throughput_mib_s()));
        out.push_str(",\"latency_ns\":{");
        field_u64(&mut out, "min", self.latency_ns.min, false);
        field_u64(&mut out, "p50", self.latency_ns.p50, true);
        field_u64(&mut out, "p95", self.latency_ns.p95, true);
        field_u64(&mut out, "p99", self.latency_ns.p99, true);
        field_u64(&mut out, "max", self.latency_ns.max, true);
        out.push('}');
        out.push_str(",\"classes\":");
        write_classes(&mut out, &self.classes);
        out.push_str(",\"size_buckets\":");
        write_buckets(&mut out, &self.size_buckets);
        out.push_str(",\"depth_buckets\":");
        write_buckets(&mut out, &self.depth_buckets);
        out.push_str(",\"errors\":{");
        for (index, (kind, count)) in self.errors.iter().enumerate() {
            if index != 0 {
                out.push(',');
            }
            quoted(&mut out, kind);
            out.push(':');
            out.push_str(&count.to_string());
        }
        out.push_str("},\"mismatch_files\":[");
        for (index, file) in self.mismatch_files.iter().enumerate() {
            if index != 0 {
                out.push(',');
            }
            quoted(&mut out, file);
        }
        out.push_str("],\"cases\":[");
        for (index, case) in self.cases.iter().enumerate() {
            if index != 0 {
                out.push(',');
            }
            out.push('{');
            out.push_str("\"name\":");
            quoted(&mut out, &case.name);
            out.push_str(",\"expectation\":");
            quoted(&mut out, case.expectation.as_str());
            field_u64(&mut out, "bytes", case.bytes, true);
            field_u64(&mut out, "values", case.values, true);
            field_usize(&mut out, "depth", case.depth, true);
            out.push_str(",\"accepted\":");
            out.push_str(if case.accepted { "true" } else { "false" });
            field_u64(&mut out, "elapsed_ns", duration_ns(case.elapsed), true);
            out.push_str(",\"throughput_mib_s\":");
            out.push_str(&format!("{:.6}", case.throughput_mib_s(self.repetitions)));
            out.push_str(",\"latency_ns\":{");
            field_u64(&mut out, "min", case.latency_ns.min, false);
            field_u64(&mut out, "p50", case.latency_ns.p50, true);
            field_u64(&mut out, "p95", case.latency_ns.p95, true);
            field_u64(&mut out, "p99", case.latency_ns.p99, true);
            field_u64(&mut out, "max", case.latency_ns.max, true);
            out.push_str("}}");
        }
        out.push_str("]}");
        out
    }
}

/// Recursively load `.json` files. Files are read before timing begins.
pub fn load_corpus(root: &Path) -> io::Result<Vec<CorpusCase>> {
    let mut paths = Vec::new();
    collect_json_paths(root, root, &mut paths)?;
    paths.sort();
    paths
        .into_iter()
        .map(|path| {
            let relative = path.strip_prefix(root).unwrap_or(&path);
            Ok(CorpusCase {
                name: relative.to_string_lossy().replace('\\', "/"),
                bytes: fs::read(&path)?,
                expectation: Expectation::from_path(&path),
            })
        })
        .collect()
}

fn collect_json_paths(root: &Path, path: &Path, output: &mut Vec<PathBuf>) -> io::Result<()> {
    let metadata = fs::symlink_metadata(path)?;
    if metadata.is_file() {
        if path
            .extension()
            .is_some_and(|extension| extension == "json")
        {
            output.push(path.to_owned());
        }
        return Ok(());
    }
    if !metadata.is_dir() {
        return Ok(());
    }
    let mut children = fs::read_dir(path)?
        .map(|entry| entry.map(|entry| entry.path()))
        .collect::<io::Result<Vec<_>>>()?;
    children.sort();
    for child in children {
        collect_json_paths(root, &child, output)?;
    }
    let _ = root;
    Ok(())
}

/// Run conformance once and parser-only timing `repetitions` times per case.
pub fn run_corpus(cases: &[CorpusCase], config: CorpusConfig) -> CorpusReport {
    let repetitions = config.repetitions.max(1);
    let mut report = CorpusReport {
        repetitions,
        files: cases.len() as u64,
        bytes: 0,
        values: 0,
        accepted: 0,
        rejected: 0,
        mismatches: 0,
        elapsed: Duration::ZERO,
        latency_ns: LatencyReport::default(),
        classes: BTreeMap::new(),
        size_buckets: BTreeMap::new(),
        depth_buckets: BTreeMap::new(),
        errors: BTreeMap::new(),
        mismatch_files: Vec::new(),
        cases: Vec::with_capacity(cases.len()),
    };
    let mut latencies = Vec::with_capacity(cases.len().saturating_mul(repetitions));

    for case in cases {
        let bytes = case.bytes.len() as u64;
        report.bytes += bytes;
        let class = report.classes.entry(case.expectation).or_default();
        class.files += 1;
        class.bytes += bytes;

        let observation =
            JsonSyntaxParser.parse_diagnostic_with_limit(&case.bytes, config.nesting_limit);
        let accepted = observation.is_ok();
        if accepted {
            report.accepted += 1;
            class.accepted += 1;
        } else {
            report.rejected += 1;
            class.rejected += 1;
        }
        let mismatch = matches!(case.expectation, Expectation::Accept) && !accepted
            || matches!(case.expectation, Expectation::Reject) && accepted;
        if mismatch {
            report.mismatches += 1;
            class.mismatches += 1;
            report.mismatch_files.push(case.name.clone());
        }

        let (values, depth) = match &observation {
            Ok((value, _)) => value_shape(value),
            Err(error) => {
                *report
                    .errors
                    .entry(error_kind_name(&error.kind).to_owned())
                    .or_default() += 1;
                (0, 0)
            }
        };
        report.values += values;
        add_bucket(
            &mut report.size_buckets,
            size_bucket(case.bytes.len()),
            bytes,
            values,
        );
        add_bucket(
            &mut report.depth_buckets,
            depth_bucket(depth),
            bytes,
            values,
        );

        let mut case_elapsed = Duration::ZERO;
        let mut case_latencies = Vec::with_capacity(repetitions);
        for _ in 0..repetitions {
            let start = Instant::now();
            let result = JsonSyntaxParser
                .parse_diagnostic_with_limit(black_box(&case.bytes), config.nesting_limit);
            let _ = black_box(result);
            let elapsed = start.elapsed();
            report.elapsed += elapsed;
            case_elapsed += elapsed;
            let elapsed_ns = duration_ns(elapsed);
            latencies.push(elapsed_ns);
            case_latencies.push(elapsed_ns);
        }
        case_latencies.sort_unstable();
        report.cases.push(CaseReport {
            name: case.name.clone(),
            expectation: case.expectation,
            bytes,
            values,
            depth,
            accepted,
            elapsed: case_elapsed,
            latency_ns: latency_report(&case_latencies),
        });
    }
    latencies.sort_unstable();
    report.latency_ns = latency_report(&latencies);
    report
}

/// Deterministic valid inputs for offline demos and scaling checks.
///
/// Each requested target produces one JSON document at least that many bytes
/// long. Content includes exact decimals, escaped text, arrays, and objects.
pub fn generated_corpus(target_sizes: &[usize]) -> Vec<CorpusCase> {
    target_sizes
        .iter()
        .copied()
        .enumerate()
        .map(|(index, target)| {
            let mut bytes = format!(
                "{{\"corpus\":\"covalence\",\"index\":{index},\"rows\":["
            )
            .into_bytes();
            let mut row = 0_u64;
            while bytes.len() + 2 < target.max(2) {
                if row != 0 {
                    bytes.push(b',');
                }
                bytes.extend_from_slice(
                    format!(
                        "{{\"id\":{row},\"exact\":{row}.125e-2,\"ok\":true,\"text\":\"json\\\\nλ\"}}"
                    )
                    .as_bytes(),
                );
                row += 1;
            }
            bytes.extend_from_slice(b"]}");
            CorpusCase {
                name: format!("generated-{index:03}-{}.json", bytes.len()),
                bytes,
                expectation: Expectation::Accept,
            }
        })
        .collect()
}

fn value_shape(value: &ParsedJsonValue) -> (u64, usize) {
    match value {
        ParsedJsonValue::Array(values) => {
            let mut count = 1;
            let mut child_depth = 0;
            for value in values {
                let (child_count, depth) = value_shape(value);
                count += child_count;
                child_depth = child_depth.max(depth);
            }
            (count, child_depth + 1)
        }
        ParsedJsonValue::Object(members) => {
            let mut count = 1;
            let mut child_depth = 0;
            for member in members {
                let (child_count, depth) = value_shape(&member.value);
                count += child_count;
                child_depth = child_depth.max(depth);
            }
            (count, child_depth + 1)
        }
        _ => (1, 0),
    }
}

fn add_bucket(
    buckets: &mut BTreeMap<&'static str, BucketReport>,
    name: &'static str,
    bytes: u64,
    values: u64,
) {
    let bucket = buckets.entry(name).or_default();
    bucket.files += 1;
    bucket.bytes += bytes;
    bucket.values += values;
}

fn size_bucket(size: usize) -> &'static str {
    match size {
        0..=255 => "000_0-255B",
        256..=4095 => "001_256B-4KiB",
        4096..=65535 => "002_4-64KiB",
        65536..=1_048_575 => "003_64KiB-1MiB",
        _ => "004_1MiB+",
    }
}

fn depth_bucket(depth: usize) -> &'static str {
    match depth {
        0 => "000_scalar",
        1..=4 => "001_1-4",
        5..=16 => "002_5-16",
        17..=64 => "003_17-64",
        _ => "004_65+",
    }
}

fn error_kind_name(kind: &JsonParseErrorKind) -> &'static str {
    match kind {
        JsonParseErrorKind::ExpectedValue => "expected-value",
        JsonParseErrorKind::ExpectedByte(_) => "expected-byte",
        JsonParseErrorKind::InvalidLiteral => "invalid-literal",
        JsonParseErrorKind::InvalidNumber => "invalid-number",
        JsonParseErrorKind::InvalidUtf8 => "invalid-utf8",
        JsonParseErrorKind::InvalidEscape => "invalid-escape",
        JsonParseErrorKind::InvalidUnicodeEscape => "invalid-unicode-escape",
        JsonParseErrorKind::UnescapedControl => "unescaped-control",
        JsonParseErrorKind::DuplicateName => "duplicate-name",
        JsonParseErrorKind::TrailingInput => "trailing-input",
        JsonParseErrorKind::NestingLimitExceeded { .. } => "nesting-limit",
    }
}

fn duration_ns(duration: Duration) -> u64 {
    duration.as_nanos().min(u128::from(u64::MAX)) as u64
}

fn latency_report(sorted: &[u64]) -> LatencyReport {
    LatencyReport {
        min: sorted.first().copied().unwrap_or(0),
        p50: percentile(sorted, 50),
        p95: percentile(sorted, 95),
        p99: percentile(sorted, 99),
        max: sorted.last().copied().unwrap_or(0),
    }
}

fn percentile(sorted: &[u64], percentile: usize) -> u64 {
    if sorted.is_empty() {
        return 0;
    }
    let index = (sorted.len() - 1) * percentile / 100;
    sorted[index]
}

fn quoted(out: &mut String, value: &str) {
    out.push('"');
    for character in value.chars() {
        match character {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            character if character <= '\u{1f}' => {
                out.push_str(&format!("\\u{:04x}", character as u32));
            }
            character => out.push(character),
        }
    }
    out.push('"');
}

fn field_u64(out: &mut String, name: &str, value: u64, comma: bool) {
    if comma {
        out.push(',');
    }
    quoted(out, name);
    out.push(':');
    out.push_str(&value.to_string());
}

fn field_usize(out: &mut String, name: &str, value: usize, comma: bool) {
    field_u64(out, name, value as u64, comma);
}

fn write_classes(out: &mut String, classes: &BTreeMap<Expectation, ClassReport>) {
    out.push('{');
    for (index, (expectation, report)) in classes.iter().enumerate() {
        if index != 0 {
            out.push(',');
        }
        quoted(out, expectation.as_str());
        out.push_str(":{");
        field_u64(out, "files", report.files, false);
        field_u64(out, "bytes", report.bytes, true);
        field_u64(out, "accepted", report.accepted, true);
        field_u64(out, "rejected", report.rejected, true);
        field_u64(out, "mismatches", report.mismatches, true);
        out.push('}');
    }
    out.push('}');
}

fn write_buckets(out: &mut String, buckets: &BTreeMap<&'static str, BucketReport>) {
    out.push('{');
    for (index, (name, report)) in buckets.iter().enumerate() {
        if index != 0 {
            out.push(',');
        }
        quoted(out, name);
        out.push_str(":{");
        field_u64(out, "files", report.files, false);
        field_u64(out, "bytes", report.bytes, true);
        field_u64(out, "values", report.values, true);
        out.push('}');
    }
    out.push('}');
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn conventions_and_mismatches_are_reported() {
        let cases = vec![
            CorpusCase {
                name: "y_ok.json".into(),
                bytes: br#"{"x":1}"#.to_vec(),
                expectation: Expectation::Accept,
            },
            CorpusCase {
                name: "n_bad.json".into(),
                bytes: b"[1,]".to_vec(),
                expectation: Expectation::Reject,
            },
            CorpusCase {
                name: "y_wrong.json".into(),
                bytes: b"no".to_vec(),
                expectation: Expectation::Accept,
            },
        ];
        let report = run_corpus(
            &cases,
            CorpusConfig {
                repetitions: 1,
                ..CorpusConfig::default()
            },
        );
        assert_eq!(report.accepted, 1);
        assert_eq!(report.rejected, 2);
        assert_eq!(report.mismatches, 1);
        assert_eq!(report.values, 2);
        assert_eq!(report.mismatch_files, ["y_wrong.json"]);
    }

    #[test]
    fn generated_corpus_is_deterministic_valid_and_grows() {
        let first = generated_corpus(&[128, 4096, 65536]);
        let second = generated_corpus(&[128, 4096, 65536]);
        assert_eq!(
            first.iter().map(|case| &case.bytes).collect::<Vec<_>>(),
            second.iter().map(|case| &case.bytes).collect::<Vec<_>>()
        );
        assert!(
            first
                .windows(2)
                .all(|pair| pair[0].bytes.len() < pair[1].bytes.len())
        );
        assert_eq!(run_corpus(&first, CorpusConfig::default()).mismatches, 0);
    }

    #[test]
    fn machine_report_is_json_text_parseable_by_our_parser() {
        let report = run_corpus(&generated_corpus(&[256]), CorpusConfig::default());
        let encoded = report.to_json();
        JsonSyntaxParser
            .parse_diagnostic(encoded.as_bytes())
            .unwrap();
    }
}
