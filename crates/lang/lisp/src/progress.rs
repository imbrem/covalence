//! Deterministic, untrusted progress reporting for ACL2 corpus imports.
//!
//! This module only aggregates [`crate::book::BookReport`] values. It cannot
//! create definitions or theorems, and a progress row is never proof evidence:
//! theorem numerators come exclusively from reports whose events have already
//! crossed the checked replay boundary.

use std::fmt::Write as _;

use crate::book::{
    BookReport, CompletenessCount, CompletenessLevel, CompletenessReport, SourceClosureStatus,
    UnresolvedImport,
};

/// Import capability exercised by a corpus progress run.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum ProgressMode {
    /// Execute definitions and attempt checked theorem replay.
    #[default]
    Replay,
    /// Traverse and classify events/world changes without proof replay.
    Inventory,
}

impl ProgressMode {
    fn protocol_name(self) -> &'static str {
        match self {
            Self::Replay => "replay",
            Self::Inventory => "inventory",
        }
    }
}

/// One completed or failed top-level book run.
#[derive(Clone, Debug)]
enum BookProgress {
    Report {
        path: String,
        completeness: CompletenessReport,
        blockers: Vec<UnresolvedImport>,
    },
    LoadError {
        path: String,
        reason: String,
    },
}

impl BookProgress {
    fn path(&self) -> &str {
        match self {
            Self::Report { path, .. } | Self::LoadError { path, .. } => path,
        }
    }
}

/// Aggregate progress for a pinned corpus run.
///
/// Callers supply the corpus identity because a filesystem path alone does not
/// identify upstream content. The reporter treats it as opaque display data.
#[derive(Clone, Debug, Default)]
pub struct CorpusProgress {
    corpus: String,
    mode: ProgressMode,
    books: Vec<BookProgress>,
}

impl CorpusProgress {
    /// Start a report for an audit-facing corpus identity, ideally a revision
    /// or content digest rather than a mutable checkout path.
    pub fn new(corpus: impl Into<String>) -> Self {
        Self {
            corpus: corpus.into(),
            mode: ProgressMode::Replay,
            books: Vec::new(),
        }
    }

    /// Label the run as inventory-only. Inventory rows measure frontend/world
    /// coverage and deliberately cannot satisfy theorem-completeness gates.
    #[must_use]
    pub fn inventory_only(mut self) -> Self {
        self.mode = ProgressMode::Inventory;
        self
    }

    /// Record one successfully processed top-level book.
    pub fn record_report(&mut self, report: &BookReport) {
        self.books.push(BookProgress::Report {
            path: report.path.clone(),
            completeness: report.completeness(),
            blockers: report.manifest().unresolved,
        });
    }

    /// Record a failure before a [`BookReport`] could be produced.
    pub fn record_load_error(&mut self, path: impl Into<String>, reason: impl Into<String>) {
        self.books.push(BookProgress::LoadError {
            path: path.into(),
            reason: reason.into(),
        });
    }

    /// Render the stable `acl2-progress-v1` tab-separated protocol.
    ///
    /// Rows are sorted by top-level path, independently of invocation order.
    /// Text fields use backslash escapes for `\`, tab, CR, and LF.
    pub fn to_tsv(&self) -> String {
        let mut books: Vec<_> = self.books.iter().collect();
        books.sort_by(|left, right| left.path().cmp(right.path()));

        let mut out = String::from("acl2-progress-v1\n");
        writeln!(&mut out, "corpus\t{}", escape(&self.corpus)).unwrap();
        writeln!(&mut out, "mode\t{}", self.mode.protocol_name()).unwrap();
        out.push_str(
            "columns\tbook\tpath\tlevel\tsource-closure\ttarget-events\
\ttarget-definitions\ttarget-theorems\tclosure-events\tclosure-definitions\
\tclosure-theorems\tunresolved-dependencies\tinterfaces\tlogical-green\
\tsource-green\ttarget-theorem-percent\n",
        );
        out.push_str("columns\tbook-error\tpath\treason\n");
        out.push_str("columns\tblocker\ttarget-book\tsource-book\tkind\tlabel\treason\n");
        out.push_str(
            "columns\tsummary\tbooks\tload-errors\tlogical-green\tsource-green\
\ttarget-events\ttarget-definitions\ttarget-theorems\tclosure-events\
\tclosure-definitions\tclosure-theorems\tunresolved-dependencies\tinterfaces\
\tblockers\ttarget-theorem-percent\tclosure-theorem-percent\
\tsource-green-percent\n",
        );

        let mut totals = Totals {
            books: books.len(),
            ..Totals::default()
        };
        let mut blocker_rows = Vec::new();

        for book in books {
            match book {
                BookProgress::Report {
                    path,
                    completeness,
                    blockers,
                } => {
                    totals.add(*completeness);
                    write_book_row(&mut out, path, *completeness);
                    for blocker in blockers {
                        blocker_rows.push((
                            path.as_str(),
                            blocker.book.as_str(),
                            blocker.kind.as_str(),
                            blocker.label.as_str(),
                            blocker.reason.as_str(),
                        ));
                    }
                }
                BookProgress::LoadError { path, reason } => {
                    totals.load_errors += 1;
                    writeln!(&mut out, "book-error\t{}\t{}", escape(path), escape(reason)).unwrap();
                    blocker_rows.push((
                        path.as_str(),
                        path.as_str(),
                        "load-error",
                        path.as_str(),
                        reason.as_str(),
                    ));
                }
            }
        }

        blocker_rows.sort();
        totals.blockers = blocker_rows.len();
        for (target, source, kind, label, reason) in blocker_rows {
            writeln!(
                &mut out,
                "blocker\t{}\t{}\t{}\t{}\t{}",
                escape(target),
                escape(source),
                escape(kind),
                escape(label),
                escape(reason)
            )
            .unwrap();
        }
        totals.write(&mut out);
        out
    }
}

#[derive(Clone, Copy, Debug, Default)]
struct Totals {
    books: usize,
    load_errors: usize,
    logical_green: usize,
    source_green: usize,
    target_events: CompletenessCount,
    target_definitions: CompletenessCount,
    target_theorems: CompletenessCount,
    closure_events: CompletenessCount,
    closure_definitions: CompletenessCount,
    closure_theorems: CompletenessCount,
    unresolved_dependencies: usize,
    interfaces: usize,
    blockers: usize,
}

impl Totals {
    fn add(&mut self, report: CompletenessReport) {
        self.logical_green += usize::from(report.is_logical_green_island());
        self.source_green += usize::from(report.is_green_island());
        add_count(&mut self.target_events, report.target.events);
        add_count(&mut self.target_definitions, report.target.definitions);
        add_count(&mut self.target_theorems, report.target.theorems);
        add_count(&mut self.closure_events, report.closure.events);
        add_count(&mut self.closure_definitions, report.closure.definitions);
        add_count(&mut self.closure_theorems, report.closure.theorems);
        self.unresolved_dependencies += report.closure.unresolved_dependencies;
        self.interfaces += report.closure.dependency_interfaces;
    }

    fn write(self, out: &mut String) {
        writeln!(
            out,
            "summary\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
            self.books,
            self.load_errors,
            self.logical_green,
            self.source_green,
            ratio(self.target_events),
            ratio(self.target_definitions),
            ratio(self.target_theorems),
            ratio(self.closure_events),
            ratio(self.closure_definitions),
            ratio(self.closure_theorems),
            self.unresolved_dependencies,
            self.interfaces,
            self.blockers,
            percent(self.target_theorems),
            percent(self.closure_theorems),
            percent(CompletenessCount {
                complete: self.source_green,
                total: self.books,
            })
        )
        .unwrap();
    }
}

fn add_count(total: &mut CompletenessCount, value: CompletenessCount) {
    total.complete += value.complete;
    total.total += value.total;
}

fn write_book_row(out: &mut String, path: &str, report: CompletenessReport) {
    writeln!(
        out,
        "book\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
        escape(path),
        level(report.level),
        source_closure(report.source_closure),
        ratio(report.target.events),
        ratio(report.target.definitions),
        ratio(report.target.theorems),
        ratio(report.closure.events),
        ratio(report.closure.definitions),
        ratio(report.closure.theorems),
        report.closure.unresolved_dependencies,
        report.closure.dependency_interfaces,
        usize::from(report.is_logical_green_island()),
        usize::from(report.is_green_island()),
        percent(report.target.theorems)
    )
    .unwrap();
}

fn level(level: CompletenessLevel) -> &'static str {
    match level {
        CompletenessLevel::Observed => "observed",
        CompletenessLevel::EventCompatible => "event-compatible",
        CompletenessLevel::DefinitionsComplete => "definitions-complete",
        CompletenessLevel::TheoremsComplete => "theorems-complete",
    }
}

fn source_closure(status: SourceClosureStatus) -> String {
    match status {
        SourceClosureStatus::Incomplete => "incomplete".into(),
        SourceClosureStatus::Recursive => "recursive".into(),
        SourceClosureStatus::Interfaced { verified } => format!("interfaced:{verified}"),
    }
}

fn ratio(count: CompletenessCount) -> String {
    format!("{}/{}", count.complete, count.total)
}

fn percent(count: CompletenessCount) -> String {
    if count.total == 0 {
        return "100.00".into();
    }
    format!("{:.2}", count.complete as f64 * 100.0 / count.total as f64)
}

fn escape(value: &str) -> String {
    let mut escaped = String::with_capacity(value.len());
    for character in value.chars() {
        match character {
            '\\' => escaped.push_str("\\\\"),
            '\t' => escaped.push_str("\\t"),
            '\r' => escaped.push_str("\\r"),
            '\n' => escaped.push_str("\\n"),
            other => escaped.push(other),
        }
    }
    escaped
}

#[cfg(test)]
mod tests {
    use super::CorpusProgress;
    use crate::book::{
        BookReport, DependencyInterfaceRecord, EventOutcome, EventRecord, TheoremNeutralCapability,
    };

    fn event(book: &str, kind: &str, label: &str, outcome: EventOutcome) -> EventRecord {
        EventRecord {
            book: book.into(),
            kind: kind.into(),
            label: label.into(),
            outcome,
            notes: Vec::new(),
        }
    }

    #[test]
    fn aggregation_is_sorted_and_counts_checked_theorems_only() {
        let partial = BookReport {
            path: "z-partial.lisp".into(),
            events: vec![
                event(
                    "z-partial.lisp",
                    "defun",
                    "f",
                    EventOutcome::Admitted { hyps: 1 },
                ),
                event(
                    "z-partial.lisp",
                    "defthm",
                    "f-law",
                    EventOutcome::Rejected {
                        reason: "missing\tlemma".into(),
                    },
                ),
            ],
            dependency_interfaces: Vec::new(),
        };
        let green = BookReport {
            path: "a-green.lisp".into(),
            events: vec![event(
                "a-green.lisp",
                "defthm",
                "truth",
                EventOutcome::Transported,
            )],
            dependency_interfaces: Vec::new(),
        };

        let mut progress = CorpusProgress::new("community-books@abc");
        progress.record_report(&partial);
        progress.record_report(&green);
        let output = progress.to_tsv();

        assert!(
            output.find("book\ta-green.lisp").unwrap()
                < output.find("book\tz-partial.lisp").unwrap()
        );
        assert!(
            output.contains(
                "blocker\tz-partial.lisp\tz-partial.lisp\tdefthm\tf-law\tmissing\\tlemma"
            )
        );
        assert!(output.contains(
            "summary\t2\t0\t1\t1\t2/3\t1/1\t1/2\t2/3\t1/1\t1/2\t0\t0\t1\t50.00\t50.00\t50.00"
        ));
    }

    #[test]
    fn interfaces_are_logical_but_not_source_green() {
        let report = BookReport {
            path: "target.lisp".into(),
            events: vec![
                event(
                    "target.lisp",
                    "include-book",
                    "docs",
                    EventOutcome::DependencyInterface {
                        sha256: "00".repeat(32),
                    },
                ),
                event("target.lisp", "defthm", "truth", EventOutcome::Transported),
            ],
            dependency_interfaces: vec![DependencyInterfaceRecord {
                requested_by: "target.lisp".into(),
                root: None,
                source: "docs.lisp".into(),
                sha256: "00".repeat(32),
                capability: TheoremNeutralCapability::TransparentDefsection,
                rationale: "test".into(),
            }],
        };
        let mut progress = CorpusProgress::new("pinned");
        progress.record_report(&report);

        let output = progress.to_tsv();
        assert!(output.contains(
            "book\ttarget.lisp\ttheorems-complete\tinterfaced:1\t2/2\t0/0\t1/1\t2/2\t0/0\t1/1\t0\t1\t1\t0\t100.00"
        ));
        assert!(output.contains("summary\t1\t0\t1\t0"));
    }

    #[test]
    fn load_errors_are_stable_blockers_and_text_is_escaped() {
        let mut progress = CorpusProgress::new("rev\n1");
        progress.record_load_error("missing.lisp", "not found\\outside\rroot");
        let output = progress.to_tsv();

        assert!(output.contains("corpus\trev\\n1\n"));
        assert!(output.contains("mode\treplay\n"));
        assert!(output.contains("book-error\tmissing.lisp\tnot found\\\\outside\\rroot"));
        assert!(output.contains(
            "blocker\tmissing.lisp\tmissing.lisp\tload-error\tmissing.lisp\tnot found\\\\outside\\rroot"
        ));
        assert!(output.contains(
            "summary\t1\t1\t0\t0\t0/0\t0/0\t0/0\t0/0\t0/0\t0/0\t0\t0\t1\t100.00\t100.00\t0.00"
        ));
    }

    #[test]
    fn inventory_mode_is_explicit_in_the_protocol() {
        let output = CorpusProgress::new("pinned").inventory_only().to_tsv();
        assert!(output.starts_with("acl2-progress-v1\ncorpus\tpinned\nmode\tinventory\n"));
    }
}
