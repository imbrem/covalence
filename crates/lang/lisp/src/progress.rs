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

/// Whether an event contributes to the public book world or is scoped under
/// ACL2's `local` wrapper.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NormalizedEventScope {
    /// An event exported by the requested book.
    Public,
    /// An event processed for the book's local proof context only.
    Local,
}

/// Stable identity of one normalized event in an authoritative denominator.
///
/// Outcomes and proof cost are deliberately absent: the denominator describes
/// what upstream source requires, while [`BookReport`] supplies the observed
/// outcomes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NormalizedEventIdentity {
    /// Canonical root-relative source book containing the event.
    pub book: String,
    /// Exact normalized event head.
    pub kind: String,
    /// Exact normalized event name or stable rendered label.
    pub label: String,
    /// Whether the event is public or nested under `local`.
    pub scope: NormalizedEventScope,
}

impl NormalizedEventIdentity {
    fn observed(event: &crate::book::EventRecord) -> Self {
        Self {
            book: event.book.clone(),
            kind: event.kind.clone(),
            label: event.label.clone(),
            scope: if event.kind.starts_with("local ") {
                NormalizedEventScope::Local
            } else {
                NormalizedEventScope::Public
            },
        }
    }
}

/// Hash-pinned authoritative event denominator for one upstream ACL2 book.
///
/// Constructing this value does not claim completeness. Only a successful
/// [`Self::compare`] returns [`UpstreamBookCompleteness`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PinnedNormalizedDenominator {
    revision: String,
    target_path: String,
    source_sha256: [u8; 32],
    events: Vec<NormalizedEventIdentity>,
}

impl PinnedNormalizedDenominator {
    /// Define an authoritative ordered denominator obtained from an exact
    /// upstream revision and source blob.
    pub fn new(
        revision: impl Into<String>,
        target_path: impl Into<String>,
        source_sha256: [u8; 32],
        events: Vec<NormalizedEventIdentity>,
    ) -> Self {
        Self {
            revision: revision.into(),
            target_path: target_path.into(),
            source_sha256: source_sha256.into(),
            events,
        }
    }

    /// Pinned upstream revision.
    pub fn revision(&self) -> &str {
        &self.revision
    }

    /// Canonical target-book path.
    pub fn target_path(&self) -> &str {
        &self.target_path
    }

    /// SHA-256 of the exact target source.
    pub fn source_sha256(&self) -> &[u8; 32] {
        &self.source_sha256
    }

    /// Exact ordered normalized-event identities.
    pub fn events(&self) -> &[NormalizedEventIdentity] {
        &self.events
    }

    /// Fail-closed comparison with an observed replay report.
    ///
    /// Inventory runs, non-green reports, identity drift, and revision/hash
    /// drift are all explicit rejections. The returned report is the only
    /// value in this module that claims import parity with the pinned upstream
    /// book. It remains untrusted analysis and carries no theorem authority.
    pub fn compare(
        &self,
        report: &BookReport,
        observed_revision: &str,
        observed_source_sha256: [u8; 32],
        mode: ProgressMode,
    ) -> Result<UpstreamBookCompleteness, DenominatorRejection> {
        let mut mismatches = Vec::new();
        if mode != ProgressMode::Replay {
            mismatches.push(DenominatorMismatch {
                code: DenominatorMismatchCode::InventoryMode,
                detail: DenominatorMismatchDetail::Mode {
                    expected: ProgressMode::Replay,
                    observed: mode,
                },
            });
        }
        if observed_revision != self.revision {
            mismatches.push(DenominatorMismatch {
                code: DenominatorMismatchCode::Revision,
                detail: DenominatorMismatchDetail::Text {
                    expected: self.revision.clone(),
                    observed: observed_revision.into(),
                },
            });
        }
        if report.path != self.target_path {
            mismatches.push(DenominatorMismatch {
                code: DenominatorMismatchCode::TargetPath,
                detail: DenominatorMismatchDetail::Text {
                    expected: self.target_path.clone(),
                    observed: report.path.clone(),
                },
            });
        }
        if observed_source_sha256 != self.source_sha256 {
            mismatches.push(DenominatorMismatch {
                code: DenominatorMismatchCode::SourceSha256,
                detail: DenominatorMismatchDetail::Sha256 {
                    expected: self.source_sha256,
                    observed: observed_source_sha256,
                },
            });
        }

        let completeness = report.completeness();
        if !completeness.is_green_island() {
            mismatches.push(DenominatorMismatch {
                code: DenominatorMismatchCode::ObservedNotGreen,
                detail: DenominatorMismatchDetail::Completeness(completeness),
            });
        }

        let observed_events: Vec<_> = report
            .events
            .iter()
            .filter(|event| event.book == report.path)
            .map(NormalizedEventIdentity::observed)
            .collect();
        if observed_events.len() != self.events.len() {
            mismatches.push(DenominatorMismatch {
                code: DenominatorMismatchCode::EventCount,
                detail: DenominatorMismatchDetail::Count {
                    expected: self.events.len(),
                    observed: observed_events.len(),
                },
            });
        }
        for index in 0..self.events.len().max(observed_events.len()) {
            let expected = self.events.get(index);
            let observed = observed_events.get(index);
            if expected != observed {
                mismatches.push(DenominatorMismatch {
                    code: DenominatorMismatchCode::EventIdentity,
                    detail: DenominatorMismatchDetail::Event {
                        index,
                        expected: expected.cloned(),
                        observed: observed.cloned(),
                    },
                });
            }
        }

        if mismatches.is_empty() {
            Ok(UpstreamBookCompleteness {
                denominator: self.clone(),
            })
        } else {
            Err(DenominatorRejection { mismatches })
        }
    }
}

/// Stable rejection classes for the authoritative denominator gate.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DenominatorMismatchCode {
    /// The run classified events without checked replay.
    InventoryMode,
    /// The observed checkout revision differs from the pin.
    Revision,
    /// The requested target path differs from the pin.
    TargetPath,
    /// The target source blob digest differs from the pin.
    SourceSha256,
    /// The observed report did not satisfy strict source-green completeness.
    ObservedNotGreen,
    /// The number of normalized target events differs.
    EventCount,
    /// An event's ordered identity differs or is absent on one side.
    EventIdentity,
}

/// Typed audit detail attached to a [`DenominatorMismatchCode`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DenominatorMismatchDetail {
    /// Required and observed progress modes.
    Mode {
        /// Required mode.
        expected: ProgressMode,
        /// Observed mode.
        observed: ProgressMode,
    },
    /// Required and observed textual identities.
    Text {
        /// Required identity.
        expected: String,
        /// Observed identity.
        observed: String,
    },
    /// Required and observed SHA-256 digests.
    Sha256 {
        /// Required digest.
        expected: [u8; 32],
        /// Observed digest.
        observed: [u8; 32],
    },
    /// Required and observed cardinalities.
    Count {
        /// Required count.
        expected: usize,
        /// Observed count.
        observed: usize,
    },
    /// The observed stream's fail-closed completeness summary.
    Completeness(CompletenessReport),
    /// Ordered event mismatch at one target-stream position.
    Event {
        /// Zero-based normalized target-stream position.
        index: usize,
        /// Required event, or `None` when the observation has an extra event.
        expected: Option<NormalizedEventIdentity>,
        /// Observed event, or `None` when an event is missing.
        observed: Option<NormalizedEventIdentity>,
    },
}

/// One structured reason an observed run did not match its denominator.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DenominatorMismatch {
    /// Stable mismatch class.
    pub code: DenominatorMismatchCode,
    /// Typed audit data for the mismatch.
    pub detail: DenominatorMismatchDetail,
}

/// All mismatches found in one fail-closed comparison.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DenominatorRejection {
    /// Deterministically ordered mismatches found by the comparison.
    pub mismatches: Vec<DenominatorMismatch>,
}

/// Untrusted evidence that one replay report exactly matched a pinned
/// denominator and was source-green.
///
/// Its fields are private so ordinary progress summaries cannot manufacture
/// an upstream-completeness claim. This is import audit evidence, never a
/// NativeHol theorem or permission to bypass checked replay.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct UpstreamBookCompleteness {
    denominator: PinnedNormalizedDenominator,
}

impl UpstreamBookCompleteness {
    /// The exact authoritative denominator satisfied by this report.
    pub fn denominator(&self) -> &PinnedNormalizedDenominator {
        &self.denominator
    }

    /// Whether this audit report claims exact pinned upstream import parity.
    ///
    /// This says nothing about kernel theorem authority beyond the checked
    /// outcomes already counted by the underlying [`BookReport`].
    pub const fn is_upstream_complete(&self) -> bool {
        true
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
    use super::{
        CorpusProgress, DenominatorMismatchCode, NormalizedEventIdentity, NormalizedEventScope,
        PinnedNormalizedDenominator, ProgressMode,
    };
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
    fn local_checked_theorems_are_visible_but_not_export_denominators() {
        let report = BookReport {
            path: "target.lisp".into(),
            events: vec![
                event(
                    "target.lisp",
                    "local defthm",
                    "helper",
                    EventOutcome::LocalTransported,
                ),
                event("target.lisp", "defthm", "public", EventOutcome::Transported),
            ],
            dependency_interfaces: Vec::new(),
        };

        assert_eq!(report.tally().transported, 1);
        assert_eq!(report.tally().local_transported, 1);
        assert_eq!(report.tally().skipped, 0);
        assert_eq!(report.completeness().target.theorems.total, 1);
        assert_eq!(report.completeness().target.theorems.complete, 1);

        let mut progress = CorpusProgress::new("pinned");
        progress.record_report(&report);
        let output = progress.to_tsv();
        assert!(output.contains(
            "book\ttarget.lisp\ttheorems-complete\trecursive\t2/2\t0/0\t1/1\t2/2\t0/0\t1/1\t0\t0\t1\t1\t100.00"
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

    fn pinned_green_report() -> BookReport {
        BookReport {
            path: "std/lists/append.lisp".into(),
            events: vec![
                event(
                    "std/lists/append.lisp",
                    "in-package",
                    "ACL2",
                    EventOutcome::Skipped {
                        reason: "package selected".into(),
                    },
                ),
                event(
                    "std/lists/append.lisp",
                    "defun",
                    "append",
                    EventOutcome::Admitted { hyps: 0 },
                ),
                event(
                    "std/lists/append.lisp",
                    "defthm",
                    "append-associative",
                    EventOutcome::Transported,
                ),
                event(
                    "std/lists/append.lisp",
                    "local verify-guards",
                    "append",
                    EventOutcome::Skipped {
                        reason: "local: checked".into(),
                    },
                ),
            ],
            dependency_interfaces: Vec::new(),
        }
    }

    fn pinned_denominator() -> PinnedNormalizedDenominator {
        let identity =
            |kind: &str, label: &str, scope: NormalizedEventScope| NormalizedEventIdentity {
                book: "std/lists/append.lisp".into(),
                kind: kind.into(),
                label: label.into(),
                scope,
            };
        PinnedNormalizedDenominator::new(
            "acl2-8.6@012345",
            "std/lists/append.lisp",
            [0xab; 32],
            vec![
                identity("in-package", "ACL2", NormalizedEventScope::Public),
                identity("defun", "append", NormalizedEventScope::Public),
                identity("defthm", "append-associative", NormalizedEventScope::Public),
                identity("local verify-guards", "append", NormalizedEventScope::Local),
            ],
        )
    }

    #[test]
    fn exact_replay_match_is_the_only_upstream_complete_report() {
        let denominator = pinned_denominator();
        let complete = denominator
            .compare(
                &pinned_green_report(),
                "acl2-8.6@012345",
                [0xab; 32],
                ProgressMode::Replay,
            )
            .unwrap();

        assert!(complete.is_upstream_complete());
        assert_eq!(complete.denominator(), &denominator);
        assert_eq!(complete.denominator().events().len(), 4);
        assert_eq!(
            complete.denominator().events()[3].scope,
            NormalizedEventScope::Local
        );
    }

    #[test]
    fn denominator_gate_reports_identity_mode_and_green_failures() {
        let denominator = pinned_denominator();
        let mut observed = pinned_green_report();
        observed.path = "drifted/append.lisp".into();
        for event in &mut observed.events {
            event.book = observed.path.clone();
        }
        observed.events[1].label = "append2".into();
        observed.events[2].outcome = EventOutcome::Rejected {
            reason: "proof failed".into(),
        };
        observed.events.pop();

        let rejection = denominator
            .compare(
                &observed,
                "acl2-8.6@different",
                [0xcd; 32],
                ProgressMode::Inventory,
            )
            .unwrap_err();
        let codes: Vec<_> = rejection
            .mismatches
            .iter()
            .map(|mismatch| mismatch.code)
            .collect();

        for required in [
            DenominatorMismatchCode::InventoryMode,
            DenominatorMismatchCode::Revision,
            DenominatorMismatchCode::TargetPath,
            DenominatorMismatchCode::SourceSha256,
            DenominatorMismatchCode::ObservedNotGreen,
            DenominatorMismatchCode::EventCount,
            DenominatorMismatchCode::EventIdentity,
        ] {
            assert!(
                codes.contains(&required),
                "missing rejection code {required:?}"
            );
        }
    }

    #[test]
    fn matching_inventory_and_non_green_replay_are_rejected() {
        let denominator = pinned_denominator();
        let green = pinned_green_report();
        let inventory = denominator
            .compare(
                &green,
                "acl2-8.6@012345",
                [0xab; 32],
                ProgressMode::Inventory,
            )
            .unwrap_err();
        assert_eq!(
            inventory.mismatches[0].code,
            DenominatorMismatchCode::InventoryMode
        );

        let mut non_green = green;
        non_green.events[2].outcome = EventOutcome::Rejected {
            reason: "not transported".into(),
        };
        let rejected = denominator
            .compare(
                &non_green,
                "acl2-8.6@012345",
                [0xab; 32],
                ProgressMode::Replay,
            )
            .unwrap_err();
        assert_eq!(rejected.mismatches.len(), 1);
        assert_eq!(
            rejected.mismatches[0].code,
            DenominatorMismatchCode::ObservedNotGreen
        );
    }

    #[test]
    fn missing_extra_reordered_and_scope_drift_fail_closed() {
        let compare = |denominator: &PinnedNormalizedDenominator, report: &BookReport| {
            denominator
                .compare(report, "acl2-8.6@012345", [0xab; 32], ProgressMode::Replay)
                .unwrap_err()
        };

        let mut missing = pinned_green_report();
        missing.events.pop();
        let rejection = compare(&pinned_denominator(), &missing);
        assert!(
            rejection
                .mismatches
                .iter()
                .any(|mismatch| mismatch.code == DenominatorMismatchCode::EventCount)
        );
        assert!(
            rejection
                .mismatches
                .iter()
                .any(|mismatch| mismatch.code == DenominatorMismatchCode::EventIdentity)
        );

        let mut extra = pinned_green_report();
        extra.events.push(event(
            "std/lists/append.lisp",
            "verify-guards",
            "append",
            EventOutcome::Skipped {
                reason: "checked".into(),
            },
        ));
        let rejection = compare(&pinned_denominator(), &extra);
        assert!(
            rejection
                .mismatches
                .iter()
                .any(|mismatch| mismatch.code == DenominatorMismatchCode::EventCount)
        );

        let mut reordered = pinned_green_report();
        reordered.events.swap(0, 1);
        let rejection = compare(&pinned_denominator(), &reordered);
        assert!(
            rejection
                .mismatches
                .iter()
                .any(|mismatch| mismatch.code == DenominatorMismatchCode::EventIdentity)
        );

        let mut wrong_scope = pinned_denominator();
        wrong_scope.events[3].scope = NormalizedEventScope::Public;
        let rejection = compare(&wrong_scope, &pinned_green_report());
        assert_eq!(rejection.mismatches.len(), 1);
        assert_eq!(
            rejection.mismatches[0].code,
            DenominatorMismatchCode::EventIdentity
        );
    }
}
