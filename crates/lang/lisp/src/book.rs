//! An honest **ACL2 book import pipeline** (`hol` feature) — read a `.lisp`
//! file of top-level ACL2 *events*, drive them through an [`Acl2Session`],
//! and tally per-event outcomes. Design:
//! `notes/vibes/lisp/acl2-book-frontend.md`.
//!
//! # The honesty invariant (the tally boundary)
//!
//! The tally NEVER claims more than the theorems actually in hand:
//!
//! - **transported** is claimed only after retrieving the stored theorem and
//!   re-checking, at the boundary, that it is **hypothesis-free** and was
//!   proved by a closed reified derivation (direct [`Acl2Proof::Certificate`]
//!   or generic [`Acl2Proof::Induction`]) projected through the soundness
//!   metatheorem to the base-HOL model. Anything else is downgraded.
//!   A checked theorem nested under `local` is reported separately as
//!   **local-checked**: it crossed the same boundary, but is not a book export
//!   and therefore never enters exported-theorem completeness counts.
//! - **admitted (in dialect)** covers installed `defun`s (kernel
//!   *hypotheses*, never axioms) and reduction-path `defthm`s (genuine kernel
//!   theorems whose hypotheses are exactly the `defun` equations used — the
//!   report says how many ride).
//! - **skipped** covers `in-package`, `include-book` dependencies (satisfied
//!   includes are themselves skips whose *contents* are tallied as their own
//!   events; missing / unconfigured `:dir` / already-included ones are
//!   recorded, never errors), `local` wrappers (contents processed, pass-1
//!   style), and theorem-neutral read-time world computation (`defconst`,
//!   `defconsts`, and evaluable `make-event`; generated events are recursively
//!   tallied with provenance) plus ordinary quasiquoted `defmacro` templates
//!   and their recursively processed expansions.
//! - **rejected** records a reason and processing continues (best-effort
//!   tally; ACL2 itself would fail certification at the first error).
//!
//! # Path confinement
//!
//! Every path — the top-level book and every `include-book` — is resolved
//! **inside an explicitly configured root**: the main book root or a named
//! [`BookConfig`] `:dir` root. Absolute paths are rejected; relative `..`
//! components (used by official x86 books) are accepted only when the
//! canonical result remains under the root that authorized it (symlink-safe).
//! The default `run_book` API authorizes only its main root.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::path::{Component, Path, PathBuf};

use covalence_hash::sha256;
use covalence_sexp::SExpr;

use crate::acl2::{Acl2Proof, Acl2Session};
use crate::acl2_api::{Acl2EventWorld, WorldEventStatus};
use crate::reader::read_book;
use crate::world::{Acl2World, GeneratedEventData};

// ============================================================================
// Errors (top-level pipeline failures — per-event failures go in the tally)
// ============================================================================

/// A book-pipeline error: the *top-level* book failed to resolve, read, or
/// parse. (Failures of individual events — including missing *included*
/// books — are recorded in the tally, not raised.)
#[derive(Debug, thiserror::Error)]
pub enum BookError {
    /// The configured book root does not resolve.
    #[error("book root `{0}` does not resolve: {1}")]
    Root(PathBuf, String),
    /// The requested book path was rejected or not found.
    #[error("book `{0}`: {1}")]
    Path(String, String),
    /// The book file could not be read.
    #[error("book `{0}`: read failed: {1}")]
    Io(PathBuf, String),
    /// The book file failed to parse.
    #[error("book `{0}`: parse failed: {1}")]
    Parse(PathBuf, String),
}

// ============================================================================
// Outcomes + the report
// ============================================================================

/// The per-event outcome classes (see the module docs for exact semantics).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EventOutcome {
    /// A `defthm` whose stored theorem is the **hypothesis-free base-HOL
    /// model equation**, proved via a closed reified derivation —
    /// re-checked at this boundary, never taken on faith.
    Transported,
    /// A checked, hypothesis-free theorem produced by the same replay
    /// boundary as [`Self::Transported`], but nested under `local` and
    /// therefore unavailable as a public export of the book.
    ///
    /// This remains distinct so audit/frontier tooling can recognize genuine
    /// checked work without adding local theorems to exported-theorem
    /// completeness numerators or denominators.
    LocalTransported,
    /// Admitted in the dialect: a `defun` installed as a kernel hypothesis,
    /// or a reduction-path `defthm` (a genuine kernel theorem; `hyps` is the
    /// number of `defun` equations riding it).
    Admitted {
        /// Number of hypotheses on the stored theorem (0 = closed).
        hyps: usize,
    },
    /// Recorded and passed over (reason says why).
    Skipped {
        /// Why the event was skipped.
        reason: String,
    },
    /// A source/generated event is represented for inventory, but still
    /// carries logical definitions or theorems that have not been replayed.
    /// This is never event-complete and therefore cannot satisfy a green gate.
    DeferredLogical {
        /// The outstanding logical work.
        reason: String,
    },
    /// A resolved include represented by a content-verified theorem-neutral
    /// interface instead of recursive source replay.
    DependencyInterface {
        /// SHA-256 of the exact dependency source accepted by the interface.
        sha256: String,
    },
    /// Rejected (reason says why); processing continued.
    Rejected {
        /// Why the event was rejected.
        reason: String,
    },
    /// A required book dependency could not be resolved.  This is distinct
    /// from an ordinary skipped include (successfully loaded or idempotent),
    /// so completeness gates never need to inspect diagnostic prose.
    UnresolvedDependency {
        /// Why the dependency could not be resolved.
        reason: String,
    },
}

/// One tallied event: where it came from, what it was, how it went.
#[derive(Clone, Debug)]
pub struct EventRecord {
    /// The book file this event came from, relative to the root (nested
    /// `include-book`s carry their own path).
    pub book: String,
    /// The event head (`defun`, `defthm`, `include-book`, …).
    pub kind: String,
    /// The event's name where it has one (`defun`/`defthm` name, included
    /// book name), else a short rendering of the form.
    pub label: String,
    /// The outcome.
    pub outcome: EventOutcome,
    /// Recorded-but-ignored extras (e.g. `defthm` `:hints`/`:rule-classes`).
    pub notes: Vec<String>,
}

/// The pipeline result: every event with its outcome, plus the summary tally.
#[derive(Clone, Debug)]
pub struct BookReport {
    /// The requested top-level book, relative to the root.
    pub path: String,
    /// Every processed event, in processing order (included books inline).
    pub events: Vec<EventRecord>,
    /// Successfully applied content-verified theorem-neutral include
    /// interfaces. These are import evidence, never theorem authority.
    pub dependency_interfaces: Vec<DependencyInterfaceRecord>,
    /// Exact source attempts in encounter order. This is untrusted importer
    /// evidence and cannot create definitions or theorems.
    pub sources: Vec<SourceRecord>,
    /// Include resolution attempts in encounter order. Classification is
    /// structured so corpus gates never need to parse diagnostic prose.
    pub includes: Vec<IncludeRecord>,
}

/// Stable root-relative identity for one ACL2 source.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct SourceIdentity {
    /// Normalized named root (`system`, never `:SYSTEM`), or `None` for the
    /// configured primary root.
    pub root: Option<String>,
    /// Normalized root-relative source path.
    pub path: String,
}

impl SourceIdentity {
    /// Construct a canonical ledger identity from an optional ACL2 root label
    /// and root-relative display path.
    pub fn new(root: Option<&str>, path: impl Into<String>) -> Self {
        Self {
            root: root.map(normalize_dir_name),
            path: normalize_interface_source(path.into()).replace('\\', "/"),
        }
    }
}

/// Why a source was consulted.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SourceRole {
    /// Requested top-level book.
    Target,
    /// Sibling ACL2 certification prelude.
    Prelude,
    /// Recursively replayed include.
    Include,
    /// Source checked against a theorem-neutral interface.
    Interface,
}

/// Structured result of one source attempt.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SourceStatus {
    /// Exact bytes were read, parsed, and replayed by the host importer.
    Replayed,
    /// Exact bytes were read and accepted by a theorem-neutral interface.
    Interface,
    /// The source could not be read.
    ReadFailed,
    /// The bytes were not valid UTF-8.
    Utf8Failed,
    /// The UTF-8 source did not parse as an ACL2 book.
    ParseFailed,
    /// Exact bytes did not match the configured interface digest.
    HashMismatch,
}

/// Untrusted evidence for one source attempt.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SourceRecord {
    /// Zero-based attempt ordinal.
    pub attempt_ordinal: usize,
    /// Stable source identity.
    pub identity: SourceIdentity,
    /// Import role.
    pub role: SourceRole,
    /// SHA-256 of the exact bytes, whenever reading succeeded.
    pub sha256: Option<[u8; 32]>,
    /// Structured outcome.
    pub status: SourceStatus,
    /// Raw diagnostic detail; never used for classification.
    pub detail: Option<String>,
}

/// Structured result of one `include-book` encounter.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IncludeStatus {
    /// The include event itself was malformed.
    Malformed,
    /// Its named `:dir` root was not configured.
    Unconfigured,
    /// No candidate source existed.
    Missing,
    /// Resolution escaped or otherwise violated path confinement.
    Refused,
    /// The resolved source had already been accepted.
    Idempotent,
    /// The resolved source was recursively replayed.
    Replayed,
    /// A theorem-neutral, exact-hash interface was applied.
    Interface,
    /// Interface bytes did not match the configured digest.
    HashMismatch,
    /// The resolved source could not be read.
    ReadFailed,
    /// The resolved source was not UTF-8 or did not parse.
    ParseFailed,
}

/// Untrusted resolution evidence for one include event.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IncludeRecord {
    /// Zero-based include encounter ordinal.
    pub encounter_ordinal: usize,
    /// Source containing the include event.
    pub requested_by: SourceIdentity,
    /// Requested book string, empty when the event was malformed.
    pub request: String,
    /// Normalized requested root, or `None` for ordinary relative lookup.
    pub root: Option<String>,
    /// Resolved source identity, when resolution succeeded.
    pub resolved: Option<SourceIdentity>,
    /// Structured outcome.
    pub status: IncludeStatus,
    /// Raw diagnostic detail; never used for classification.
    pub detail: Option<String>,
}

/// Evidence that one exact dependency source was replaced by a closed
/// theorem-neutral importer capability.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DependencyInterfaceRecord {
    /// Book containing the include event.
    pub requested_by: String,
    /// Named include root, or `None` for the main book root.
    pub root: Option<String>,
    /// Canonical root-relative source path including extension.
    pub source: String,
    /// Verified exact source SHA-256.
    pub sha256: String,
    /// Closed importer behavior used for the interface.
    pub capability: TheoremNeutralCapability,
    /// Audit-facing reason this dependency is theorem-neutral here.
    pub rationale: String,
}

/// Stable high-level classes used by large-corpus import gates.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ImportClass {
    /// A function definition event, whether executed or inventoried.
    LogicalDefinition,
    /// A theorem event, whether proved or inventoried.
    LogicalTheorem,
    /// A wrapper, include, or proof-control event.
    ProofControl,
    /// Documentation, diagnostics, guard, or host-execution control.
    ExecutionOrDocs,
    /// Computed read-time world data; never theorem authority.
    ReadTimeWorld,
    /// A rejected form or unresolved include that may affect logical meaning.
    UnresolvedLogicalDependency,
}

/// One deterministic unresolved item in an [`ImportManifest`].
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct UnresolvedImport {
    /// Source book.
    pub book: String,
    /// Event head.
    pub kind: String,
    /// Event name/label.
    pub label: String,
    /// Rejection or missing-dependency reason.
    pub reason: String,
}

/// Deterministic inventory suitable for X0/X1 corpus gates.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ImportManifest {
    /// Counts by high-level import class.
    pub classes: BTreeMap<ImportClass, usize>,
    /// Counts by exact event head.
    pub kinds: BTreeMap<String, usize>,
    /// Rejection counts by exact event head.
    pub rejections: BTreeMap<String, usize>,
    /// Sorted unresolved logical dependencies.
    pub unresolved: Vec<UnresolvedImport>,
}

/// A numerator/denominator pair for one ACL2 import stage.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct CompletenessCount {
    /// Items that completed the stage.
    pub complete: usize,
    /// Items that are required to complete the stage.
    pub total: usize,
}

impl CompletenessCount {
    /// Whether every observed requirement completed this stage.
    pub const fn is_complete(self) -> bool {
        self.complete == self.total
    }
}

/// The strongest fail-closed compatibility level reached by a book report.
///
/// These levels describe Covalence's processing of the observed event stream.
/// They deliberately do not claim parity with upstream ACL2 until a pinned
/// authoritative normalized-event denominator is supplied.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
pub enum CompletenessLevel {
    /// Some event failed or a required dependency was unresolved.
    #[default]
    Observed,
    /// Every observed event was handled and the include closure resolved.
    EventCompatible,
    /// Every observed logical definition was represented by the dialect.
    DefinitionsComplete,
    /// Every observed logical theorem became a checked, hypothesis-free
    /// NativeHol theorem.
    TheoremsComplete,
}

/// How the dependency source boundary was represented for this report.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum SourceClosureStatus {
    /// Some observed event or dependency failed, so closure is incomplete.
    #[default]
    Incomplete,
    /// Every included source was recursively traversed.
    Recursive,
    /// Logical closure used verified theorem-neutral interfaces; the number
    /// is the exact count applied during this run.
    Interfaced { verified: usize },
}

/// Structured stage counts for either the requested book or its full closure.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct CompletenessScope {
    /// All events in this scope that were handled without rejection.
    pub events: CompletenessCount,
    /// Logical definitions represented by successful admissions.
    pub definitions: CompletenessCount,
    /// Logical theorem obligations transported to closed NativeHol theorems.
    pub theorems: CompletenessCount,
    /// Required include dependencies that did not resolve.
    pub unresolved_dependencies: usize,
    /// Content-verified theorem-neutral interfaces used instead of recursive
    /// source replay.
    pub dependency_interfaces: usize,
}

impl CompletenessScope {
    const fn is_logically_complete(self) -> bool {
        self.events.is_complete()
            && self.definitions.is_complete()
            && self.theorems.is_complete()
            && self.unresolved_dependencies == 0
    }

    const fn is_source_complete(self) -> bool {
        self.is_logically_complete() && self.dependency_interfaces == 0
    }
}

/// Structured ACL2-facing completeness summary for one [`BookReport`].
///
/// This is untrusted import analysis.  In particular, it cannot create or
/// upgrade theorem authority; theorem completion is counted only from the
/// already checked [`EventOutcome::Transported`] boundary.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct CompletenessReport {
    /// Events authored by the requested book itself.  This exposes its exports
    /// independently from the often much larger dependency closure.
    pub target: CompletenessScope,
    /// All events observed while loading the requested book and its transitive
    /// include closure.
    pub closure: CompletenessScope,
    /// Strongest level reached by this observed stream.
    pub level: CompletenessLevel,
    /// Whether dependency sources were recursive, interfaced, or incomplete.
    pub source_closure: SourceClosureStatus,
}

impl CompletenessReport {
    /// Whether the logical import boundary is complete. Content-verified,
    /// theorem-neutral dependency interfaces are allowed at this boundary.
    pub const fn is_logical_green_island(self) -> bool {
        matches!(self.level, CompletenessLevel::TheoremsComplete)
            && self.target.is_logically_complete()
            && self.closure.is_logically_complete()
    }

    /// Strict green-island predicate for an observed, closed book stream.
    ///
    /// A green island has no rejected event or unresolved dependency, every
    /// definition is represented, and every theorem is transported.  This is
    /// intentionally stricter than a successful parser/linker inventory.
    pub const fn is_green_island(self) -> bool {
        matches!(self.level, CompletenessLevel::TheoremsComplete)
            && self.target.is_source_complete()
            && self.closure.is_source_complete()
    }
}

// TODO(cov:acl2.progress.cli-completeness-gate, major): Expose the same structured report through a `cov acl2` progress/import completeness gate without duplicating classification logic.

impl fmt::Display for ImportManifest {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "import classes: {:?}", self.classes)?;
        writeln!(f, "event kinds: {:?}", self.kinds)?;
        writeln!(f, "rejections by kind: {:?}", self.rejections)?;
        writeln!(
            f,
            "unresolved logical dependencies: {}",
            self.unresolved.len()
        )?;
        for item in &self.unresolved {
            writeln!(
                f,
                "  {}: ({} {}) — {}",
                item.book, item.kind, item.label, item.reason
            )?;
        }
        Ok(())
    }
}

/// The summary counts of a [`BookReport`].
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Tally {
    /// Closed base-HOL theorems transported from reified derivations.
    pub transported: usize,
    /// Closed checked theorems processed under `local`, hence not exported.
    pub local_transported: usize,
    /// Defuns installed / dialect theorems proved by reduction.
    pub admitted: usize,
    /// Recorded no-ops (`in-package`, include deps, `local`).
    pub skipped: usize,
    /// Rejections (with reasons in the event records).
    pub rejected: usize,
}

impl Tally {
    /// Total number of events.
    pub fn total(&self) -> usize {
        self.transported + self.local_transported + self.admitted + self.skipped + self.rejected
    }
}

impl BookReport {
    /// The summary tally.
    pub fn tally(&self) -> Tally {
        let mut t = Tally::default();
        for e in &self.events {
            match e.outcome {
                EventOutcome::Transported => t.transported += 1,
                EventOutcome::LocalTransported => t.local_transported += 1,
                EventOutcome::Admitted { .. } => t.admitted += 1,
                EventOutcome::Skipped { .. }
                | EventOutcome::DeferredLogical { .. }
                | EventOutcome::DependencyInterface { .. }
                | EventOutcome::UnresolvedDependency { .. } => t.skipped += 1,
                EventOutcome::Rejected { .. } => t.rejected += 1,
            }
        }
        t
    }

    /// Find the record for a named event (first match).
    pub fn event(&self, label: &str) -> Option<&EventRecord> {
        self.events.iter().find(|e| e.label == label)
    }

    /// Project the event stream into a stable, proof-cost-independent import
    /// inventory. Maps are ordered and unresolved rows are sorted.
    pub fn manifest(&self) -> ImportManifest {
        let mut out = ImportManifest::default();
        for event in &self.events {
            *out.kinds.entry(event.kind.clone()).or_default() += 1;
            let (class, unresolved) = classify_import(event);
            *out.classes.entry(class).or_default() += 1;
            if matches!(event.outcome, EventOutcome::Rejected { .. }) {
                *out.rejections.entry(event.kind.clone()).or_default() += 1;
            }
            if let Some(reason) = unresolved {
                out.unresolved.push(UnresolvedImport {
                    book: event.book.clone(),
                    kind: event.kind.clone(),
                    label: event.label.clone(),
                    reason,
                });
            }
        }
        out.unresolved.sort();
        out
    }

    /// Summarize the observed event stream as explicit compatibility,
    /// definition, and theorem stages.
    pub fn completeness(&self) -> CompletenessReport {
        let mut report = CompletenessReport::default();
        for event in &self.events {
            count_completeness_event(&mut report.closure, event);
            if event.book == self.path {
                count_completeness_event(&mut report.target, event);
            }
        }
        report.level = if !report.closure.events.is_complete()
            || report.closure.unresolved_dependencies != 0
        {
            CompletenessLevel::Observed
        } else if !report.closure.definitions.is_complete() {
            CompletenessLevel::EventCompatible
        } else if !report.closure.theorems.is_complete() {
            CompletenessLevel::DefinitionsComplete
        } else {
            CompletenessLevel::TheoremsComplete
        };
        report.source_closure = if !report.closure.events.is_complete()
            || report.closure.unresolved_dependencies != 0
        {
            SourceClosureStatus::Incomplete
        } else if report.closure.dependency_interfaces != 0 {
            SourceClosureStatus::Interfaced {
                verified: report.closure.dependency_interfaces,
            }
        } else {
            SourceClosureStatus::Recursive
        };
        report
    }
}

fn count_completeness_event(scope: &mut CompletenessScope, event: &EventRecord) {
    scope.events.total += 1;
    if !matches!(
        event.outcome,
        EventOutcome::Rejected { .. }
            | EventOutcome::DeferredLogical { .. }
            | EventOutcome::UnresolvedDependency { .. }
    ) {
        scope.events.complete += 1;
    }
    if matches!(event.outcome, EventOutcome::UnresolvedDependency { .. }) {
        scope.unresolved_dependencies += 1;
    }
    if matches!(event.outcome, EventOutcome::DependencyInterface { .. }) {
        scope.dependency_interfaces += 1;
    }
    // Count logical obligations from their source event kind, independently
    // of outcome.  A rejected theorem is still part of the denominator.
    match logical_event_class(event) {
        Some(ImportClass::LogicalDefinition) => {
            scope.definitions.total += 1;
            if matches!(event.outcome, EventOutcome::Admitted { .. }) {
                scope.definitions.complete += 1;
            }
        }
        Some(ImportClass::LogicalTheorem) => {
            scope.theorems.total += 1;
            if matches!(event.outcome, EventOutcome::Transported) {
                scope.theorems.complete += 1;
            }
        }
        _ => {}
    }
}

fn logical_event_class(event: &EventRecord) -> Option<ImportClass> {
    match event.kind.as_str() {
        "defun" | "defund" | "defun-inline" | "defund-inline" | "defun-nx" | "defn" | "define" => {
            Some(ImportClass::LogicalDefinition)
        }
        "defthm"
        | "defthmd"
        | "defrule"
        | "defruled"
        | "defrulel"
        | "defruledl"
        | "defthm-unsigned-byte-p"
        | "defthm-signed-byte-p"
        | "defthm-using-gl"
        | "def-gl-thm"
        | "local def-gl-thm"
        | "defcong"
        | "defequiv"
        | "defrefinement" => Some(ImportClass::LogicalTheorem),
        _ => None,
    }
}

fn classify_import(event: &EventRecord) -> (ImportClass, Option<String>) {
    let unresolved = match &event.outcome {
        EventOutcome::Rejected { reason } => Some(reason.clone()),
        EventOutcome::DeferredLogical { reason } => Some(reason.clone()),
        EventOutcome::UnresolvedDependency { reason } => Some(reason.clone()),
        _ => None,
    };
    if unresolved.is_some() {
        return (ImportClass::UnresolvedLogicalDependency, unresolved);
    }
    let class = if event
        .notes
        .iter()
        .any(|note| note == "no theorem authority from expansion")
    {
        ImportClass::ReadTimeWorld
    } else {
        match event.kind.as_str() {
            "defun" | "defund" | "defun-inline" | "defund-inline" | "defun-nx" | "defn"
            | "define" => ImportClass::LogicalDefinition,
            "defthm"
            | "defthmd"
            | "defrule"
            | "defruled"
            | "defrulel"
            | "defruledl"
            | "defthm-unsigned-byte-p"
            | "defthm-signed-byte-p"
            | "defthm-using-gl"
            | "def-gl-thm"
            | "local def-gl-thm"
            | "defcong"
            | "defequiv"
            | "defrefinement" => ImportClass::LogicalTheorem,
            "defconst" | "defconsts" | "make-event" | "defmacro" | "table" => {
                ImportClass::ReadTimeWorld
            }
            "in-package"
            | "verify-guards"
            | "set-inhibit-output-lst"
            | "set-inhibit-warnings"
            | "set-gag-mode"
            | "set-print-clause-ids"
            | "set-compile-fns"
            | "set-debugger-enable"
            | "assert-event"
            | "defxdoc"
            | "defxdoc+"
            | "xdoc::set-default-parents"
            | "xdoc::order-subtopics"
            | "xdoc::add-resource-directory"
            | "acl2::add-untranslate-pattern-function"
            | "acl2::optimize-untranslate-patterns"
            | "defttag"
            | "include-raw"
            | "defattach"
            | "acl2::set-raw-mode-on" => ImportClass::ExecutionOrDocs,
            "program defun" => ImportClass::ExecutionOrDocs,
            _ => ImportClass::ProofControl,
        }
    };
    (class, None)
}

impl fmt::Display for BookReport {
    /// The tally table: one line per event, then the summary.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let t = self.tally();
        writeln!(f, "book {}: {} events", self.path, t.total())?;
        for e in &self.events {
            let (tag, detail) = match &e.outcome {
                EventOutcome::Transported => (
                    "transported",
                    "closed base-HOL model theorem (reified derivation path)".to_string(),
                ),
                EventOutcome::LocalTransported => (
                    "local-checked",
                    "closed base-HOL model theorem (local, not exported)".to_string(),
                ),
                EventOutcome::Admitted { hyps: 0 } => ("admitted", "in dialect, closed".into()),
                EventOutcome::Admitted { hyps } => (
                    "admitted",
                    format!("in dialect, rides {hyps} defun hypothesis(es)"),
                ),
                EventOutcome::Skipped { reason } => ("skipped", reason.clone()),
                EventOutcome::DeferredLogical { reason } => ("DEFERRED", reason.clone()),
                EventOutcome::DependencyInterface { sha256 } => (
                    "INTERFACE",
                    format!("content-verified theorem-neutral dependency ({sha256})"),
                ),
                EventOutcome::Rejected { reason } => ("REJECTED", reason.clone()),
                EventOutcome::UnresolvedDependency { reason } => ("UNRESOLVED", reason.clone()),
            };
            write!(f, "  [{tag:^11}] ({} {}) — {detail}", e.kind, e.label)?;
            if e.book != self.path {
                write!(f, " [from {}]", e.book)?;
            }
            for n in &e.notes {
                write!(f, " [{n}]")?;
            }
            writeln!(f)?;
        }
        write!(
            f,
            "tally: {} of {} event(s) transported to closed base-HOL theorems, \
             {} local checked (not exported), {} admitted in dialect, {} skipped, {} rejected",
            t.transported,
            t.total(),
            t.local_transported,
            t.admitted,
            t.skipped,
            t.rejected
        )
    }
}

// ============================================================================
// Path confinement
// ============================================================================

/// A confined path resolution: found (canonical, inside the root), missing
/// (rejected-or-absent distinction matters — a missing *dependency* is a
/// skip, a missing *top-level book* is an error), or refused.
enum Resolved {
    Found(PathBuf),
    Missing(PathBuf),
}

/// Public configuration for book lookup.
///
/// `root` authorizes top-level books and ordinary relative `include-book`s.
/// Named roots authorize ACL2 `:dir` includes; for example,
/// `with_dir_root("system", acl2_books)` enables `:dir :system`.  A named
/// root is an additional confinement boundary, not an escape hatch: files
/// reached through it must remain below that root, including through symlinks.
#[derive(Clone, Debug)]
pub struct BookConfig {
    root: PathBuf,
    dir_roots: BTreeMap<String, PathBuf>,
    extensions: Vec<String>,
    inventory_only: bool,
    theorem_neutral_interfaces: BTreeMap<(Option<String>, String), TheoremNeutralInterface>,
    configuration_errors: Vec<String>,
}

/// Content-identified contract for an included book that contributes no
/// logical definitions or theorems to the importing book.
///
/// This is an untrusted host-import boundary: it can omit source processing,
/// but it cannot create a kernel definition or theorem. Any later reference
/// to an omitted logical symbol therefore still fails closed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TheoremNeutralInterface {
    sha256: [u8; 32],
    capability: TheoremNeutralCapability,
    rationale: String,
}

/// Closed set of importer behaviors that an include interface may rely on.
///
/// Configurations cannot invent macro semantics: every variant corresponds
/// to frontend behavior implemented and tested in this crate.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TheoremNeutralCapability {
    /// The target uses only the importer's built-in transparent `defsection`
    /// event-container semantics from this dependency.
    TransparentDefsection,
}

impl TheoremNeutralInterface {
    /// Declare the exact source digest and an audit-facing explanation.
    pub fn new(
        sha256: [u8; 32],
        capability: TheoremNeutralCapability,
        rationale: impl Into<String>,
    ) -> Self {
        Self {
            sha256,
            capability,
            rationale: rationale.into(),
        }
    }
}

impl BookConfig {
    /// Configure a root with the common ACL2/Lisp source extensions, in
    /// preference order.
    pub fn new(root: impl Into<PathBuf>) -> Self {
        Self {
            root: root.into(),
            dir_roots: BTreeMap::new(),
            extensions: vec!["lisp".into(), "lsp".into(), "acl2".into()],
            inventory_only: false,
            theorem_neutral_interfaces: BTreeMap::new(),
            configuration_errors: Vec::new(),
        }
    }

    /// Traverse and classify without admitting definitions or proving
    /// theorems. Includes and syntax classification still run normally.
    #[must_use]
    pub fn inventory_only(mut self) -> Self {
        self.inventory_only = true;
        self
    }

    /// Add an explicitly authorized `:dir` root.  `name` may be written with
    /// or without the leading colon and is matched case-insensitively.
    #[must_use]
    pub fn with_dir_root(mut self, name: impl AsRef<str>, root: impl Into<PathBuf>) -> Self {
        self.dir_roots
            .insert(normalize_dir_name(name.as_ref()), root.into());
        self
    }

    /// Represent an ordinary root-relative include through an exact,
    /// theorem-neutral source interface.
    #[must_use]
    pub fn with_theorem_neutral_interface(
        mut self,
        source: impl Into<String>,
        interface: TheoremNeutralInterface,
    ) -> Self {
        self.insert_theorem_neutral_interface(
            (None, normalize_interface_source(source.into())),
            interface,
        );
        self
    }

    /// Represent an include reached through `:dir DIR` using an exact,
    /// theorem-neutral source interface.
    #[must_use]
    pub fn with_dir_theorem_neutral_interface(
        mut self,
        dir: impl AsRef<str>,
        source: impl Into<String>,
        interface: TheoremNeutralInterface,
    ) -> Self {
        self.insert_theorem_neutral_interface(
            (
                Some(normalize_dir_name(dir.as_ref())),
                normalize_interface_source(source.into()),
            ),
            interface,
        );
        self
    }

    fn insert_theorem_neutral_interface(
        &mut self,
        key: (Option<String>, String),
        interface: TheoremNeutralInterface,
    ) {
        if let Some(previous) = self.theorem_neutral_interfaces.get(&key) {
            if previous != &interface {
                self.configuration_errors.push(format!(
                    "conflicting theorem-neutral interfaces for {:?}/{}",
                    key.0, key.1
                ));
            }
            return;
        }
        self.theorem_neutral_interfaces.insert(key, interface);
    }

    /// Replace the ordered extension search list. Leading dots are optional.
    /// An explicitly extension-bearing include is always tried as written.
    #[must_use]
    pub fn with_extensions<I, S>(mut self, extensions: I) -> Self
    where
        I: IntoIterator<Item = S>,
        S: AsRef<str>,
    {
        self.extensions = extensions
            .into_iter()
            .map(|s| s.as_ref().trim_start_matches('.').to_string())
            .filter(|s| !s.is_empty())
            .collect();
        self
    }
}

fn normalize_interface_source(mut source: String) -> String {
    while let Some(rest) = source.strip_prefix("./") {
        source = rest.to_string();
    }
    source
}

fn hex_digest(digest: &[u8; 32]) -> String {
    let mut out = String::with_capacity(64);
    for byte in digest {
        use std::fmt::Write as _;
        write!(&mut out, "{byte:02x}").expect("writing to String cannot fail");
    }
    out
}

enum InterfaceVerificationError {
    Read(String),
    Utf8 { digest: [u8; 32], detail: String },
    Parse { digest: [u8; 32], detail: String },
    Hash { actual: [u8; 32], detail: String },
}

fn verify_interface_source(
    file: &Path,
    expected: &[u8; 32],
) -> Result<[u8; 32], InterfaceVerificationError> {
    let bytes = std::fs::read(file).map_err(|error| {
        InterfaceVerificationError::Read(format!("could not read {}: {error}", file.display()))
    })?;
    let actual = sha256(&bytes);
    if &actual != expected {
        return Err(InterfaceVerificationError::Hash {
            actual,
            detail: format!(
                "SHA-256 mismatch for {}: expected {}, got {}",
                file.display(),
                hex_digest(expected),
                hex_digest(&actual)
            ),
        });
    }
    let source = std::str::from_utf8(&bytes).map_err(|error| InterfaceVerificationError::Utf8 {
        digest: actual,
        detail: format!("{} is not UTF-8 ACL2 source: {error}", file.display()),
    })?;
    read_book(source).map_err(|error| InterfaceVerificationError::Parse {
        digest: actual,
        detail: format!("{} is not readable ACL2 source: {error}", file.display()),
    })?;
    Ok(actual)
}

fn normalize_dir_name(name: &str) -> String {
    name.trim_start_matches(':').to_ascii_lowercase()
}

/// Resolve `rel` against `base_dir`, confined to `root` (both canonical):
/// reject absolute/prefixed paths, then canonicalize and require the result to
/// remain under `root` (symlink-safe). Relative `..` is valid when it stays
/// inside that boundary, as required by official x86 books.
fn confine(root: &Path, base_dir: &Path, rel: &str) -> Result<Resolved, String> {
    let p = Path::new(rel);
    if p.is_absolute() {
        return Err("absolute paths are not allowed (book paths are root-relative)".into());
    }
    if p.components().any(|c| matches!(c, Component::Prefix(_))) {
        return Err("path prefixes are not allowed (must stay inside the book root)".into());
    }
    let joined = base_dir.join(p);
    match joined.canonicalize() {
        Ok(canon) => {
            if canon.starts_with(root) {
                Ok(Resolved::Found(canon))
            } else {
                Err("path (including any `..`) resolves outside the book root".into())
            }
        }
        Err(_) => Ok(Resolved::Missing(joined)),
    }
}

/// Candidate source names. If the caller supplied an extension, preserve it;
/// otherwise probe the configured list in order.
fn source_candidates(name: &str, extensions: &[String]) -> Vec<String> {
    if Path::new(name).extension().is_some() {
        vec![name.to_string()]
    } else {
        extensions
            .iter()
            .map(|ext| format!("{name}.{ext}"))
            .collect()
    }
}

fn resolve_source(
    root: &Path,
    base_dir: &Path,
    name: &str,
    extensions: &[String],
) -> Result<Resolved, String> {
    let mut first_missing = None;
    for candidate in source_candidates(name, extensions) {
        match confine(root, base_dir, &candidate)? {
            found @ Resolved::Found(_) => return Ok(found),
            Resolved::Missing(path) => first_missing.get_or_insert(path),
        };
    }
    Ok(Resolved::Missing(
        first_missing.unwrap_or_else(|| base_dir.join(name)),
    ))
}

/// A root-relative display path (falls back to the full path).
fn display_rel(root: &Path, p: &Path) -> String {
    p.strip_prefix(root)
        .unwrap_or(p)
        .to_string_lossy()
        .into_owned()
}

// ============================================================================
// The pipeline
// ============================================================================

/// Pipeline state threaded through recursive `include-book` processing.
struct Pipeline<'s> {
    sess: &'s mut Acl2Session,
    world: Acl2World,
    root: LookupRoot,
    dir_roots: BTreeMap<String, LookupRoot>,
    extensions: Vec<String>,
    inventory_only: bool,
    theorem_neutral_interfaces: BTreeMap<(Option<String>, String), TheoremNeutralInterface>,
    applied_dependency_interfaces: Vec<DependencyInterfaceRecord>,
    sources: Vec<SourceRecord>,
    includes: Vec<IncludeRecord>,
    next_include_ordinal: usize,
    /// Current ACL2 default definition mode, changed by ordered `(program)`
    /// and `(logic)` events.
    program_mode: bool,
    macro_depth: usize,
    /// Canonical paths already included (re-inclusion is idempotent).
    seen: BTreeSet<PathBuf>,
    events: Vec<EventRecord>,
    /// Ordered semantic registry populated by accepted FTY bitstruct events.
    /// It is theorem-neutral and is used only to expand later aggregate
    /// layouts whose field widths/fixers are already known.
    bitstructs: BTreeMap<String, BitstructType>,
    /// ACL2 macro aliases map a translating macro to its logical function.
    /// Kept frontend-local so they cannot mint definitions or theorems.
    macro_aliases: BTreeMap<String, String>,
    logical_functions: BTreeSet<String>,
}

#[derive(Clone)]
struct LookupRoot {
    path: PathBuf,
    label: Option<String>,
}

#[derive(Clone)]
struct BitstructType {
    width: u32,
    fix: String,
}

#[derive(Clone)]
struct BitstructField {
    name: String,
    ty: BitstructType,
    lsb: u32,
}

/// **Run a book**: resolve `path` (a root-relative source path; the extension
/// may be omitted) inside `root`, process its events through
/// `sess`, and return the tally report. Only top-level resolution / read /
/// parse failures are `Err` — event failures are tallied.
pub fn run_book(sess: &mut Acl2Session, root: &Path, path: &str) -> Result<BookReport, BookError> {
    run_book_with_config(sess, &BookConfig::new(root), path)
}

/// Run a book with named `:dir` roots and configurable extension lookup.
pub fn run_book_with_config(
    sess: &mut Acl2Session,
    config: &BookConfig,
    path: &str,
) -> Result<BookReport, BookError> {
    // ACL2 event expansion is structurally recursive over nested terms and
    // include/event containers. Rust's test-worker stack is only a couple of
    // MiB, which is insufficient for real certified worlds such as x86isa
    // once their certification prelude unlocks generated events. Fuel still
    // bounds evaluation; this dedicated stack merely makes that existing
    // bound usable for sizeable books.
    std::thread::scope(|scope| {
        let worker = std::thread::Builder::new()
            .name("covalence-acl2-book".into())
            .stack_size(32 * 1024 * 1024)
            .spawn_scoped(scope, || run_book_with_config_inner(sess, config, path))
            .map_err(|error| BookError::Path(path.into(), error.to_string()))?;
        match worker.join() {
            Ok(result) => result,
            Err(payload) => std::panic::resume_unwind(payload),
        }
    })
}

fn run_book_with_config_inner(
    sess: &mut Acl2Session,
    config: &BookConfig,
    path: &str,
) -> Result<BookReport, BookError> {
    if let Some(error) = config.configuration_errors.first() {
        return Err(BookError::Path(
            path.into(),
            format!("invalid book configuration: {error}"),
        ));
    }
    let root = config
        .root
        .canonicalize()
        .map_err(|e| BookError::Root(config.root.clone(), e.to_string()))?;
    let mut dir_roots = BTreeMap::new();
    for (name, configured) in &config.dir_roots {
        let path = configured
            .canonicalize()
            .map_err(|e| BookError::Root(configured.clone(), e.to_string()))?;
        dir_roots.insert(
            name.clone(),
            LookupRoot {
                path,
                label: Some(format!(":{name}")),
            },
        );
    }
    let file = match resolve_source(&root, &root, path, &config.extensions) {
        Ok(Resolved::Found(f)) => f,
        Ok(Resolved::Missing(p)) => {
            return Err(BookError::Path(
                path.into(),
                format!("not found ({})", p.display()),
            ));
        }
        Err(reason) => return Err(BookError::Path(path.into(), reason)),
    };
    let mut pipe = Pipeline {
        sess,
        world: Acl2World::new(),
        root: LookupRoot {
            path: root.clone(),
            label: None,
        },
        dir_roots,
        extensions: config.extensions.clone(),
        inventory_only: config.inventory_only,
        theorem_neutral_interfaces: config.theorem_neutral_interfaces.clone(),
        applied_dependency_interfaces: Vec::new(),
        sources: Vec::new(),
        includes: Vec::new(),
        next_include_ordinal: 0,
        program_mode: false,
        macro_depth: 0,
        seen: BTreeSet::new(),
        events: Vec::new(),
        bitstructs: BTreeMap::from([
            (
                "bit".into(),
                BitstructType {
                    width: 1,
                    fix: "bfix".into(),
                },
            ),
            (
                "bitp".into(),
                BitstructType {
                    width: 1,
                    fix: "bfix".into(),
                },
            ),
        ]),
        macro_aliases: BTreeMap::new(),
        logical_functions: BTreeSet::new(),
    };
    let display = display_rel(&root, &file);
    // ACL2 certification may establish a book's initial world in a sibling
    // `NAME.acl2` prelude before reading `NAME.lisp`.  This is semantically
    // significant (x86isa/top.acl2 installs its sharp-dot constants), so a
    // source import must replay the prelude rather than infer hidden include
    // edges or start from an empty world.  The prelude remains ordinary,
    // theorem-neutral frontend input and is confined by the same root.
    let prelude = (file.extension().and_then(|ext| ext.to_str()) != Some("acl2"))
        .then(|| file.with_extension("acl2"))
        .filter(|candidate| candidate.is_file());
    if let Some(prelude) = prelude {
        let prelude = prelude
            .canonicalize()
            .map_err(|e| BookError::Io(prelude.clone(), e.to_string()))?;
        if !prelude.starts_with(&root) {
            return Err(BookError::Path(
                path.into(),
                "certification prelude resolves outside the book root".into(),
            ));
        }
        pipe.seen.insert(prelude.clone());
        let lookup = pipe.root.clone();
        pipe.process_file(&prelude, &lookup, SourceRole::Prelude)?;
    }
    pipe.seen.insert(file.clone());
    let lookup = pipe.root.clone();
    pipe.process_file(&file, &lookup, SourceRole::Target)?;
    Ok(BookReport {
        path: display,
        events: pipe.events,
        dependency_interfaces: pipe.applied_dependency_interfaces,
        sources: pipe.sources,
        includes: pipe.includes,
    })
}

impl Pipeline<'_> {
    /// Read + parse one book file and process its events in order.
    fn process_file(
        &mut self,
        file: &Path,
        lookup: &LookupRoot,
        role: SourceRole,
    ) -> Result<(), BookError> {
        let relative = display_rel(&lookup.path, file);
        let identity = SourceIdentity::new(lookup.label.as_deref(), relative.clone());
        let attempt_ordinal = self.sources.len();
        let bytes = match std::fs::read(file) {
            Ok(bytes) => bytes,
            Err(error) => {
                self.sources.push(SourceRecord {
                    attempt_ordinal,
                    identity,
                    role,
                    sha256: None,
                    status: SourceStatus::ReadFailed,
                    detail: Some(error.to_string()),
                });
                return Err(BookError::Io(file.to_path_buf(), error.to_string()));
            }
        };
        let digest = sha256(&bytes);
        let src = match std::str::from_utf8(&bytes) {
            Ok(src) => src,
            Err(error) => {
                self.sources.push(SourceRecord {
                    attempt_ordinal,
                    identity,
                    role,
                    sha256: Some(digest),
                    status: SourceStatus::Utf8Failed,
                    detail: Some(error.to_string()),
                });
                return Err(BookError::Parse(file.to_path_buf(), error.to_string()));
            }
        };
        let forms = match read_book(src) {
            Ok(forms) => forms,
            Err(error) => {
                self.sources.push(SourceRecord {
                    attempt_ordinal,
                    identity,
                    role,
                    sha256: Some(digest),
                    status: SourceStatus::ParseFailed,
                    detail: Some(error.to_string()),
                });
                return Err(BookError::Parse(file.to_path_buf(), error.to_string()));
            }
        };
        self.sources.push(SourceRecord {
            attempt_ordinal,
            identity,
            role,
            sha256: Some(digest),
            status: SourceStatus::Replayed,
            detail: None,
        });
        let book = match &lookup.label {
            Some(label) => format!("{label}/{relative}"),
            None => relative,
        };
        for form in &forms {
            let rec = self.process_event(&book, file, lookup, form)?;
            self.events.push(rec);
        }
        Ok(())
    }

    /// Classify + drive one event; the record is the tally row. Only I/O or
    /// parse failures of an *included* file propagate as `Err` (they are
    /// converted to rejections by the caller of the include, below).
    fn process_event(
        &mut self,
        book: &str,
        file: &Path,
        lookup: &LookupRoot,
        form: &SExpr,
    ) -> Result<EventRecord, BookError> {
        let rec = |kind: &str, label: String, outcome: EventOutcome| EventRecord {
            book: book.to_string(),
            kind: kind.to_string(),
            label,
            outcome,
            notes: Vec::new(),
        };
        let Some(items) = form.as_list() else {
            return Ok(rec(
                "atom",
                summarize(form),
                EventOutcome::Rejected {
                    reason: "a top-level book form must be an event list".into(),
                },
            ));
        };
        let Some(head) = items.first().and_then(SExpr::as_symbol) else {
            return Ok(rec(
                "form",
                summarize(form),
                EventOutcome::Rejected {
                    reason: "event head is not a symbol".into(),
                },
            ));
        };
        if head != "defmacro" {
            match self.world.expand_macro_call(form) {
                Ok(Some(expanded)) => {
                    return self.process_macro_call(book, file, lookup, head, form, &expanded);
                }
                Ok(None) => {}
                Err(error) => {
                    return Ok(rec(
                        head,
                        summarize(form),
                        EventOutcome::Rejected {
                            reason: format!("macro expansion failed: {error}"),
                        },
                    ));
                }
            }
        }
        match head {
            "program" | "logic" => {
                if items.len() != 1 {
                    return Ok(rec(
                        head,
                        head.into(),
                        EventOutcome::Rejected {
                            reason: format!("{head}: expected a nullary mode event"),
                        },
                    ));
                }
                self.program_mode = head == "program";
                Ok(EventRecord {
                    book: book.into(),
                    kind: head.into(),
                    label: head.into(),
                    outcome: EventOutcome::Skipped {
                        reason: format!("default definition mode changed to {head}"),
                    },
                    notes: vec![
                        "ordered admission/execution state; no theorem authority".into(),
                        format!("form: {}", render_form(form)),
                    ],
                })
            }
            "in-package" => Ok(rec(
                "in-package",
                summarize_arg(items),
                EventOutcome::Skipped {
                    reason: "single-package slice — recorded, no-op".into(),
                },
            )),
            "include-book" => self.process_include(book, file, lookup, items),
            "local" => self.process_local(book, file, lookup, items),
            "progn" | "defsection" | "acl2::with-supporters" => {
                self.process_container(book, file, lookup, head, items)
            }
            "with-output" => self.process_with_output(book, file, lookup, items),
            "progn!" => self.process_progn_bang(book, file, lookup, items),
            "encapsulate" => self.process_encapsulate(book, file, lookup, items),
            "defmacro" => self.process_defmacro(book, form, items),
            "add-macro-alias" => Ok(self.process_add_macro_alias(book, items)),
            "defconst" | "defconsts" => self.process_constant(book, head, form, items),
            "table" => {
                let label = summarize_arg(items);
                match self.world.process_world_event(form) {
                    Ok(WorldEventStatus::Handled) => Ok(EventRecord {
                        book: book.into(),
                        kind: head.into(),
                        label,
                        outcome: EventOutcome::Skipped {
                            reason: "ordered ACL2 table update recorded".into(),
                        },
                        notes: vec![
                            "table state grants no theorem authority".into(),
                            format!("form: {}", render_form(form)),
                        ],
                    }),
                    Ok(WorldEventStatus::Unhandled) => Ok(rec(
                        head,
                        label,
                        EventOutcome::Rejected {
                            reason: "table event was not recognized by the ACL2 world".into(),
                        },
                    )),
                    Err(error) => Ok(rec(
                        head,
                        label,
                        EventOutcome::Rejected {
                            reason: format!("table update rejected: {error}"),
                        },
                    )),
                }
            }
            "make-event" => self.process_make_event(book, file, lookup, form, items),
            "more-returns" | "std::more-returns" => {
                self.process_more_returns(book, file, lookup, head, items)
            }
            "assert-event" if self.inventory_only => Ok(EventRecord {
                book: book.into(),
                kind: "assert-event".into(),
                label: items
                    .get(1)
                    .map(summarize)
                    .unwrap_or_else(|| "assert-event".into()),
                outcome: EventOutcome::Rejected {
                    reason: "assert-event is not evaluated in bounded inventory mode".into(),
                },
                notes: vec![
                    "fail-closed: potentially unbounded execution assertion".into(),
                    "no theorem authority".into(),
                    format!("form: {}", render_form(form)),
                ],
            }),
            "assert-event" => Ok(self.process_assert_event(book, form, items)),
            "define" => self.process_define(book, file, lookup, items),
            "defun" | "defund" | "defun-inline" | "defund-inline" | "defun-nx" | "defn" => {
                let label = event_name(items);
                if let Err(error) = self.world.process_world_event(form) {
                    return Ok(rec(
                        head,
                        label,
                        EventOutcome::Rejected {
                            reason: format!("read-time function installation failed: {error}"),
                        },
                    ));
                }
                if self.program_mode {
                    return Ok(EventRecord {
                        book: book.into(),
                        kind: "program defun".into(),
                        label,
                        outcome: EventOutcome::Skipped {
                            reason:
                                "default :program definition installed only in read-time execution world"
                                    .into(),
                        },
                        notes: vec![
                            format!("source event kind: {head}"),
                            "no logical definition or theorem authority".into(),
                        ],
                    });
                }
                self.logical_functions.insert(label.clone());
                if self.inventory_only {
                    if items.len() < 4
                        || items.get(1).and_then(SExpr::as_symbol).is_none()
                        || items.get(2).and_then(SExpr::as_list).is_none()
                    {
                        return Ok(rec(
                            head,
                            label,
                            EventOutcome::Rejected {
                                reason: "malformed function definition".into(),
                            },
                        ));
                    }
                    return Ok(rec(
                        head,
                        label,
                        EventOutcome::Skipped {
                            reason: "inventory only — logical definition not executed".into(),
                        },
                    ));
                }
                let normalized = self.rewrite_macro_aliases(&normalize_event_head(items, "defun"));
                match self.sess.try_event(&normalized) {
                    Ok(Some(name)) => Ok(rec(head, name, EventOutcome::Admitted { hyps: 0 })),
                    Ok(None) => Ok(rec(
                        head,
                        label,
                        EventOutcome::Rejected {
                            reason: "malformed defun event".into(),
                        },
                    )),
                    Err(e) => Ok(rec(
                        head,
                        label,
                        EventOutcome::Rejected {
                            reason: e.to_string(),
                        },
                    )),
                }
            }
            "defthm" | "defthmd" => {
                if self.inventory_only {
                    if items.len() < 3 || items.get(1).and_then(SExpr::as_symbol).is_none() {
                        return Ok(rec(
                            head,
                            event_name(items),
                            EventOutcome::Rejected {
                                reason: "malformed theorem event".into(),
                            },
                        ));
                    }
                    return Ok(rec(
                        head,
                        event_name(items),
                        EventOutcome::Skipped {
                            reason: "inventory only — theorem not proved".into(),
                        },
                    ));
                }
                let normalized = normalize_event_head(items, "defthm");
                let normalized_items = normalized.as_list().expect("constructed list");
                let mut record = self.process_defthm(book, normalized_items);
                record.kind = head.into();
                Ok(record)
            }
            "defrule" | "defruled" | "defrulel" => {
                if self.inventory_only {
                    if items.len() < 3 || items.get(1).and_then(SExpr::as_symbol).is_none() {
                        return Ok(rec(
                            head,
                            event_name(items),
                            EventOutcome::Rejected {
                                reason: "malformed theorem alias".into(),
                            },
                        ));
                    }
                    return Ok(rec(
                        head,
                        event_name(items),
                        EventOutcome::Skipped {
                            reason: "inventory only — theorem alias not proved".into(),
                        },
                    ));
                }
                let normalized = normalize_event_head(items, "defthm");
                let normalized_items = normalized.as_list().expect("constructed list");
                let mut record = self.process_defthm(book, normalized_items);
                record.kind = head.into();
                record.notes.push(match head {
                    "defruled" => "disabled-rule metadata ignored".into(),
                    "defrulel" => {
                        "local-rule metadata recorded; theorem retained in session".into()
                    }
                    _ => "defrule metadata normalized to defthm".into(),
                });
                if head == "defrulel" {
                    record.outcome = match record.outcome {
                        EventOutcome::Transported | EventOutcome::Admitted { .. } => {
                            EventOutcome::Skipped {
                                reason: "local defrule processed, not exported".into(),
                            }
                        }
                        other => other,
                    };
                }
                Ok(record)
            }
            "defruledl" => {
                if self.inventory_only {
                    return Ok(rec(
                        head,
                        event_name(items),
                        EventOutcome::Skipped {
                            reason: "inventory only — local disabled theorem alias not proved"
                                .into(),
                        },
                    ));
                }
                let normalized = normalize_event_head(items, "defthm");
                let normalized_items = normalized.as_list().expect("constructed list");
                let mut record = self.process_defthm(book, normalized_items);
                record.kind = head.into();
                record.notes.push(
                    "local disabled-rule metadata recorded; theorem retained in session".into(),
                );
                record.outcome = match record.outcome {
                    EventOutcome::Transported | EventOutcome::Admitted { .. } => {
                        EventOutcome::Skipped {
                            reason: "local disabled defrule processed, not exported".into(),
                        }
                    }
                    other => other,
                };
                Ok(record)
            }
            "defthm-unsigned-byte-p" | "defthm-signed-byte-p" => {
                Ok(self.process_bound_theorem(book, head, items))
            }
            "defthm-using-gl" | "def-gl-thm" => Ok(self.process_gl_theorem(book, head, items)),
            "def-generic-rule" => self.process_generic_rule(book, file, lookup, items, None),
            "def-projection-rule"
            | "def-listp-rule"
            | "def-nonempty-listp-rule"
            | "def-listfix-rule"
            | "def-mapappend-rule" => {
                let table = match head {
                    "def-projection-rule" => "projection-rules",
                    "def-listp-rule" => "listp-rules",
                    "def-nonempty-listp-rule" => "nonempty-listp-rules",
                    "def-listfix-rule" => "listfix-rules",
                    _ => "mapappend-rules",
                };
                self.process_generic_rule(book, file, lookup, items, Some(table))
            }
            "defbitstruct" => self.process_scalar_bitstruct(book, file, lookup, items),
            "defprod" | "fty::defprod" | "fty::deflist" | "fty::defoption" => {
                self.process_fty_container(book, file, lookup, head, items)
            }
            "fty::deftypes" => Ok(rejected_event(
                book,
                head,
                &event_name(items),
                "mutually recursive FTY types require simultaneous predicate/fixer admission",
            )),
            "fty::deffixtype" => self.process_deffixtype(book, file, lookup, items),
            "defequiv" => Ok(self.process_defequiv(book, items)),
            "defrefinement" => Ok(self.process_defrefinement(book, items)),
            "defcong" => Ok(self.process_defcong(book, items)),
            "in-theory"
            | "def-ruleset"
            | "def-ruleset!"
            | "add-to-ruleset"
            | "deftheory"
            | "theory-invariant"
            | "set-default-hints"
            | "set-default-parents"
            | "set-non-linearp"
            | "set-rewrite-stack-limit"
            | "set-state-ok" => Ok(EventRecord {
                book: book.into(),
                kind: head.into(),
                label: event_name(items),
                outcome: EventOutcome::Skipped {
                    reason: "proof-control world mutation recorded for future replay".into(),
                },
                notes: vec![format!("form: {}", render_form(form))],
            }),
            "defxdoc"
            | "defxdoc+"
            | "xdoc::set-default-parents"
            | "xdoc::order-subtopics"
            | "xdoc::add-resource-directory"
            | "acl2::add-untranslate-pattern-function"
            | "acl2::optimize-untranslate-patterns" => Ok(EventRecord {
                book: book.into(),
                kind: head.into(),
                label: event_name(items),
                outcome: EventOutcome::Skipped {
                    reason: "documentation event recorded, no logical effect".into(),
                },
                notes: vec![format!("form: {}", render_form(form))],
            }),
            "defttag" | "include-raw" | "defattach" | "acl2::set-raw-mode-on" => Ok(EventRecord {
                book: book.into(),
                kind: head.into(),
                label: event_name(items),
                outcome: EventOutcome::Skipped {
                    reason: "raw/execution attachment recorded outside the logical import world"
                        .into(),
                },
                notes: vec![
                    "no theorem authority; excluded from the trusted kernel".into(),
                    format!("form: {}", render_form(form)),
                ],
            }),
            "push-untouchable" => Ok(EventRecord {
                book: book.into(),
                kind: head.into(),
                label: event_name(items),
                outcome: EventOutcome::Skipped {
                    reason: "admission-control world mutation recorded for future replay".into(),
                },
                notes: vec![format!("form: {}", render_form(form))],
            }),
            other if logic_irrelevant_event(other) => Ok(rec(
                other,
                event_name(items),
                EventOutcome::Skipped {
                    reason: "portcullis/control event has no logical effect in this importer"
                        .into(),
                },
            )),
            other => Ok(rec(
                other,
                event_name(items),
                EventOutcome::Rejected {
                    reason: format!(
                        "`{other}` events are not supported in this slice \
                         (supported: in-package, include-book, defun aliases/plain define, \
                          defthm/defrule aliases, empty-signature encapsulate, local, \
                          progn, defsection)"
                    ),
                },
            )),
        }
    }

    fn process_constant(
        &mut self,
        book: &str,
        kind: &str,
        form: &SExpr,
        items: &[SExpr],
    ) -> Result<EventRecord, BookError> {
        let label = if kind == "defconsts" {
            items
                .get(1)
                .and_then(SExpr::as_list)
                .and_then(|names| names.first())
                .and_then(SExpr::as_symbol)
                .map(str::to_owned)
                .unwrap_or_else(|| event_name(items))
        } else {
            event_name(items)
        };
        let outcome = match self.world.process_world_event(form) {
            Ok(WorldEventStatus::Handled) => EventOutcome::Skipped {
                reason: "read-time constant evaluated and installed; no theorem authority".into(),
            },
            Ok(WorldEventStatus::Unhandled) => EventOutcome::Rejected {
                reason: format!("internal: `{kind}` was not recognized by the ACL2 world"),
            },
            Err(error) => EventOutcome::Rejected {
                reason: format!("read-time constant evaluation failed: {error}"),
            },
        };
        Ok(EventRecord {
            book: book.into(),
            kind: kind.into(),
            label,
            outcome,
            notes: vec!["computed world data only; no theorem minted".into()],
        })
    }

    /// Expand the top-level `std::more-returns` event through the same
    /// retained `define` metadata as its ACL2 macro.  The generated `progn`
    /// and every theorem are recursively processed, so the wrapper itself
    /// can never stand in for the theorem obligations it introduces.
    fn process_more_returns(
        &mut self,
        book: &str,
        file: &Path,
        lookup: &LookupRoot,
        kind: &str,
        items: &[SExpr],
    ) -> Result<EventRecord, BookError> {
        let arguments = SExpr::List(items[1..].to_vec());
        let generated = call(
            "make-event",
            vec![call(
                "more-returns-fn",
                vec![
                    call("quote", vec![arguments]),
                    call("w", vec![SExpr::symbol("state")]),
                ],
            )],
        );
        let generated_items = generated.as_list().expect("constructed list");
        let mut record =
            self.process_make_event(book, file, lookup, &generated, generated_items)?;
        record.kind = kind.into();
        record.label = items
            .get(1)
            .and_then(SExpr::as_symbol)
            .map(str::to_owned)
            .unwrap_or_else(|| "current-define".into());
        record.notes.push(
            "expanded from retained define metadata; nested theorem obligations preserved".into(),
        );
        Ok(record)
    }

    /// Evaluate `assert-event` as a bounded read-time assertion.  Success is
    /// only an execution check and grants no theorem authority; false or
    /// unevaluable assertions are rejected.
    fn process_assert_event(&mut self, book: &str, form: &SExpr, items: &[SExpr]) -> EventRecord {
        let label = items
            .get(1)
            .map(summarize)
            .unwrap_or_else(|| "assert-event".into());
        let outcome = if items.len() != 2 {
            EventOutcome::Rejected {
                reason: "assert-event: expected exactly one assertion".into(),
            }
        } else {
            let sharp_dot = call("sharp-dot", vec![items[1].clone()]);
            match self.world.eval_sharp_dot(&sharp_dot) {
                Ok(crate::world::WorldValue::Nil) => EventOutcome::Rejected {
                    reason: "assert-event evaluated to nil".into(),
                },
                Ok(_) => EventOutcome::Skipped {
                    reason: "read-time assertion evaluated true; no theorem authority".into(),
                },
                Err(error) => EventOutcome::Rejected {
                    reason: format!("assert-event evaluation failed: {error}"),
                },
            }
        };
        EventRecord {
            book: book.into(),
            kind: "assert-event".into(),
            label,
            outcome,
            notes: vec![
                "execution check only; assertion result is not imported as a theorem".into(),
                format!("form: {}", render_form(form)),
            ],
        }
    }

    fn process_defmacro(
        &mut self,
        book: &str,
        form: &SExpr,
        items: &[SExpr],
    ) -> Result<EventRecord, BookError> {
        let label = event_name(items);
        let outcome = match self.world.process_world_event(form) {
            Ok(WorldEventStatus::Handled) => EventOutcome::Skipped {
                reason: "ordinary quasiquoted macro template installed for untrusted expansion"
                    .into(),
            },
            Ok(WorldEventStatus::Unhandled) => EventOutcome::Rejected {
                reason: "internal: defmacro was not recognized by the ACL2 world".into(),
            },
            Err(error) => EventOutcome::Rejected {
                reason: format!("defmacro installation rejected: {error}"),
            },
        };
        Ok(EventRecord {
            book: book.into(),
            kind: "defmacro".into(),
            label,
            outcome,
            notes: vec!["macro expansion grants no theorem authority".into()],
        })
    }

    fn process_add_macro_alias(&mut self, book: &str, items: &[SExpr]) -> EventRecord {
        let reject =
            |label: &str, reason: String| rejected_event(book, "add-macro-alias", label, &reason);
        if items.len() != 3 {
            return reject("?", "add-macro-alias requires alias and target".into());
        }
        let (Some(alias), Some(target)) = (
            items.get(1).and_then(SExpr::as_symbol),
            items.get(2).and_then(SExpr::as_symbol),
        ) else {
            return reject("?", "add-macro-alias names must be symbols".into());
        };
        let mut resolved = target.to_string();
        let mut seen = BTreeSet::from([alias.to_string()]);
        while let Some(next) = self.macro_aliases.get(&resolved) {
            if !seen.insert(resolved.clone()) {
                return reject(alias, format!("macro alias cycle through {resolved}"));
            }
            resolved = next.clone();
        }
        if resolved == alias || !seen.insert(resolved.clone()) {
            return reject(alias, format!("macro alias cycle through {resolved}"));
        }
        if !self.logical_functions.contains(&resolved) {
            return reject(
                alias,
                format!("macro alias target `{resolved}` is not an ordered logical function"),
            );
        }
        self.macro_aliases
            .insert(alias.to_string(), target.to_string());
        EventRecord {
            book: book.into(),
            kind: "add-macro-alias".into(),
            label: alias.into(),
            outcome: EventOutcome::Skipped {
                reason: "macro-to-logical-function alias registered".into(),
            },
            notes: vec![
                format!("target: {target}"),
                format!("resolved logical target: {resolved}"),
                "proof-control/read-time translation only; no definition or theorem added".into(),
            ],
        }
    }

    fn rewrite_macro_aliases(&self, form: &SExpr) -> SExpr {
        let Some(items) = form.as_list() else {
            return form.clone();
        };
        if matches!(
            items.first().and_then(SExpr::as_symbol),
            Some("quote" | "quasiquote")
        ) {
            return form.clone();
        }
        let mut rewritten = items
            .iter()
            .map(|item| self.rewrite_macro_aliases(item))
            .collect::<Vec<_>>();
        if let Some(head) = items.first().and_then(SExpr::as_symbol) {
            let mut target = head;
            let mut seen = BTreeSet::new();
            while let Some(next) = self.macro_aliases.get(target) {
                if !seen.insert(target) {
                    break;
                }
                target = next;
            }
            if target != head {
                rewritten[0] = SExpr::symbol(target);
            }
        }
        SExpr::List(rewritten)
    }

    fn process_macro_call(
        &mut self,
        book: &str,
        file: &Path,
        lookup: &LookupRoot,
        name: &str,
        call: &SExpr,
        expanded: &SExpr,
    ) -> Result<EventRecord, BookError> {
        let label = summarize(call);
        if self.macro_depth >= 256 {
            return Ok(EventRecord {
                book: book.into(),
                kind: name.into(),
                label,
                outcome: EventOutcome::Rejected {
                    reason: "macro expansion depth exceeded 256".into(),
                },
                notes: Vec::new(),
            });
        }
        self.macro_depth += 1;
        let first_nested = self.events.len();
        let result = self.process_event(book, file, lookup, expanded);
        self.macro_depth -= 1;
        let mut emitted = result?;
        let provenance = format!("generated by macro call {label}");
        for nested in &mut self.events[first_nested..] {
            nested.notes.push(provenance.clone());
        }
        emitted.notes.push(provenance);
        let emitted_summary = format!("expanded to ({} {})", emitted.kind, emitted.label);
        self.events.push(emitted);
        Ok(EventRecord {
            book: book.into(),
            kind: name.into(),
            label,
            outcome: EventOutcome::Skipped {
                reason: "macro template expanded; emitted event recursively processed".into(),
            },
            notes: vec![
                emitted_summary,
                "no theorem authority from expansion".into(),
            ],
        })
    }

    fn process_make_event(
        &mut self,
        book: &str,
        file: &Path,
        lookup: &LookupRoot,
        form: &SExpr,
        items: &[SExpr],
    ) -> Result<EventRecord, BookError> {
        let label = items
            .get(1)
            .map(summarize)
            .unwrap_or_else(|| "make-event".into());
        let generated = match self.world.eval_make_event_data(form) {
            Ok(generated) => generated,
            Err(error) => {
                return Ok(EventRecord {
                    book: book.into(),
                    kind: "make-event".into(),
                    label,
                    outcome: EventOutcome::Rejected {
                        reason: format!("make-event evaluation failed: {error}"),
                    },
                    notes: vec!["no generated event was installed".into()],
                });
            }
        };
        let provenance = format!("generated by make-event {label}");
        if let GeneratedEventData::QuotedDefconstProgn(constants) = generated {
            let count = constants.len();
            for (name, value) in constants {
                self.world.install_generated_constant(name.clone(), value);
                self.events.push(EventRecord {
                    book: book.into(),
                    kind: "defconst".into(),
                    label: name,
                    outcome: EventOutcome::Skipped {
                        reason: "read-time constant evaluated and installed; no theorem authority"
                            .into(),
                    },
                    notes: vec![
                        "computed world data only; no theorem minted".into(),
                        provenance.clone(),
                    ],
                });
            }
            self.events.push(EventRecord {
                book: book.into(),
                kind: "progn".into(),
                label: "progn".into(),
                outcome: EventOutcome::Skipped {
                    reason: "transparent event container — contents processed".into(),
                },
                notes: vec![provenance],
            });
            return Ok(EventRecord {
                book: book.into(),
                kind: "make-event".into(),
                label,
                outcome: EventOutcome::Skipped {
                    reason: "read-time expression evaluated; emitted event recursively processed"
                        .into(),
                },
                notes: vec![
                    "emitted (progn progn)".into(),
                    format!(
                        "installed {count} generated quoted constants without surface rematerialization"
                    ),
                    "no theorem authority from evaluation".into(),
                ],
            });
        }
        let GeneratedEventData::Surface(generated) = generated else {
            unreachable!("optimized generated event handled above");
        };
        let first_nested = self.events.len();
        let mut emitted = self.process_event(book, file, lookup, &generated)?;
        for nested in &mut self.events[first_nested..] {
            nested.notes.push(provenance.clone());
        }
        emitted.notes.push(provenance);
        let emitted_summary = format!("emitted ({} {})", emitted.kind, emitted.label);
        self.events.push(emitted);
        Ok(EventRecord {
            book: book.into(),
            kind: "make-event".into(),
            label,
            outcome: EventOutcome::Skipped {
                reason: "read-time expression evaluated; emitted event recursively processed"
                    .into(),
            },
            notes: vec![
                emitted_summary,
                "no theorem authority from evaluation".into(),
            ],
        })
    }

    /// Bounded exact core of `fty::deffixtype` when `:define t`: define the
    /// fixing equivalence and emit the standard fixer closure/identity and
    /// equivalence obligations, plus the fixtype registry entry.
    fn process_deffixtype(
        &mut self,
        book: &str,
        file: &Path,
        lookup: &LookupRoot,
        items: &[SExpr],
    ) -> Result<EventRecord, BookError> {
        let Some(name) = items.get(1).and_then(SExpr::as_symbol) else {
            return Ok(rejected_event(
                book,
                "fty::deffixtype",
                "?",
                "deffixtype: name must be a symbol",
            ));
        };
        let options = match theorem_macro_options(&items[2..]) {
            Ok(options) => options,
            Err(reason) => return Ok(rejected_event(book, "fty::deffixtype", name, &reason)),
        };
        if options.iter().any(|(key, _)| {
            !matches!(
                key.as_str(),
                ":pred" | ":fix" | ":equiv" | ":define" | ":forward"
            )
        }) {
            return Ok(rejected_event(
                book,
                "fty::deffixtype",
                name,
                "deffixtype: unsupported option",
            ));
        }
        let get_symbol = |key: &str| {
            options
                .iter()
                .find(|(candidate, _)| candidate == key)
                .and_then(|(_, value)| value.as_symbol())
        };
        let (Some(pred), Some(fix), Some(equiv)) = (
            get_symbol(":pred"),
            get_symbol(":fix"),
            get_symbol(":equiv"),
        ) else {
            return Ok(rejected_event(
                book,
                "fty::deffixtype",
                name,
                "deffixtype: :pred, :fix, and :equiv symbols are required",
            ));
        };
        if get_symbol(":define") != Some("t") {
            return Ok(rejected_event(
                book,
                "fty::deffixtype",
                name,
                "deffixtype: bounded expansion requires :define t",
            ));
        }
        let x = SExpr::symbol("x");
        let y = SExpr::symbol("y");
        let forms = vec![
            SExpr::List(vec![
                SExpr::symbol("defun"),
                SExpr::symbol(equiv),
                SExpr::List(vec![x.clone(), y.clone()]),
                SExpr::List(vec![
                    SExpr::symbol("equal"),
                    SExpr::List(vec![SExpr::symbol(fix), x.clone()]),
                    SExpr::List(vec![SExpr::symbol(fix), y]),
                ]),
            ]),
            SExpr::List(vec![
                SExpr::symbol("defthm"),
                SExpr::symbol(&format!("{pred}-of-{fix}")),
                SExpr::List(vec![
                    SExpr::symbol(pred),
                    SExpr::List(vec![SExpr::symbol(fix), x.clone()]),
                ]),
            ]),
            SExpr::List(vec![
                SExpr::symbol("defthm"),
                SExpr::symbol(&format!("{fix}-when-{pred}")),
                SExpr::List(vec![
                    SExpr::symbol("implies"),
                    SExpr::List(vec![SExpr::symbol(pred), x.clone()]),
                    SExpr::List(vec![
                        SExpr::symbol("equal"),
                        SExpr::List(vec![SExpr::symbol(fix), x.clone()]),
                        x,
                    ]),
                ]),
            ]),
            SExpr::List(vec![SExpr::symbol("defequiv"), SExpr::symbol(equiv)]),
        ];
        for form in forms {
            let head = form
                .as_list()
                .and_then(|parts| parts.first())
                .and_then(SExpr::as_symbol)
                .expect("constructed head");
            let mut child = if self.inventory_only && head == "defun" {
                let parts = form.as_list().expect("constructed event");
                EventRecord {
                    book: book.into(),
                    kind: "defun".into(),
                    label: event_name(parts),
                    outcome: EventOutcome::Skipped {
                        reason: "inventory only — generated fixtype definition not executed".into(),
                    },
                    notes: vec![format!("generated form: {}", render_form(&form))],
                }
            } else {
                self.process_event(book, file, lookup, &form)?
            };
            child
                .notes
                .push("generated by fty::deffixtype :define t".into());
            self.events.push(child);
        }
        self.events.push(EventRecord {
            book: book.into(),
            kind: "fty::fixtype-table".into(),
            label: name.into(),
            outcome: EventOutcome::Skipped {
                reason: "fixtype registry entry recorded for future replay".into(),
            },
            notes: vec![
                format!("predicate: {pred}"),
                format!("fixer: {fix}"),
                format!("equivalence: {equiv}"),
                format!(
                    "forward metadata: {}",
                    get_symbol(":forward").unwrap_or("nil")
                ),
            ],
        });
        Ok(EventRecord {
            book: book.into(),
            kind: "fty::deffixtype".into(),
            label: name.into(),
            outcome: EventOutcome::DeferredLogical {
                reason: "fixtype definition expanded into logical obligations".into(),
            },
            notes: vec![format!(
                "source: {}",
                render_form(&SExpr::List(items.to_vec()))
            )],
        })
    }

    /// Bounded semantic expansion for FTY's scalar bitstruct form
    /// `(defbitstruct name width)`. Aggregate layouts/options remain
    /// unresolved. The emitted predicate/fixer/equivalence are the standard
    /// unsigned-bitvector fixtype core.
    fn process_scalar_bitstruct(
        &mut self,
        book: &str,
        file: &Path,
        lookup: &LookupRoot,
        items: &[SExpr],
    ) -> Result<EventRecord, BookError> {
        let Some(name) = items.get(1).and_then(SExpr::as_symbol) else {
            return Ok(rejected_event(
                book,
                "defbitstruct",
                &event_name(items),
                "defbitstruct: name must be a symbol",
            ));
        };
        let Some(width) = items.get(2).and_then(SExpr::as_symbol) else {
            return self.process_aggregate_bitstruct(book, file, lookup, items);
        };
        let Some(width_num) = width.parse::<u32>().ok().filter(|w| *w > 0) else {
            return self.process_aggregate_bitstruct(book, file, lookup, items);
        };
        if items.len() != 3 {
            return Ok(rejected_event(
                book,
                "defbitstruct",
                name,
                "defbitstruct: only a positive literal scalar width is supported",
            ));
        }
        let pred = format!("{name}-p");
        let fix = format!("{name}-fix");
        let equiv = format!("{name}-equiv");
        let x = SExpr::symbol("x");
        let y = SExpr::symbol("y");
        let forms = vec![
            SExpr::List(vec![
                SExpr::symbol("defun"),
                SExpr::symbol(&pred),
                SExpr::List(vec![x.clone()]),
                SExpr::List(vec![
                    SExpr::symbol("unsigned-byte-p"),
                    SExpr::symbol(width),
                    x.clone(),
                ]),
            ]),
            SExpr::List(vec![
                SExpr::symbol("defun"),
                SExpr::symbol(&fix),
                SExpr::List(vec![x.clone()]),
                SExpr::List(vec![
                    SExpr::symbol("loghead"),
                    SExpr::symbol(width),
                    x.clone(),
                ]),
            ]),
            SExpr::List(vec![
                SExpr::symbol("defun"),
                SExpr::symbol(&equiv),
                SExpr::List(vec![x.clone(), y.clone()]),
                SExpr::List(vec![
                    SExpr::symbol("equal"),
                    SExpr::List(vec![SExpr::symbol(&fix), x.clone()]),
                    SExpr::List(vec![SExpr::symbol(&fix), y]),
                ]),
            ]),
            SExpr::List(vec![
                SExpr::symbol("defthm"),
                SExpr::symbol(&format!("{pred}-of-{fix}")),
                SExpr::List(vec![
                    SExpr::symbol(&pred),
                    SExpr::List(vec![SExpr::symbol(&fix), x]),
                ]),
            ]),
            SExpr::List(vec![SExpr::symbol("defequiv"), SExpr::symbol(&equiv)]),
        ];
        for form in forms {
            let constructed_head = form
                .as_list()
                .and_then(|items| items.first())
                .and_then(SExpr::as_symbol)
                .expect("constructed head");
            let mut child = if self.inventory_only && constructed_head == "defun" {
                let child_items = form.as_list().expect("constructed event");
                EventRecord {
                    book: book.into(),
                    kind: child_items[0].as_symbol().expect("constructed head").into(),
                    label: event_name(child_items),
                    outcome: EventOutcome::Skipped {
                        reason: "inventory only — scalar bitstruct obligation not executed".into(),
                    },
                    notes: vec![format!("generated form: {}", render_form(&form))],
                }
            } else {
                self.process_event(book, file, lookup, &form)?
            };
            child
                .notes
                .push("generated by scalar FTY defbitstruct expansion".into());
            self.events.push(child);
        }
        self.events.push(EventRecord {
            book: book.into(),
            kind: "fty::bitstruct-table".into(),
            label: name.into(),
            outcome: EventOutcome::Skipped {
                reason: "scalar bitstruct registry entry recorded for future replay".into(),
            },
            notes: vec![format!("width: {width}")],
        });
        let ty = BitstructType {
            width: width_num,
            fix: fix.clone(),
        };
        self.bitstructs.insert(name.to_string(), ty.clone());
        self.bitstructs.insert(pred.clone(), ty);
        Ok(EventRecord {
            book: book.into(),
            kind: "defbitstruct".into(),
            label: name.into(),
            outcome: EventOutcome::DeferredLogical {
                reason: "scalar bitstruct expanded into fixtype logical obligations".into(),
            },
            notes: vec![
                format!("width: {width}"),
                "bounded expansion: scalar literal-width form".into(),
            ],
        })
    }

    /// Exact logical-definition core for the common full, unsigned aggregate
    /// FTY bitstruct form used by x86isa. Field types must already be present
    /// in the ordered bitstruct registry; this preserves include/event order
    /// and prevents guessed widths. Documentation, `:inline`, `:msb-first
    /// nil`, and field defaults do not alter these logical definitions.
    fn process_aggregate_bitstruct(
        &mut self,
        book: &str,
        file: &Path,
        lookup: &LookupRoot,
        items: &[SExpr],
    ) -> Result<EventRecord, BookError> {
        let name = items[1].as_symbol().expect("caller validated");
        let mut layout = None;
        let mut cursor = 2;
        while cursor < items.len() {
            if let Some(keyword) = items[cursor]
                .as_symbol()
                .filter(|symbol| symbol.starts_with(':'))
            {
                let Some(value) = items.get(cursor + 1) else {
                    return Ok(rejected_event(
                        book,
                        "defbitstruct",
                        name,
                        &format!("defbitstruct: option {keyword} has no value"),
                    ));
                };
                if keyword == ":msb-first" && value.as_symbol() != Some("nil") {
                    return Ok(rejected_event(
                        book,
                        "defbitstruct",
                        name,
                        "defbitstruct: only the LSB-first aggregate layout is supported",
                    ));
                }
                if !matches!(
                    keyword,
                    ":inline" | ":msb-first" | ":parents" | ":short" | ":long" | ":xvar"
                ) {
                    return Ok(rejected_event(
                        book,
                        "defbitstruct",
                        name,
                        &format!(
                            "defbitstruct: aggregate option {keyword} requires full FTY expansion"
                        ),
                    ));
                }
                cursor += 2;
                continue;
            }
            if items[cursor].as_str().is_some() {
                cursor += 1;
                continue;
            }
            if layout.replace(&items[cursor]).is_some() {
                return Ok(rejected_event(
                    book,
                    "defbitstruct",
                    name,
                    "defbitstruct: multiple aggregate layouts",
                ));
            }
            cursor += 1;
        }
        let Some(layout) = layout.and_then(SExpr::as_list) else {
            return Ok(rejected_event(
                book,
                "defbitstruct",
                name,
                "defbitstruct: aggregate field layout must be a list",
            ));
        };
        let mut fields = Vec::with_capacity(layout.len());
        let mut lsb = 0u32;
        for field in layout {
            let Some(parts) = field.as_list() else {
                return Ok(rejected_event(
                    book,
                    "defbitstruct",
                    name,
                    "defbitstruct: aggregate field must be a list",
                ));
            };
            let (Some(field_name), Some(type_name)) = (
                parts.first().and_then(SExpr::as_symbol),
                parts.get(1).and_then(SExpr::as_symbol),
            ) else {
                return Ok(rejected_event(
                    book,
                    "defbitstruct",
                    name,
                    "defbitstruct: field requires a symbolic name and registered type",
                ));
            };
            // The only field option in the x86 full-layout subset is
            // `:default`, which affects the generated maker macro but not any
            // logical definition or theorem.
            let mut rest = &parts[2..];
            if rest.first().is_some_and(|item| item.as_str().is_some()) {
                rest = &rest[1..];
            }
            while let Some(keyword) = rest.first().and_then(SExpr::as_symbol) {
                if keyword != ":default" || rest.len() < 2 {
                    return Ok(rejected_event(
                        book,
                        "defbitstruct",
                        name,
                        &format!(
                            "defbitstruct: field option {keyword} requires full FTY expansion"
                        ),
                    ));
                }
                rest = &rest[2..];
            }
            if !rest.is_empty() {
                return Ok(rejected_event(
                    book,
                    "defbitstruct",
                    name,
                    "defbitstruct: malformed field metadata",
                ));
            }
            let Some(ty) = self.bitstructs.get(type_name).cloned() else {
                return Ok(rejected_event(
                    book,
                    "defbitstruct",
                    name,
                    &format!("defbitstruct: unknown ordered field type {type_name}"),
                ));
            };
            fields.push(BitstructField {
                name: field_name.into(),
                ty: ty.clone(),
                lsb,
            });
            lsb = lsb
                .checked_add(ty.width)
                .ok_or_else(|| BookError::Path(name.into(), "bitstruct width overflow".into()))?;
        }
        if fields.is_empty() || lsb == 0 {
            return Ok(rejected_event(
                book,
                "defbitstruct",
                name,
                "defbitstruct: aggregate layout must be nonempty",
            ));
        }

        let pred = format!("{name}-p");
        let fix = format!("{name}-fix");
        let equiv = format!("{name}-equiv");
        let x = SExpr::symbol("x");
        let y = SExpr::symbol("y");
        let mut forms = vec![
            defun_form(
                &pred,
                vec![x.clone()],
                SExpr::List(vec![
                    SExpr::symbol("unsigned-byte-p"),
                    SExpr::symbol(&lsb.to_string()),
                    x.clone(),
                ]),
            ),
            defun_form(
                &fix,
                vec![x.clone()],
                SExpr::List(vec![
                    SExpr::symbol("loghead"),
                    SExpr::symbol(&lsb.to_string()),
                    x.clone(),
                ]),
            ),
            defun_form(
                &equiv,
                vec![x.clone(), y.clone()],
                SExpr::List(vec![
                    SExpr::symbol("equal"),
                    call(&fix, vec![x.clone()]),
                    call(&fix, vec![y.clone()]),
                ]),
            ),
        ];

        let ctor_formals = fields
            .iter()
            .map(|field| SExpr::symbol(&field.name))
            .collect::<Vec<_>>();
        let ctor_body = fields.iter().rev().fold(None, |rest, field| {
            let fixed = call(&field.ty.fix, vec![SExpr::symbol(&field.name)]);
            Some(match rest {
                None => fixed,
                Some(high) => SExpr::List(vec![
                    SExpr::symbol("logapp"),
                    SExpr::symbol(&field.ty.width.to_string()),
                    fixed,
                    high,
                ]),
            })
        });
        forms.push(defun_form(
            name,
            ctor_formals,
            ctor_body.expect("nonempty fields"),
        ));
        for field in &fields {
            let accessor = format!("{name}->{}", field.name);
            forms.push(defun_form(
                &accessor,
                vec![x.clone()],
                SExpr::List(vec![
                    SExpr::symbol("bitops::part-select"),
                    call(&fix, vec![x.clone()]),
                    SExpr::symbol(":low"),
                    SExpr::symbol(&field.lsb.to_string()),
                    SExpr::symbol(":width"),
                    SExpr::symbol(&field.ty.width.to_string()),
                ]),
            ));
            forms.push(defun_form(
                &format!("!{accessor}"),
                vec![SExpr::symbol(&field.name), x.clone()],
                SExpr::List(vec![
                    SExpr::symbol("bitops::part-install"),
                    call(&field.ty.fix, vec![SExpr::symbol(&field.name)]),
                    call(&fix, vec![x.clone()]),
                    SExpr::symbol(":width"),
                    SExpr::symbol(&field.ty.width.to_string()),
                    SExpr::symbol(":low"),
                    SExpr::symbol(&field.lsb.to_string()),
                ]),
            ));
        }
        for form in forms {
            let mut child = self.process_event(book, file, lookup, &form)?;
            child
                .notes
                .push("generated by full unsigned FTY defbitstruct expansion".into());
            child.notes.push(format!(
                "source: {}",
                render_form(&SExpr::List(items.to_vec()))
            ));
            self.events.push(child);
        }
        // Predicate/fixer/equivalence theorems and every accessor/updater
        // theorem remain represented by the original macro form for replay.
        // This row is proof-control, not theorem authority.
        self.events.push(EventRecord {
            book: book.into(),
            kind: "fty::bitstruct-obligations".into(),
            label: name.into(),
            outcome: EventOutcome::DeferredLogical {
                reason: "official generated theorem family retained for future proof replay".into(),
            },
            notes: vec![
                format!("fields: {}", fields.len()),
                format!("source: {}", render_form(&SExpr::List(items.to_vec()))),
                "no generated theorem admitted".into(),
            ],
        });
        self.events.push(EventRecord {
            book: book.into(),
            kind: "fty::bitstruct-table".into(),
            label: name.into(),
            outcome: EventOutcome::Skipped {
                reason: "aggregate bitstruct registry entry installed".into(),
            },
            notes: vec![format!("width: {lsb}")],
        });
        let ty = BitstructType {
            width: lsb,
            fix: fix.clone(),
        };
        self.bitstructs.insert(name.into(), ty.clone());
        self.bitstructs.insert(pred, ty);
        Ok(EventRecord {
            book: book.into(),
            kind: "defbitstruct".into(),
            label: name.into(),
            outcome: EventOutcome::DeferredLogical {
                reason: "full unsigned aggregate expanded into exact logical definition core"
                    .into(),
            },
            notes: vec![
                format!("width: {lsb}"),
                format!("fields: {}", fields.len()),
                "generated theorem family retained as a replay obligation; no theorem authority"
                    .into(),
            ],
        })
    }

    /// Inventory the exact public logical surface of the non-mutual FTY
    /// container forms used by x86isa.  Their official expansion is large and
    /// proof-oriented; every generated theorem remains one explicit replay
    /// obligation carrying the complete source form.  Definitions are
    /// enumerated only when their names follow directly from the macro syntax.
    fn process_fty_container(
        &mut self,
        book: &str,
        file: &Path,
        lookup: &LookupRoot,
        kind: &str,
        items: &[SExpr],
    ) -> Result<EventRecord, BookError> {
        let Some(name) = items.get(1).and_then(SExpr::as_symbol) else {
            return Ok(rejected_event(
                book,
                kind,
                "?",
                "FTY container name must be a symbol",
            ));
        };
        if !self.inventory_only {
            return Ok(rejected_event(
                book,
                kind,
                name,
                "FTY container logical definitions remain inventory-only proof obligations",
            ));
        }
        let separator = items
            .iter()
            .position(|item| item.as_symbol() == Some("///"))
            .unwrap_or(items.len());
        let pre = &items[2..separator];
        let post = if separator < items.len() {
            &items[separator + 1..]
        } else {
            &[][..]
        };
        let mut names = vec![
            format!("{name}-p"),
            format!("{name}-fix"),
            format!("{name}-equiv"),
        ];
        match kind {
            "defprod" | "fty::defprod" => {
                let Some(fields) = pre.iter().find_map(|candidate| {
                    let fields = candidate.as_list()?;
                    fields
                        .iter()
                        .all(|field| {
                            field.as_list().is_some_and(|parts| {
                                parts.first().and_then(SExpr::as_symbol).is_some()
                                    && parts.get(1).and_then(SExpr::as_symbol).is_some()
                            })
                        })
                        .then_some(fields)
                }) else {
                    return Ok(rejected_event(
                        book,
                        kind,
                        name,
                        "FTY defprod field layout was not found",
                    ));
                };
                names.push(name.to_string());
                for field in fields {
                    let field_name = field
                        .as_list()
                        .and_then(|parts| parts.first())
                        .and_then(SExpr::as_symbol)
                        .expect("validated field");
                    names.push(format!("{name}->{field_name}"));
                }
            }
            "fty::deflist" => {
                names.push(format!("{name}-count"));
            }
            "fty::defoption" => {
                if items.get(2).and_then(SExpr::as_symbol).is_none() {
                    return Ok(rejected_event(
                        book,
                        kind,
                        name,
                        "FTY defoption element predicate must be a symbol",
                    ));
                }
                names.push(format!("{name}-some->val"));
            }
            _ => unreachable!("dispatch limits FTY container kinds"),
        }
        let source = render_form(&SExpr::List(items.to_vec()));
        for generated in names {
            self.events.push(EventRecord {
                book: book.into(),
                kind: "defun".into(),
                label: generated,
                outcome: EventOutcome::Skipped {
                    reason: "inventory only — official FTY logical definition not executed".into(),
                },
                notes: vec![
                    format!("generated by {kind}"),
                    format!("source: {source}"),
                    "definition name derived from the official FTY public interface".into(),
                    "no theorem authority".into(),
                ],
            });
        }
        self.events.push(EventRecord {
            book: book.into(),
            kind: "fty::container-obligations".into(),
            label: name.into(),
            outcome: EventOutcome::DeferredLogical {
                reason: "official generated equation/theorem family retained for proof replay"
                    .into(),
            },
            notes: vec![
                format!("source: {source}"),
                "no generated theorem admitted".into(),
            ],
        });
        for event in post {
            let mut child = self.process_event(book, file, lookup, event)?;
            child.notes.push(format!("generated after {kind} ///"));
            self.events.push(child);
        }
        Ok(EventRecord {
            book: book.into(),
            kind: kind.into(),
            label: name.into(),
            outcome: EventOutcome::DeferredLogical {
                reason: "FTY public definition surface inventoried; proof family retained".into(),
            },
            notes: vec![
                format!("source: {source}"),
                "bounded subset: non-mutual public interface".into(),
            ],
        })
    }

    /// Exact expansion of `std/lists/abstract`'s `def-generic-rule`: one
    /// theorem obligation plus one rule-table registration.
    fn process_generic_rule(
        &mut self,
        book: &str,
        file: &Path,
        lookup: &LookupRoot,
        items: &[SExpr],
        alias_table: Option<&str>,
    ) -> Result<EventRecord, BookError> {
        let (table, name_index, formula_index, options_index) = match alias_table {
            Some(table) => (table.to_string(), 1, 2, 3),
            None => {
                let Some(table) = items.get(1).and_then(SExpr::as_symbol) else {
                    return Ok(rejected_event(
                        book,
                        "def-generic-rule",
                        "?",
                        "def-generic-rule: table name must be a symbol",
                    ));
                };
                (table.to_string(), 2, 3, 4)
            }
        };
        let kind = items
            .first()
            .and_then(SExpr::as_symbol)
            .unwrap_or("def-generic-rule");
        let Some(name) = items.get(name_index).and_then(SExpr::as_symbol) else {
            return Ok(rejected_event(
                book,
                kind,
                "?",
                "generic rule: theorem name must be a symbol",
            ));
        };
        let Some(formula) = items.get(formula_index) else {
            return Ok(rejected_event(
                book,
                kind,
                name,
                "generic rule: missing theorem formula",
            ));
        };
        let options = match theorem_macro_options(&items[options_index..]) {
            Ok(options) => options,
            Err(reason) => return Ok(rejected_event(book, kind, name, &reason)),
        };
        if options.iter().any(|(key, _)| !generic_rule_option(key)) {
            return Ok(rejected_event(
                book,
                kind,
                name,
                "generic rule: unknown keyword option",
            ));
        }
        let mut theorem = vec![
            SExpr::symbol("defthm"),
            SExpr::symbol(name),
            formula.clone(),
        ];
        for (key, value) in &options {
            if matches!(key.as_str(), ":hints" | ":rule-classes" | ":otf-flg") {
                theorem.push(SExpr::symbol(key));
                theorem.push(value.clone());
            }
        }
        let theorem = SExpr::List(theorem);
        let mut theorem_record = self.process_event(book, file, lookup, &theorem)?;
        theorem_record
            .notes
            .push("generated by std/lists/abstract def-generic-rule".into());
        self.events.push(theorem_record);
        self.events.push(EventRecord {
            book: book.into(),
            kind: "generic-rule-table".into(),
            label: table.clone(),
            outcome: EventOutcome::Skipped {
                reason: "generic rule-table registration recorded for future replay".into(),
            },
            notes: vec![
                format!("theorem: {name}"),
                format!("source options: {}", options.len()),
            ],
        });
        Ok(EventRecord {
            book: book.into(),
            kind: kind.into(),
            label: name.into(),
            outcome: EventOutcome::Skipped {
                reason: "macro expanded — theorem obligation and table registration emitted".into(),
            },
            notes: vec![
                format!("table: {table}"),
                format!("source: {}", render_form(&SExpr::List(items.to_vec()))),
            ],
        })
    }

    /// Expand the explicit `:hyp`/`:bound`/`:concl` core of the standard
    /// bound-theorem macros. Generation flags and hints are proof metadata.
    fn process_bound_theorem(&mut self, book: &str, kind: &str, items: &[SExpr]) -> EventRecord {
        let label = event_name(items);
        let reject = |reason: String| EventRecord {
            book: book.into(),
            kind: kind.into(),
            label: label.clone(),
            outcome: EventOutcome::Rejected { reason },
            notes: Vec::new(),
        };
        if items.len() < 4 || items.get(1).and_then(SExpr::as_symbol).is_none() {
            return reject(format!("{kind}: expected a name and keyword arguments"));
        }
        let mut hyp = SExpr::symbol("t");
        let mut bound = None;
        let mut concl = None;
        let mut notes = Vec::new();
        let mut rest = &items[2..];
        while let Some(key_expr) = rest.first() {
            let Some(key) = key_expr.as_symbol().filter(|key| key.starts_with(':')) else {
                return reject(format!("{kind}: expected keyword/value arguments"));
            };
            if rest.len() < 2 {
                return reject(format!("{kind}: option {key} has no value"));
            }
            match key {
                ":hyp" => hyp = rest[1].clone(),
                ":bound" => bound = Some(rest[1].clone()),
                ":concl" => concl = Some(rest[1].clone()),
                _ => notes.push(format!("{key} proof metadata recorded")),
            }
            rest = &rest[2..];
        }
        let (Some(bound), Some(concl)) = (bound, concl) else {
            return reject(format!("{kind}: both :bound and :concl are required"));
        };
        let predicate = if kind == "defthm-unsigned-byte-p" {
            "unsigned-byte-p"
        } else {
            "signed-byte-p"
        };
        let conclusion = SExpr::List(vec![SExpr::symbol(predicate), bound, concl]);
        let formula = if hyp.as_symbol() == Some("t") {
            conclusion
        } else {
            SExpr::List(vec![SExpr::symbol("implies"), hyp, conclusion])
        };
        if self.inventory_only {
            return EventRecord {
                book: book.into(),
                kind: kind.into(),
                label,
                outcome: EventOutcome::Skipped {
                    reason: "inventory only — explicit bound theorem not proved".into(),
                },
                notes,
            };
        }
        let normalized = vec![SExpr::symbol("defthm"), items[1].clone(), formula];
        let mut record = self.process_defthm(book, &normalized);
        record.kind = kind.into();
        record.notes.extend(notes);
        record
    }

    /// ACL2's exact `defequiv` obligation: Boolean-valued, reflexive,
    /// symmetric, and transitive.
    fn process_defequiv(&mut self, book: &str, items: &[SExpr]) -> EventRecord {
        let Some(equiv) = items.get(1).and_then(SExpr::as_symbol) else {
            return rejected_event(book, "defequiv", "?", "defequiv: relation must be a symbol");
        };
        let options = match theorem_macro_options(&items[2..]) {
            Ok(options) => options,
            Err(reason) => return rejected_event(book, "defequiv", equiv, &reason),
        };
        if options.iter().any(|(key, _)| !equivalence_option(key)) {
            return rejected_event(book, "defequiv", equiv, "defequiv: unknown keyword option");
        }
        if options
            .iter()
            .find(|(key, _)| key == ":event-name")
            .is_some_and(|(_, value)| value.as_symbol().is_none())
        {
            return rejected_event(
                book,
                "defequiv",
                equiv,
                "defequiv: :event-name must be a symbol",
            );
        }
        let event_name = options
            .iter()
            .find(|(key, _)| key == ":event-name")
            .and_then(|(_, value)| value.as_symbol())
            .map(str::to_string)
            .unwrap_or_else(|| format!("{equiv}-is-an-equivalence"));
        let x = SExpr::symbol("x");
        let y = SExpr::symbol("y");
        let z = SExpr::symbol("z");
        let call = |a: SExpr, b: SExpr| SExpr::List(vec![SExpr::symbol(equiv), a, b]);
        let formula = SExpr::List(vec![
            SExpr::symbol("and"),
            SExpr::List(vec![SExpr::symbol("booleanp"), call(x.clone(), y.clone())]),
            call(x.clone(), x.clone()),
            SExpr::List(vec![
                SExpr::symbol("implies"),
                call(x.clone(), y.clone()),
                call(y.clone(), x.clone()),
            ]),
            SExpr::List(vec![
                SExpr::symbol("implies"),
                SExpr::List(vec![
                    SExpr::symbol("and"),
                    call(x.clone(), y.clone()),
                    call(y, z.clone()),
                ]),
                call(x, z),
            ]),
        ]);
        self.generated_theorem(
            book,
            "defequiv",
            &event_name,
            formula,
            options,
            "ACL2 equivalence-relation-condition",
        )
    }

    /// ACL2's exact `defrefinement-form` obligation:
    /// `(equiv1 x y) => (equiv2 x y)`.
    fn process_defrefinement(&mut self, book: &str, items: &[SExpr]) -> EventRecord {
        let (Some(equiv1), Some(equiv2)) = (
            items.get(1).and_then(SExpr::as_symbol),
            items.get(2).and_then(SExpr::as_symbol),
        ) else {
            return rejected_event(
                book,
                "defrefinement",
                "?",
                "defrefinement: both relations must be symbols",
            );
        };
        let options = match theorem_macro_options(&items[3..]) {
            Ok(options) => options,
            Err(reason) => return rejected_event(book, "defrefinement", equiv1, &reason),
        };
        if options.iter().any(|(key, _)| !equivalence_option(key)) {
            return rejected_event(
                book,
                "defrefinement",
                equiv1,
                "defrefinement: unknown keyword option",
            );
        }
        if options
            .iter()
            .find(|(key, _)| key == ":event-name")
            .is_some_and(|(_, value)| value.as_symbol().is_none())
        {
            return rejected_event(
                book,
                "defrefinement",
                equiv1,
                "defrefinement: :event-name must be a symbol",
            );
        }
        let event_name = options
            .iter()
            .find(|(key, _)| key == ":event-name")
            .and_then(|(_, value)| value.as_symbol())
            .map(str::to_string)
            .unwrap_or_else(|| format!("{equiv1}-refines-{equiv2}"));
        let x = SExpr::symbol("x");
        let y = SExpr::symbol("y");
        let formula = SExpr::List(vec![
            SExpr::symbol("implies"),
            SExpr::List(vec![SExpr::symbol(equiv1), x.clone(), y.clone()]),
            SExpr::List(vec![SExpr::symbol(equiv2), x, y]),
        ]);
        self.generated_theorem(
            book,
            "defrefinement",
            &event_name,
            formula,
            options,
            "ACL2 refinement rule",
        )
    }

    /// ACL2's exact `defcong-form` obligation.
    fn process_defcong(&mut self, book: &str, items: &[SExpr]) -> EventRecord {
        let (Some(equiv1), Some(equiv2), Some(fn_args), Some(k_text)) = (
            items.get(1).and_then(SExpr::as_symbol),
            items.get(2).and_then(SExpr::as_symbol),
            items.get(3).and_then(SExpr::as_list),
            items.get(4).and_then(SExpr::as_symbol),
        ) else {
            return rejected_event(
                book,
                "defcong",
                "?",
                "defcong: expected equiv1 equiv2 (function args...) positive-index",
            );
        };
        let Ok(k) = k_text.parse::<usize>() else {
            return rejected_event(book, "defcong", equiv1, "defcong: index is not a natural");
        };
        let symbols: Vec<_> = fn_args.iter().filter_map(SExpr::as_symbol).collect();
        let unique_args: BTreeSet<_> = symbols.iter().skip(1).copied().collect();
        if k == 0
            || k >= fn_args.len()
            || symbols.len() != fn_args.len()
            || unique_args.len() != symbols.len().saturating_sub(1)
            || symbols.first().copied() == Some("if")
        {
            return rejected_event(
                book,
                "defcong",
                equiv1,
                "defcong: malformed function application or argument index",
            );
        }
        let options = match theorem_macro_options(&items[5..]) {
            Ok(options) => options,
            Err(reason) => return rejected_event(book, "defcong", equiv1, &reason),
        };
        if options.iter().any(|(key, _)| !equivalence_option(key)) {
            return rejected_event(book, "defcong", equiv1, "defcong: unknown keyword option");
        }
        if options
            .iter()
            .find(|(key, _)| key == ":event-name")
            .is_some_and(|(_, value)| value.as_symbol().is_none())
        {
            return rejected_event(
                book,
                "defcong",
                equiv1,
                "defcong: :event-name must be a symbol",
            );
        }
        let function = fn_args[0].as_symbol().expect("validated");
        let argument = fn_args[k].as_symbol().expect("validated");
        let replacement = format!("{argument}-equiv");
        let mut updated = fn_args.to_vec();
        updated[k] = SExpr::symbol(&replacement);
        let default_name = format!("{equiv1}-implies-{equiv2}-{function}-{k}");
        let event_name = options
            .iter()
            .find(|(key, _)| key == ":event-name")
            .and_then(|(_, value)| value.as_symbol())
            .unwrap_or(&default_name)
            .to_string();
        let formula = SExpr::List(vec![
            SExpr::symbol("implies"),
            SExpr::List(vec![
                SExpr::symbol(equiv1),
                SExpr::symbol(argument),
                SExpr::symbol(&replacement),
            ]),
            SExpr::List(vec![
                SExpr::symbol(equiv2),
                SExpr::List(fn_args.to_vec()),
                SExpr::List(updated),
            ]),
        ]);
        self.generated_theorem(
            book,
            "defcong",
            &event_name,
            formula,
            options,
            "ACL2 defcong-form",
        )
    }

    fn generated_theorem(
        &mut self,
        book: &str,
        kind: &str,
        name: &str,
        formula: SExpr,
        options: Vec<(String, SExpr)>,
        provenance: &str,
    ) -> EventRecord {
        let notes = vec![
            format!("generated formula: {}", render_form(&formula)),
            format!("provenance: {provenance}"),
            format!("macro options recorded: {}", options.len()),
        ];
        if self.inventory_only {
            return EventRecord {
                book: book.into(),
                kind: kind.into(),
                label: name.into(),
                outcome: EventOutcome::Skipped {
                    reason: "inventory only — generated theorem obligation not proved".into(),
                },
                notes,
            };
        }
        let normalized = vec![SExpr::symbol("defthm"), SExpr::symbol(name), formula];
        let mut record = self.process_defthm(book, &normalized);
        record.kind = kind.into();
        record.notes.extend(notes);
        record
    }

    /// Normalize the theorem statement emitted by Centaur's GL theorem
    /// wrappers. GL symbolic bindings and configuration are proof inputs, not
    /// axioms: the exact implication is retained as an ordinary theorem
    /// obligation and must later be reconstructed or certificate-checked.
    fn process_gl_theorem(&mut self, book: &str, kind: &str, items: &[SExpr]) -> EventRecord {
        let Some(name) = items.get(1).and_then(SExpr::as_symbol) else {
            return rejected_event(book, kind, "?", "GL theorem name must be a symbol");
        };
        let options = match theorem_macro_options(&items[2..]) {
            Ok(options) => options,
            Err(reason) => return rejected_event(book, kind, name, &reason),
        };
        let mut hyp = None;
        let mut concl = None;
        for (key, value) in &options {
            match key.as_str() {
                ":hyp" => hyp = Some(value.clone()),
                ":concl" => concl = Some(value.clone()),
                _ => {}
            }
        }
        let Some(concl) = concl else {
            return rejected_event(book, kind, name, "GL theorem requires exactly one :concl");
        };
        let formula = match hyp {
            Some(hyp) => SExpr::list(vec![SExpr::symbol("implies"), hyp, concl]),
            None => concl,
        };
        self.generated_theorem(
            book,
            kind,
            name,
            formula,
            options,
            "Centaur GL theorem wrapper; symbolic execution requires checked certificate replay",
        )
    }

    /// Lower the recoverable core of `std/util/define` to `defun`. Guard/type,
    /// documentation, rule-enable, and execution metadata do not change the
    /// logical body. `:prepwork` events are recursively processed before the
    /// definition, just as in the macro's generated `progn`. Unknown options,
    /// destructuring, and multiple returns are rejected rather than guessed
    /// at. Metadata after the body and events after `///` are processed.
    fn process_define(
        &mut self,
        book: &str,
        file: &Path,
        lookup: &LookupRoot,
        items: &[SExpr],
    ) -> Result<EventRecord, BookError> {
        let label = event_name(items);
        let reject = |reason: String, notes: Vec<String>| EventRecord {
            book: book.into(),
            kind: "define".into(),
            label: label.clone(),
            outcome: EventOutcome::Rejected { reason },
            notes,
        };
        if items.len() < 4 {
            return Ok(reject(
                "define: expected name, formals, and body".into(),
                vec![],
            ));
        }
        let Some(formals) = items[2].as_list() else {
            return Ok(reject("define: formals must be a list".into(), vec![]));
        };
        let mut plain_formals = Vec::with_capacity(formals.len());
        let mut notes = Vec::new();
        let mut keyword_formals = false;
        let mut optional_formals = false;
        for formal in formals {
            let name = if let Some(name) = formal.as_symbol() {
                if name == "&key" {
                    keyword_formals = true;
                    notes.push("keyword formals recorded for read-time evaluation".into());
                    continue;
                }
                if name == "&optional" {
                    optional_formals = true;
                    notes.push("optional formals recorded for read-time evaluation".into());
                    continue;
                }
                name
            } else if let Some(binding) = formal.as_list() {
                let designator = binding.first().unwrap_or(formal);
                let name = designator.as_symbol().or_else(|| {
                    designator
                        .as_list()
                        .and_then(|guarded| guarded.first())
                        .and_then(SExpr::as_symbol)
                });
                let Some(name) = name else {
                    return Ok(reject(
                        "define: destructuring/anonymous formal is not supported".into(),
                        notes,
                    ));
                };
                if binding.len() == 1 {
                    notes.push(format!("singleton named binder {name} normalized"));
                } else {
                    notes.push(format!("formal {name} guard/type metadata recorded"));
                }
                name
            } else {
                return Ok(reject(
                    "define: formal is neither a symbol nor a named guarded binder".into(),
                    notes,
                ));
            };
            if name.starts_with('&') {
                return Ok(reject(
                    "define: Common Lisp lambda-list formals are not supported".into(),
                    notes,
                ));
            }
            plain_formals.push(SExpr::symbol(name));
        }
        if (keyword_formals || optional_formals) && !self.inventory_only {
            return Ok(reject(
                "define: keyword/optional formals require inventory/read-time expansion mode"
                    .into(),
                notes,
            ));
        }

        let mut cursor = 3;
        let mut prepwork = Vec::new();
        let mut type_prescriptions = Vec::new();
        let mut program_mode = false;
        loop {
            let Some(item) = items.get(cursor) else {
                break;
            };
            if item.as_str().is_some() {
                notes.push("definition documentation recorded".into());
                cursor += 1;
            } else if item
                .as_list()
                .and_then(|form| form.first())
                .and_then(SExpr::as_symbol)
                == Some("declare")
            {
                notes.push("definition declaration metadata recorded".into());
                cursor += 1;
            } else {
                let Some(keyword) = item.as_symbol().filter(|name| name.starts_with(':')) else {
                    break;
                };
                let Some(value) = items.get(cursor + 1) else {
                    return Ok(reject(
                        format!("define: option {keyword} has no value"),
                        notes,
                    ));
                };
                if keyword == ":prepwork" {
                    let Some(events) = quoted_list(value) else {
                        return Ok(reject(
                            "define: :prepwork must be a list of events".into(),
                            notes,
                        ));
                    };
                    prepwork.extend(events.iter().cloned());
                    notes.push(format!(":prepwork events recorded: {}", events.len()));
                    cursor += 2;
                    continue;
                }
                if keyword == ":type-prescription" {
                    type_prescriptions.push(value.clone());
                    notes.push("generated :type-prescription obligation recorded".into());
                    cursor += 2;
                    continue;
                }
                if !define_metadata_option(keyword) {
                    return Ok(reject(
                        format!(
                            "define: option {keyword} may change logical expansion and is not supported"
                        ),
                        notes,
                    ));
                }
                if keyword == ":returns"
                    && value
                        .as_list()
                        .and_then(|returns| returns.first())
                        .and_then(SExpr::as_symbol)
                        == Some("mv")
                {
                    if !self.inventory_only {
                        return Ok(reject(
                            "define: multiple-value :returns requires real macro expansion".into(),
                            notes,
                        ));
                    }
                    notes.push("multiple-value :returns metadata recorded".into());
                    cursor += 2;
                    continue;
                }
                if keyword == ":mode" {
                    program_mode = value.as_symbol() == Some(":program");
                }
                notes.push(format!("{keyword} metadata recorded"));
                cursor += 2;
            }
        }
        let Some(body) = items.get(cursor) else {
            return Ok(reject("define: missing logical body".into(), notes));
        };
        cursor += 1;
        // std::define permits theorem/guard metadata after the body. It has
        // the same meaning there as before the body; preserve it rather than
        // mistaking the first keyword for an extra logical form.
        while let Some(keyword) = items.get(cursor).and_then(SExpr::as_symbol) {
            if keyword == "///" {
                break;
            }
            if !keyword.starts_with(':') {
                break;
            }
            let Some(_value) = items.get(cursor + 1) else {
                return Ok(reject(
                    format!("define: post-body option {keyword} has no value"),
                    notes,
                ));
            };
            if keyword == ":prepwork" {
                let Some(events) = quoted_list(_value) else {
                    return Ok(reject(
                        "define: post-body :prepwork must be a list of events".into(),
                        notes,
                    ));
                };
                prepwork.extend(events.iter().cloned());
                notes.push(format!(
                    "post-body :prepwork events recorded: {}",
                    events.len()
                ));
                cursor += 2;
                continue;
            }
            if keyword == ":type-prescription" {
                type_prescriptions.push(_value.clone());
                notes.push("generated post-body :type-prescription obligation recorded".into());
                cursor += 2;
                continue;
            }
            if !define_metadata_option(keyword) {
                return Ok(reject(
                    format!(
                        "define: post-body option {keyword} may change logical expansion and is not supported"
                    ),
                    notes,
                ));
            }
            notes.push(format!("post-body {keyword} metadata recorded"));
            cursor += 2;
        }
        let post = if cursor == items.len() {
            &[][..]
        } else if items.get(cursor).and_then(SExpr::as_symbol) == Some("///") {
            &items[cursor + 1..]
        } else {
            return Ok(reject(
                "define: unexpected non-metadata forms after logical body (expected `///`)".into(),
                notes,
            ));
        };
        let normalized = self.rewrite_macro_aliases(&SExpr::List(vec![
            SExpr::symbol("defun"),
            items[1].clone(),
            SExpr::List(plain_formals),
            body.clone(),
        ]));
        // `define` is normalized to a theorem-neutral read-time function as
        // well as to its logical `defun`.  This lets later `make-event`
        // generators compute event data, but never admits their output: every
        // emitted event still returns through `process_event`.
        // Preserve the authored DEFINE form in the read-time world even when
        // its logical core normalizes to DEFUN.  DEFINE's ordered guts
        // registry (:returns, formals, and /// scope) is required by authored
        // DEFRET/MORE-RETURNS events and carries no theorem authority.
        let world_form = SExpr::List(items.to_vec());
        for event in prepwork {
            let child = self.process_event(book, file, lookup, &event)?;
            let failed = matches!(child.outcome, EventOutcome::Rejected { .. });
            self.events.push(child);
            if failed && !self.inventory_only {
                return Ok(reject(
                    "define: a :prepwork event was rejected".into(),
                    notes,
                ));
            }
        }
        // Logical inventory may support a wider lambda list than the bounded
        // read-time evaluator. Failure to install it computationally must not
        // panic or grant authority; later make-event use reports the boundary.
        let _ = self.world.process_world_event(&world_form);
        self.logical_functions.insert(label.clone());
        let record = if program_mode {
            notes.push("no theorem authority from expansion".into());
            EventRecord {
                book: book.into(),
                kind: "define".into(),
                label: label.clone(),
                outcome: EventOutcome::Skipped {
                    reason: ":mode :program definition installed only in the read-time world"
                        .into(),
                },
                notes: notes.clone(),
            }
        } else if self.inventory_only {
            EventRecord {
                book: book.into(),
                kind: "define".into(),
                label: label.clone(),
                outcome: EventOutcome::Skipped {
                    reason: "inventory only — recoverable logical definition not executed".into(),
                },
                notes: notes.clone(),
            }
        } else {
            match self.sess.try_event(&normalized) {
                Ok(Some(name)) => EventRecord {
                    book: book.into(),
                    kind: "define".into(),
                    label: name,
                    outcome: EventOutcome::Admitted { hyps: 0 },
                    notes: notes.clone(),
                },
                Ok(None) => reject("malformed define event".into(), notes.clone()),
                Err(e) => reject(e.to_string(), notes.clone()),
            }
        };
        if !matches!(record.outcome, EventOutcome::Rejected { .. }) {
            for (index, formula) in type_prescriptions.into_iter().enumerate() {
                let suffix = if index == 0 {
                    String::new()
                } else {
                    format!("-{}", index + 1)
                };
                let theorem = self.generated_theorem(
                    book,
                    "define :type-prescription",
                    &format!("{label}-type-prescription{suffix}"),
                    formula,
                    vec![(":rule-classes".into(), SExpr::symbol(":type-prescription"))],
                    &format!("std::define {label} :type-prescription"),
                );
                self.events.push(theorem);
            }
            for event in post {
                if event.as_str().is_some() {
                    notes.push("/// documentation ignored".into());
                } else {
                    let child = self.process_event(book, file, lookup, event)?;
                    self.events.push(child);
                }
            }
        }
        Ok(EventRecord { notes, ..record })
    }

    /// `with-output` changes host presentation only. Its final form is the
    /// wrapped event; preceding arguments are retained verbatim for replay.
    fn process_with_output(
        &mut self,
        book: &str,
        file: &Path,
        lookup: &LookupRoot,
        items: &[SExpr],
    ) -> Result<EventRecord, BookError> {
        let Some(child) = items.last().filter(|_| items.len() >= 2) else {
            return Ok(EventRecord {
                book: book.into(),
                kind: "with-output".into(),
                label: "with-output".into(),
                outcome: EventOutcome::Rejected {
                    reason: "with-output: missing wrapped event".into(),
                },
                notes: Vec::new(),
            });
        };
        if child.as_list().is_none() {
            return Ok(EventRecord {
                book: book.into(),
                kind: "with-output".into(),
                label: "with-output".into(),
                outcome: EventOutcome::Rejected {
                    reason: "with-output: final argument is not an event form".into(),
                },
                notes: vec![format!(
                    "options: {}",
                    items[1..items.len() - 1]
                        .iter()
                        .map(render_form)
                        .collect::<Vec<_>>()
                        .join(" ")
                )],
            });
        }
        let child = self.process_event(book, file, lookup, child)?;
        self.events.push(child);
        Ok(EventRecord {
            book: book.into(),
            kind: "with-output".into(),
            label: "with-output".into(),
            outcome: EventOutcome::Skipped {
                reason: "presentation wrapper — child event processed".into(),
            },
            notes: vec![format!(
                "options: {}",
                items[1..items.len() - 1]
                    .iter()
                    .map(render_form)
                    .collect::<Vec<_>>()
                    .join(" ")
            )],
        })
    }

    /// `progn!` sequences host/world events. Process each child in order and
    /// retain the wrapper as proof/execution control.
    fn process_progn_bang(
        &mut self,
        book: &str,
        file: &Path,
        lookup: &LookupRoot,
        items: &[SExpr],
    ) -> Result<EventRecord, BookError> {
        for child in &items[1..] {
            let child = self.process_event(book, file, lookup, child)?;
            self.events.push(child);
        }
        Ok(EventRecord {
            book: book.into(),
            kind: "progn!".into(),
            label: "progn!".into(),
            outcome: EventOutcome::Skipped {
                reason: "event sequence wrapper — children processed".into(),
            },
            notes: Vec::new(),
        })
    }

    /// Process an `encapsulate` only when its signature is empty. Such a form
    /// introduces no constrained functions, so it is a transparent event
    /// container. Non-empty signatures need real constraint/witness semantics.
    fn process_encapsulate(
        &mut self,
        book: &str,
        file: &Path,
        lookup: &LookupRoot,
        items: &[SExpr],
    ) -> Result<EventRecord, BookError> {
        let Some(signature) = items.get(1).and_then(SExpr::as_list) else {
            return Ok(EventRecord {
                book: book.into(),
                kind: "encapsulate".into(),
                label: "encapsulate".into(),
                outcome: EventOutcome::Rejected {
                    reason: "encapsulate: expected a signature list".into(),
                },
                notes: Vec::new(),
            });
        };
        if !signature.is_empty() {
            return Ok(EventRecord {
                book: book.into(),
                kind: "encapsulate".into(),
                label: "encapsulate".into(),
                outcome: EventOutcome::Rejected {
                    reason: "encapsulate with constrained function signatures is not supported"
                        .into(),
                },
                notes: Vec::new(),
            });
        }
        for child in &items[2..] {
            let child = self.process_event(book, file, lookup, child)?;
            self.events.push(child);
        }
        Ok(EventRecord {
            book: book.into(),
            kind: "encapsulate".into(),
            label: "encapsulate".into(),
            outcome: EventOutcome::Skipped {
                reason: "empty-signature event container — contents processed".into(),
            },
            notes: Vec::new(),
        })
    }

    /// Transparent event containers used pervasively by community books.
    /// Their child events are processed in order and tallied independently;
    /// the wrapper itself is an honest skipped row.
    fn process_container(
        &mut self,
        book: &str,
        file: &Path,
        lookup: &LookupRoot,
        kind: &str,
        items: &[SExpr],
    ) -> Result<EventRecord, BookError> {
        let (label, mut rest) = if kind == "defsection" {
            (event_name(items), &items[2..])
        } else {
            ("progn".into(), &items[1..])
        };
        let mut notes = Vec::new();
        while let Some(item) = rest.first() {
            if item.as_str().is_some() {
                notes.push("documentation ignored".into());
                rest = &rest[1..];
                continue;
            }
            if let Some(keyword) = item.as_symbol().filter(|s| s.starts_with(':')) {
                if rest.len() < 2 {
                    return Ok(EventRecord {
                        book: book.into(),
                        kind: kind.into(),
                        label,
                        outcome: EventOutcome::Rejected {
                            reason: format!("{kind}: option {keyword} has no value"),
                        },
                        notes,
                    });
                }
                notes.push(format!("{keyword} ignored"));
                rest = &rest[2..];
                continue;
            }
            let child = self.process_event(book, file, lookup, item)?;
            self.events.push(child);
            rest = &rest[1..];
        }
        Ok(EventRecord {
            book: book.into(),
            kind: kind.into(),
            label,
            outcome: EventOutcome::Skipped {
                reason: "transparent event container — contents processed".into(),
            },
            notes,
        })
    }

    /// `(include-book "name" [:dir …])` — resolve relative to the including
    /// book's directory, confined to the root; recurse when found.
    fn process_include(
        &mut self,
        book: &str,
        file: &Path,
        current_root: &LookupRoot,
        items: &[SExpr],
    ) -> Result<EventRecord, BookError> {
        let mut rec = EventRecord {
            book: book.to_string(),
            kind: "include-book".to_string(),
            label: summarize_arg(items),
            outcome: EventOutcome::Skipped {
                reason: String::new(),
            },
            notes: Vec::new(),
        };
        let requested_by = SourceIdentity::new(
            current_root.label.as_deref(),
            display_rel(&current_root.path, file),
        );
        let encounter_ordinal = self.next_include_ordinal;
        self.next_include_ordinal += 1;
        let mut include = IncludeRecord {
            encounter_ordinal,
            requested_by,
            request: String::new(),
            root: current_root.label.as_deref().map(normalize_dir_name),
            resolved: None,
            status: IncludeStatus::Malformed,
            detail: None,
        };
        // Reserve the encounter-order slot before recursive replay. Nested
        // includes may complete first, but cannot reorder this ledger.
        self.includes.push(include.clone());
        let name = match items.get(1).and_then(|a| a.as_str()) {
            Some(("", bytes)) => String::from_utf8_lossy(bytes).into_owned(),
            _ => {
                let detail = "include-book: expected a book name string".to_string();
                rec.outcome = EventOutcome::Rejected {
                    reason: detail.clone(),
                };
                include.detail = Some(detail);
                self.includes[encounter_ordinal] = include;
                return Ok(rec);
            }
        };
        include.request = name.clone();
        rec.label = name.clone();
        let mut selected_root = current_root.clone();
        let mut explicit_dir = false;
        let mut extras = &items[2..];
        while let Some(option) = extras.first() {
            let Some(keyword) = option.as_symbol() else {
                let detail = format!(
                    "include-book: expected keyword option, got {}",
                    summarize(option)
                );
                rec.outcome = EventOutcome::Rejected {
                    reason: detail.clone(),
                };
                include.detail = Some(detail);
                self.includes[encounter_ordinal] = include;
                return Ok(rec);
            };
            if extras.len() < 2 {
                let detail = format!("include-book: option {keyword} has no value");
                rec.outcome = EventOutcome::Rejected {
                    reason: detail.clone(),
                };
                include.detail = Some(detail);
                self.includes[encounter_ordinal] = include;
                return Ok(rec);
            }
            if !keyword.eq_ignore_ascii_case(":dir") {
                rec.notes.push(format!("{keyword} ignored"));
                extras = &extras[2..];
                continue;
            }
            let Some(dir) = extras[1].as_symbol() else {
                let detail = "include-book: :dir value must be a keyword".to_string();
                rec.outcome = EventOutcome::Rejected {
                    reason: detail.clone(),
                };
                include.detail = Some(detail);
                self.includes[encounter_ordinal] = include;
                return Ok(rec);
            };
            let key = normalize_dir_name(dir);
            include.root = Some(key.clone());
            let Some(root) = self.dir_roots.get(&key) else {
                let detail =
                    format!("include-book :dir {dir} is not configured — dependency skipped");
                rec.outcome = EventOutcome::UnresolvedDependency {
                    reason: detail.clone(),
                };
                include.status = IncludeStatus::Unconfigured;
                include.detail = Some(detail);
                self.includes[encounter_ordinal] = include;
                return Ok(rec);
            };
            selected_root = root.clone();
            explicit_dir = true;
            extras = &extras[2..];
        }
        let base_dir = if explicit_dir {
            &selected_root.path
        } else {
            file.parent().unwrap_or(&selected_root.path)
        };
        let mut resolution = resolve_source(&selected_root.path, base_dir, &name, &self.extensions);
        // A named project root is a convenient ACL2 `:dir` entry point, but
        // it is common for a book reached through it to use ordinary `../`
        // includes into a sibling project directory.  Permit that only when
        // the configured :system root independently contains both the
        // including directory and the resolved dependency.  Explicit
        // `:dir` includes retain their own confinement boundary.
        if !explicit_dir && resolution.is_err() {
            if let Some(system_root) = self.dir_roots.get("system") {
                if base_dir.starts_with(&system_root.path) {
                    resolution =
                        resolve_source(&system_root.path, base_dir, &name, &self.extensions);
                    if matches!(resolution, Ok(Resolved::Found(_))) {
                        selected_root = system_root.clone();
                    }
                }
            }
        }
        rec.outcome = match resolution {
            Err(reason) => {
                let detail = format!("include-book \"{name}\": {reason}");
                include.status = IncludeStatus::Refused;
                include.detail = Some(detail.clone());
                EventOutcome::Rejected { reason: detail }
            }
            Ok(Resolved::Missing(p)) => {
                let detail = format!("dependency not found ({}) — skipped", p.display());
                include.status = IncludeStatus::Missing;
                include.detail = Some(detail.clone());
                EventOutcome::UnresolvedDependency { reason: detail }
            }
            Ok(Resolved::Found(f)) => {
                let interface_root = selected_root.label.as_deref().map(normalize_dir_name);
                let interface_source = display_rel(&selected_root.path, &f);
                let resolved_identity =
                    SourceIdentity::new(selected_root.label.as_deref(), interface_source.clone());
                include.resolved = Some(resolved_identity.clone());
                let interface_key = (interface_root.clone(), interface_source.clone());
                if let Some(interface) =
                    self.theorem_neutral_interfaces.get(&interface_key).cloned()
                {
                    match verify_interface_source(&f, &interface.sha256) {
                        Err(error) => {
                            let (sha256, source_status, include_status, detail) = match error {
                                InterfaceVerificationError::Read(detail) => (
                                    None,
                                    SourceStatus::ReadFailed,
                                    IncludeStatus::ReadFailed,
                                    detail,
                                ),
                                InterfaceVerificationError::Utf8 { digest, detail } => (
                                    Some(digest),
                                    SourceStatus::Utf8Failed,
                                    IncludeStatus::ParseFailed,
                                    detail,
                                ),
                                InterfaceVerificationError::Parse { digest, detail } => (
                                    Some(digest),
                                    SourceStatus::ParseFailed,
                                    IncludeStatus::ParseFailed,
                                    detail,
                                ),
                                InterfaceVerificationError::Hash { actual, detail } => (
                                    Some(actual),
                                    SourceStatus::HashMismatch,
                                    IncludeStatus::HashMismatch,
                                    detail,
                                ),
                            };
                            self.sources.push(SourceRecord {
                                attempt_ordinal: self.sources.len(),
                                identity: resolved_identity,
                                role: SourceRole::Interface,
                                sha256,
                                status: source_status,
                                detail: Some(detail.clone()),
                            });
                            include.status = include_status;
                            include.detail = Some(detail.clone());
                            EventOutcome::UnresolvedDependency {
                                reason: format!("dependency interface {detail}"),
                            }
                        }
                        Ok(digest) if !self.seen.insert(f.clone()) => {
                            self.sources.push(SourceRecord {
                                attempt_ordinal: self.sources.len(),
                                identity: resolved_identity,
                                role: SourceRole::Interface,
                                sha256: Some(digest),
                                status: SourceStatus::Interface,
                                detail: None,
                            });
                            include.status = IncludeStatus::Idempotent;
                            EventOutcome::Skipped {
                                reason: "already included — idempotent".into(),
                            }
                        }
                        Ok(digest) => {
                            self.sources.push(SourceRecord {
                                attempt_ordinal: self.sources.len(),
                                identity: resolved_identity,
                                role: SourceRole::Interface,
                                sha256: Some(digest),
                                status: SourceStatus::Interface,
                                detail: None,
                            });
                            self.applied_dependency_interfaces
                                .push(DependencyInterfaceRecord {
                                    requested_by: book.into(),
                                    root: interface_root,
                                    source: interface_source,
                                    sha256: hex_digest(&digest),
                                    capability: interface.capability,
                                    rationale: interface.rationale.clone(),
                                });
                            rec.notes.push(interface.rationale.clone());
                            include.status = IncludeStatus::Interface;
                            EventOutcome::DependencyInterface {
                                sha256: hex_digest(&digest),
                            }
                        }
                    }
                } else if !self.seen.insert(f.clone()) {
                    include.status = IncludeStatus::Idempotent;
                    EventOutcome::Skipped {
                        reason: "already included — idempotent".into(),
                    }
                } else {
                    // Certification controls such as PROGRAM/LOGIC are
                    // scoped to the included book. Its definitions and
                    // theorem-neutral registries are imported, but its
                    // reader/admission mode must not leak into the parent.
                    let saved_program_mode = self.program_mode;
                    let included = self.process_file(&f, &selected_root, SourceRole::Include);
                    self.program_mode = saved_program_mode;
                    match included {
                        Ok(()) => {
                            include.status = IncludeStatus::Replayed;
                            EventOutcome::Skipped {
                                reason: "dependency included — its events are tallied above".into(),
                            }
                        }
                        Err(e) => {
                            self.seen.remove(&f);
                            include.status = match self.sources.last().map(|source| source.status) {
                                Some(SourceStatus::ReadFailed) => IncludeStatus::ReadFailed,
                                _ => IncludeStatus::ParseFailed,
                            };
                            include.detail = Some(e.to_string());
                            EventOutcome::Rejected {
                                reason: format!("include-book \"{name}\": {e}"),
                            }
                        }
                    }
                }
            }
        };
        self.includes[encounter_ordinal] = include;
        Ok(rec)
    }

    /// `(local event)` — process the contents (pass-1 style: a local defun
    /// IS installed for later events), tally the wrapper as skipped; an
    /// inner failure stays a rejection.
    fn process_local(
        &mut self,
        book: &str,
        file: &Path,
        lookup: &LookupRoot,
        items: &[SExpr],
    ) -> Result<EventRecord, BookError> {
        if items.len() != 2 {
            return Ok(EventRecord {
                book: book.to_string(),
                kind: "local".to_string(),
                label: "local".to_string(),
                outcome: EventOutcome::Rejected {
                    reason: "local takes exactly one event".into(),
                },
                notes: Vec::new(),
            });
        }
        let nested_start = self.events.len();
        let mut inner = self.process_event(book, file, lookup, &items[1])?;
        for nested in &mut self.events[nested_start..] {
            localize_event(nested);
        }
        localize_event(&mut inner);
        Ok(inner)
    }

    /// `(defthm name goal [:kw val …])` — keyword arguments are stripped and
    /// recorded; the bare event is driven through the session; the outcome
    /// class is decided by **re-checking the stored theorem** (the honesty
    /// boundary — see the module docs).
    fn process_defthm(&mut self, book: &str, items: &[SExpr]) -> EventRecord {
        let label = event_name(items);
        let mut rec = EventRecord {
            book: book.to_string(),
            kind: "defthm".to_string(),
            label: label.clone(),
            outcome: EventOutcome::Rejected {
                reason: String::new(),
            },
            notes: Vec::new(),
        };
        if items.len() < 3 {
            rec.outcome = EventOutcome::Rejected {
                reason: "defthm: expected (defthm name goal …)".into(),
            };
            return rec;
        }
        // Strip trailing keyword pairs (:hints, :rule-classes, …) — ignored
        // but recorded.
        let mut extras = &items[3..];
        while let Some(kw) = extras.first() {
            let Some(k) = kw.as_symbol().filter(|s| s.starts_with(':')) else {
                rec.outcome = EventOutcome::Rejected {
                    reason: format!(
                        "defthm: unexpected trailing argument {} (expected :keyword value pairs)",
                        summarize(kw)
                    ),
                };
                return rec;
            };
            if extras.len() < 2 {
                rec.outcome = EventOutcome::Rejected {
                    reason: format!("defthm: keyword {k} has no value"),
                };
                return rec;
            }
            rec.notes.push(format!("{k} ignored"));
            extras = &extras[2..];
        }
        let bare = SExpr::List(vec![
            items[0].clone(),
            items[1].clone(),
            self.rewrite_macro_aliases(&items[2]),
        ]);
        match self.sess.try_event(&bare) {
            Ok(Some(name)) => {
                // THE HONESTY BOUNDARY: classify off the stored theorem
                // itself, never off the event's success alone.
                let entry = self.sess.theorem_entry(&name);
                rec.outcome = match entry {
                    Some(t)
                        if matches!(
                            t.proof,
                            Acl2Proof::Certificate { .. } | Acl2Proof::Induction { .. }
                        ) && t.thm.hyps().is_empty() =>
                    {
                        EventOutcome::Transported
                    }
                    Some(t) => EventOutcome::Admitted {
                        hyps: t.thm.hyps().len(),
                    },
                    None => EventOutcome::Rejected {
                        reason: "internal: defthm reported success but stored no theorem".into(),
                    },
                };
            }
            Ok(None) => {
                rec.outcome = EventOutcome::Rejected {
                    reason: "malformed defthm event".into(),
                };
            }
            Err(e) => {
                rec.outcome = EventOutcome::Rejected {
                    reason: e.to_string(),
                };
            }
        }
        rec
    }
}

// ============================================================================
// Small render helpers
// ============================================================================

fn localize_event(event: &mut EventRecord) {
    if !event.kind.starts_with("local ") {
        event.kind = format!("local {}", event.kind);
    }
    event.outcome = match std::mem::replace(
        &mut event.outcome,
        EventOutcome::Rejected {
            reason: "localization placeholder".into(),
        },
    ) {
        EventOutcome::Rejected { reason } => EventOutcome::Rejected {
            reason: format!("local: {reason}"),
        },
        EventOutcome::Skipped { reason } => EventOutcome::Skipped {
            reason: format!("local: {reason}"),
        },
        EventOutcome::DeferredLogical { reason } => EventOutcome::DeferredLogical {
            reason: format!("local: {reason}"),
        },
        EventOutcome::DependencyInterface { sha256 } => {
            EventOutcome::DependencyInterface { sha256 }
        }
        EventOutcome::UnresolvedDependency { reason } => EventOutcome::UnresolvedDependency {
            reason: format!("local: {reason}"),
        },
        EventOutcome::LocalTransported => EventOutcome::LocalTransported,
        EventOutcome::Transported => EventOutcome::LocalTransported,
        EventOutcome::Admitted { .. } => EventOutcome::Skipped {
            reason: "local: processed (installed for this session), not exported".into(),
        },
    };
}

fn normalize_event_head(items: &[SExpr], head: &str) -> SExpr {
    let mut normalized = items.to_vec();
    normalized[0] = SExpr::symbol(head);
    SExpr::List(normalized)
}

fn call(name: &str, args: Vec<SExpr>) -> SExpr {
    SExpr::List(std::iter::once(SExpr::symbol(name)).chain(args).collect())
}

fn defun_form(name: &str, formals: Vec<SExpr>, body: SExpr) -> SExpr {
    SExpr::List(vec![
        SExpr::symbol("defun"),
        SExpr::symbol(name),
        SExpr::List(formals),
        body,
    ])
}

fn rejected_event(book: &str, kind: &str, label: &str, reason: &str) -> EventRecord {
    EventRecord {
        book: book.into(),
        kind: kind.into(),
        label: label.into(),
        outcome: EventOutcome::Rejected {
            reason: reason.into(),
        },
        notes: Vec::new(),
    }
}

fn theorem_macro_options(items: &[SExpr]) -> Result<Vec<(String, SExpr)>, String> {
    let mut out = Vec::new();
    let mut rest = items;
    while let Some(key_expr) = rest.first() {
        let Some(key) = key_expr.as_symbol().filter(|key| key.starts_with(':')) else {
            return Err("theorem macro: expected keyword/value options".into());
        };
        if rest.len() < 2 {
            return Err(format!("theorem macro: option {key} has no value"));
        }
        out.push((key.to_string(), rest[1].clone()));
        rest = &rest[2..];
    }
    Ok(out)
}

fn equivalence_option(key: &str) -> bool {
    matches!(
        key,
        ":package" | ":event-name" | ":rule-classes" | ":instructions" | ":hints" | ":otf-flg"
    )
}

fn generic_rule_option(key: &str) -> bool {
    matches!(
        key,
        ":name"
            | ":body"
            | ":disable"
            | ":requirement"
            | ":inst-rule-classes"
            | ":cheap-rule-classes"
            | ":rule-classes"
            | ":tags"
            | ":hints"
            | ":otf-flg"
    )
}

/// Events confined to host execution, diagnostics, compilation, or guard
/// checking. Keep this explicit: arbitrary `set-*` and `table` events can
/// affect logical admission or macro expansion and must remain rejected.
fn logic_irrelevant_event(head: &str) -> bool {
    matches!(
        head,
        "logic"
            | "verify-guards"
            | "set-inhibit-output-lst"
            | "set-inhibit-warnings"
            | "set-gag-mode"
            | "set-print-clause-ids"
            | "set-compile-fns"
            | "set-debugger-enable"
            | "set-parallel-execution"
            | "set-waterfall-parallelism"
    )
}

/// `std/util/define` options that leave the logical function body intact.
/// This is intentionally an allowlist; notably `:prepwork`, `:hooks`,
/// `:wrapper`, and unknown options require the real macro expansion.
fn define_metadata_option(keyword: &str) -> bool {
    matches!(
        keyword,
        ":guard"
            | ":measure"
            | ":guard-hints"
            | ":verify-guards"
            | ":returns"
            | ":parents"
            | ":short"
            | ":long"
            | ":enabled"
            | ":inline"
            | ":no-function"
            | ":irrelevant-formals-ok"
            | ":non-executable"
            | ":split-types"
            | ":ignore-ok"
            | ":hints"
            | ":mode"
    )
}

fn quoted_list(value: &SExpr) -> Option<&[SExpr]> {
    let list = value.as_list()?;
    if list.first().and_then(SExpr::as_symbol) == Some("quote") && list.len() == 2 {
        list[1].as_list()
    } else {
        Some(list)
    }
}

/// The event's name field (`(defun NAME …)` / `(defthm NAME …)`).
fn event_name(items: &[SExpr]) -> String {
    items
        .get(1)
        .and_then(SExpr::as_symbol)
        .map(str::to_string)
        .unwrap_or_else(|| "?".to_string())
}

/// The first argument, prettied (`in-package` / string args).
fn summarize_arg(items: &[SExpr]) -> String {
    items.get(1).map(summarize).unwrap_or_else(|| "?".into())
}

/// A short one-line rendering of a form (for labels).
fn summarize(e: &SExpr) -> String {
    match e {
        SExpr::Atom(covalence_sexp::Atom::Symbol(s)) => s.to_string(),
        SExpr::Atom(covalence_sexp::Atom::Str { bytes, .. }) => {
            format!("\"{}\"", String::from_utf8_lossy(bytes))
        }
        SExpr::List(items) => {
            let inner: Vec<String> = items.iter().take(3).map(summarize).collect();
            let ell = if items.len() > 3 { " …" } else { "" };
            format!("({}{})", inner.join(" "), ell)
        }
    }
}

/// Complete, deterministic S-expression rendering for future replay notes.
fn render_form(e: &SExpr) -> String {
    match e {
        SExpr::Atom(covalence_sexp::Atom::Symbol(s)) => s.to_string(),
        SExpr::Atom(covalence_sexp::Atom::Str { bytes, .. }) => {
            format!("\"{}\"", String::from_utf8_lossy(bytes))
        }
        SExpr::List(items) => format!(
            "({})",
            items.iter().map(render_form).collect::<Vec<_>>().join(" ")
        ),
    }
}
