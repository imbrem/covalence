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
//!   proved on the reified-certificate path ([`Acl2Proof::Certificate`] —
//!   `⊢ Derivable_ACL2 ⌜goal⌝` → soundness metatheorem → the base-HOL model
//!   equation). Anything else is downgraded to *admitted*.
//! - **admitted (in dialect)** covers installed `defun`s (kernel
//!   *hypotheses*, never axioms) and reduction-path `defthm`s (genuine kernel
//!   theorems whose hypotheses are exactly the `defun` equations used — the
//!   report says how many ride).
//! - **skipped** covers `in-package`, `include-book` dependencies (satisfied
//!   includes are themselves skips whose *contents* are tallied as their own
//!   events; missing / `:dir` / already-included ones are recorded, never
//!   errors), and `local` wrappers (contents processed, pass-1 style).
//! - **rejected** records a reason and processing continues (best-effort
//!   tally; ACL2 itself would fail certification at the first error).
//!
//! # Path confinement
//!
//! Every path — the top-level book and every `include-book` — is resolved
//! **inside a configured root**: absolute paths and `..` components are
//! rejected lexically, then the resolved file is canonicalized and required
//! to stay under the canonical root (symlink-safe). The server's `/api/lisp`
//! endpoint forwards cells to `Session::eval_cell`, so `#book` cannot read or
//! traverse outside the directory the server was started in.

use std::collections::BTreeSet;
use std::fmt;
use std::path::{Component, Path, PathBuf};

use covalence_sexp::SExpr;

use crate::acl2::{Acl2Proof, Acl2Session};
use crate::reader::read_book;

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
    /// model equation**, proved via the reified certificate path —
    /// re-checked at this boundary, never taken on faith.
    Transported,
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
    /// Rejected (reason says why); processing continued.
    Rejected {
        /// Why the event was rejected.
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
}

/// The summary counts of a [`BookReport`].
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Tally {
    /// Closed base-HOL theorems minted via the certificate path.
    pub transported: usize,
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
        self.transported + self.admitted + self.skipped + self.rejected
    }
}

impl BookReport {
    /// The summary tally.
    pub fn tally(&self) -> Tally {
        let mut t = Tally::default();
        for e in &self.events {
            match e.outcome {
                EventOutcome::Transported => t.transported += 1,
                EventOutcome::Admitted { .. } => t.admitted += 1,
                EventOutcome::Skipped { .. } => t.skipped += 1,
                EventOutcome::Rejected { .. } => t.rejected += 1,
            }
        }
        t
    }

    /// Find the record for a named event (first match).
    pub fn event(&self, label: &str) -> Option<&EventRecord> {
        self.events.iter().find(|e| e.label == label)
    }
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
                    "closed base-HOL model equation (certificate path)".to_string(),
                ),
                EventOutcome::Admitted { hyps: 0 } => ("admitted", "in dialect, closed".into()),
                EventOutcome::Admitted { hyps } => (
                    "admitted",
                    format!("in dialect, rides {hyps} defun hypothesis(es)"),
                ),
                EventOutcome::Skipped { reason } => ("skipped", reason.clone()),
                EventOutcome::Rejected { reason } => ("REJECTED", reason.clone()),
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
             {} admitted in dialect, {} skipped, {} rejected",
            t.transported,
            t.total(),
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

/// Resolve `rel` against `base_dir`, confined to `root` (both canonical):
/// reject absolute paths and any `..` component lexically, then canonicalize
/// and require the result to remain under `root` (symlink-safe).
fn confine(root: &Path, base_dir: &Path, rel: &str) -> Result<Resolved, String> {
    let p = Path::new(rel);
    if p.is_absolute() {
        return Err("absolute paths are not allowed (book paths are root-relative)".into());
    }
    if p.components()
        .any(|c| matches!(c, Component::ParentDir | Component::Prefix(_)))
    {
        return Err("`..` components are not allowed (must stay inside the book root)".into());
    }
    let joined = base_dir.join(p);
    match joined.canonicalize() {
        Ok(canon) => {
            if canon.starts_with(root) {
                Ok(Resolved::Found(canon))
            } else {
                Err("resolves outside the book root".into())
            }
        }
        Err(_) => Ok(Resolved::Missing(joined)),
    }
}

/// `name` with a `.lisp` extension appended if it has none (the ACL2
/// `include-book` convention names books without the extension).
fn with_lisp_ext(name: &str) -> String {
    if name.ends_with(".lisp") {
        name.to_string()
    } else {
        format!("{name}.lisp")
    }
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
    root: PathBuf,
    /// Canonical paths already included (re-inclusion is idempotent).
    seen: BTreeSet<PathBuf>,
    events: Vec<EventRecord>,
}

/// **Run a book**: resolve `path` (a root-relative `.lisp` path; the
/// extension may be omitted) inside `root`, process its events through
/// `sess`, and return the tally report. Only top-level resolution / read /
/// parse failures are `Err` — event failures are tallied.
pub fn run_book(sess: &mut Acl2Session, root: &Path, path: &str) -> Result<BookReport, BookError> {
    let root = root
        .canonicalize()
        .map_err(|e| BookError::Root(root.to_path_buf(), e.to_string()))?;
    let rel = with_lisp_ext(path);
    let file = match confine(&root, &root, &rel) {
        Ok(Resolved::Found(f)) => f,
        Ok(Resolved::Missing(p)) => {
            return Err(BookError::Path(rel, format!("not found ({})", p.display())));
        }
        Err(reason) => return Err(BookError::Path(rel, reason)),
    };
    let mut pipe = Pipeline {
        sess,
        root: root.clone(),
        seen: BTreeSet::new(),
        events: Vec::new(),
    };
    let display = display_rel(&root, &file);
    pipe.seen.insert(file.clone());
    pipe.process_file(&file)?;
    Ok(BookReport {
        path: display,
        events: pipe.events,
    })
}

impl Pipeline<'_> {
    /// Read + parse one book file and process its events in order.
    fn process_file(&mut self, file: &Path) -> Result<(), BookError> {
        let src = std::fs::read_to_string(file)
            .map_err(|e| BookError::Io(file.to_path_buf(), e.to_string()))?;
        let forms =
            read_book(&src).map_err(|e| BookError::Parse(file.to_path_buf(), e.to_string()))?;
        let book = display_rel(&self.root, file);
        for form in &forms {
            let rec = self.process_event(&book, file, form)?;
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
        match head {
            "in-package" => Ok(rec(
                "in-package",
                summarize_arg(items),
                EventOutcome::Skipped {
                    reason: "single-package slice — recorded, no-op".into(),
                },
            )),
            "include-book" => self.process_include(book, file, items),
            "local" => self.process_local(book, file, items),
            "defun" => {
                let label = event_name(items);
                match self.sess.try_event(form) {
                    Ok(Some(name)) => Ok(rec("defun", name, EventOutcome::Admitted { hyps: 0 })),
                    Ok(None) => Ok(rec(
                        "defun",
                        label,
                        EventOutcome::Rejected {
                            reason: "malformed defun event".into(),
                        },
                    )),
                    Err(e) => Ok(rec(
                        "defun",
                        label,
                        EventOutcome::Rejected {
                            reason: e.to_string(),
                        },
                    )),
                }
            }
            "defthm" => Ok(self.process_defthm(book, items)),
            other => Ok(rec(
                other,
                event_name(items),
                EventOutcome::Rejected {
                    reason: format!(
                        "`{other}` events are not supported in this slice \
                         (supported: in-package, include-book, defun, defthm, local)"
                    ),
                },
            )),
        }
    }

    /// `(include-book "name" [:dir …])` — resolve relative to the including
    /// book's directory, confined to the root; recurse when found.
    fn process_include(
        &mut self,
        book: &str,
        file: &Path,
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
        let name = match items.get(1).and_then(|a| a.as_str()) {
            Some(("", bytes)) => String::from_utf8_lossy(bytes).into_owned(),
            _ => {
                rec.outcome = EventOutcome::Rejected {
                    reason: "include-book: expected a book name string".into(),
                };
                return Ok(rec);
            }
        };
        rec.label = name.clone();
        if items.len() > 2 {
            // Keyword options (`:dir` is the common one): no system book
            // directory is configured in this slice.
            rec.outcome = EventOutcome::Skipped {
                reason: "include-book options (e.g. :dir) are not configured — \
                         dependency skipped"
                    .into(),
            };
            return Ok(rec);
        }
        let base_dir = file.parent().unwrap_or(&self.root).to_path_buf();
        rec.outcome = match confine(&self.root, &base_dir, &with_lisp_ext(&name)) {
            Err(reason) => EventOutcome::Rejected {
                reason: format!("include-book \"{name}\": {reason}"),
            },
            Ok(Resolved::Missing(p)) => EventOutcome::Skipped {
                reason: format!("dependency not found ({}) — skipped", p.display()),
            },
            Ok(Resolved::Found(f)) => {
                if !self.seen.insert(f.clone()) {
                    EventOutcome::Skipped {
                        reason: "already included — idempotent".into(),
                    }
                } else {
                    self.process_file(&f)?;
                    EventOutcome::Skipped {
                        reason: "dependency included — its events are tallied above".into(),
                    }
                }
            }
        };
        Ok(rec)
    }

    /// `(local event)` — process the contents (pass-1 style: a local defun
    /// IS installed for later events), tally the wrapper as skipped; an
    /// inner failure stays a rejection.
    fn process_local(
        &mut self,
        book: &str,
        file: &Path,
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
        let mut inner = self.process_event(book, file, &items[1])?;
        inner.kind = format!("local {}", inner.kind);
        inner.outcome = match inner.outcome {
            EventOutcome::Rejected { reason } => EventOutcome::Rejected {
                reason: format!("local: {reason}"),
            },
            EventOutcome::Skipped { reason } => EventOutcome::Skipped {
                reason: format!("local: {reason}"),
            },
            // Genuinely processed — but a local event is not exported, so
            // it is tallied as skipped (see the design note: pass-1 only).
            EventOutcome::Transported | EventOutcome::Admitted { .. } => EventOutcome::Skipped {
                reason: "local: processed (installed for this session), not exported".into(),
            },
        };
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
        let bare = SExpr::List(vec![items[0].clone(), items[1].clone(), items[2].clone()]);
        match self.sess.try_event(&bare) {
            Ok(Some(name)) => {
                // THE HONESTY BOUNDARY: classify off the stored theorem
                // itself, never off the event's success alone.
                let entry = self.sess.theorem_entry(&name);
                rec.outcome = match entry {
                    Some(t)
                        if matches!(t.proof, Acl2Proof::Certificate { .. })
                            && t.thm.hyps().is_empty() =>
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
