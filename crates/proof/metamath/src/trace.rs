//! Proof **traces** and one-way conclusion **matching** — the substrate for a
//! LAMP-style ([lamp-guide.metamath.org]) interactive proof assistant.
//!
//! Two independent facilities live here, both strictly *untrusted consumers* of
//! [`crate::verify`]:
//!
//! * [`proof_trace`] — replay a `$p` theorem's proof and record, per step, the
//!   substitution that was **actually computed by the verifier**. This is the
//!   data behind LAMP's "click a step to see how the applied theorem's
//!   hypotheses map onto it" panel. It is produced by
//!   [`crate::verify::replay`] with a recording [`ReplayObserver`], i.e. by a
//!   *real verifying replay* — never reconstructed, guessed, or re-derived by a
//!   second implementation. If the proof does not verify, `proof_trace` fails
//!   exactly as [`crate::verify::verify_assertion`] does.
//! * [`match_conclusion`] — the one-step **backward** move: given a goal
//!   expression and a candidate assertion, solve for the assertion's frame
//!   variables so that its conclusion becomes the goal.
//!
//! Neither facility is trusted. A trace is a *view* of a proof that already
//! verified; a match is a *suggestion* whose only guarantee is stated in
//! [`match_conclusion`]'s contract. Every proof assembled on top of these must
//! still be checked end-to-end by the real verifier.
//!
//! [lamp-guide.metamath.org]: https://lamp-guide.metamath.org/

use std::collections::BTreeMap;

use crate::database::{Assertion, Database};
use crate::error::MmError;
use crate::expr::{Expr, Symbol, render};
use crate::subst::{Subst, apply_subst};
use crate::verify::{ReplayObserver, replay};

// ---------------------------------------------------------------------------
// Proof traces
// ---------------------------------------------------------------------------

/// What a [`TraceStep`] did.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TraceKind {
    /// A `$f` floating hypothesis pushed `typecode var`.
    FloatHyp,
    /// A `$e` essential hypothesis pushed its expression.
    EssentialHyp,
    /// An assertion (`$a`/`$p`) was applied.
    Assertion,
    /// A compressed-proof `Z` marker saved the top of stack to the heap.
    Save,
    /// A compressed-proof backreference re-pushed a saved heap entry.
    HeapRef,
}

impl TraceKind {
    /// The stable camelCase tag used on the wire.
    pub fn tag(self) -> &'static str {
        match self {
            TraceKind::FloatHyp => "floatHyp",
            TraceKind::EssentialHyp => "essentialHyp",
            TraceKind::Assertion => "assertion",
            TraceKind::Save => "save",
            TraceKind::HeapRef => "heapRef",
        }
    }
}

/// One hypothesis of an applied assertion, shown before and after the
/// substitution — the "how do this theorem's hypotheses map onto my step"
/// pairing. Floats come first (rendered as `typecode var` before, and as the
/// argument expression after), then essentials, matching argument order.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TraceHyp {
    /// The hypothesis's own label in the database.
    pub label: String,
    /// The hypothesis schema as written, rendered.
    pub before: String,
    /// The schema after applying the step's substitution, rendered. For a
    /// verifying replay this always equals the corresponding argument.
    pub after: String,
}

/// One recorded step of a verifying proof replay.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TraceStep {
    /// 0-based position in the trace.
    pub index: usize,
    /// The statement label, for the steps that have one. `None` for
    /// [`TraceKind::Save`] and [`TraceKind::HeapRef`], which reference the heap
    /// rather than a statement.
    pub label: Option<String>,
    /// What this step did.
    pub kind: TraceKind,
    /// The expression pushed by this step, rendered. For [`TraceKind::Save`]
    /// (which pushes nothing) this is the expression that was saved.
    pub expr: String,
    /// The stack depth *after* the step.
    pub stack_depth: usize,
    /// [`TraceKind::Assertion`] only: the popped arguments, rendered, in
    /// mandatory order (floats then essentials).
    pub args: Vec<String>,
    /// [`TraceKind::Assertion`] only: the substitution the verifier computed,
    /// as `(variable, rendered replacement body)`. The body carries no
    /// typecode — it is the symbol sequence spliced in place, exactly what
    /// [`apply_subst`] uses.
    pub subst: Vec<(String, String)>,
    /// [`TraceKind::Assertion`] only: the applied assertion's hypotheses,
    /// before and after the substitution.
    pub hyps: Vec<TraceHyp>,
    /// [`TraceKind::HeapRef`] only: the heap index that was re-pushed.
    pub heap_index: Option<usize>,
}

impl TraceStep {
    fn new(
        index: usize,
        kind: TraceKind,
        label: Option<String>,
        expr: &Expr,
        depth: usize,
    ) -> Self {
        Self {
            index,
            label,
            kind,
            expr: render(expr),
            stack_depth: depth,
            args: Vec::new(),
            subst: Vec::new(),
            hyps: Vec::new(),
            heap_index: None,
        }
    }
}

/// Render a substitution's replacement body (a bare symbol sequence, no
/// typecode) to its flat surface form.
fn render_body(body: &[Symbol]) -> String {
    let mut out = String::new();
    for (i, s) in body.iter().enumerate() {
        if i > 0 {
            out.push(' ');
        }
        out.push_str(s.as_str());
    }
    out
}

/// The [`ReplayObserver`] that turns a verifying replay into a [`TraceStep`]
/// list.
#[derive(Default)]
struct TraceRecorder {
    steps: Vec<TraceStep>,
}

impl ReplayObserver for TraceRecorder {
    fn float_hyp(&mut self, label: &str, pushed: &Expr, depth: usize) {
        let i = self.steps.len();
        self.steps.push(TraceStep::new(
            i,
            TraceKind::FloatHyp,
            Some(label.to_string()),
            pushed,
            depth,
        ));
    }

    fn essential_hyp(&mut self, label: &str, pushed: &Expr, depth: usize) {
        let i = self.steps.len();
        self.steps.push(TraceStep::new(
            i,
            TraceKind::EssentialHyp,
            Some(label.to_string()),
            pushed,
            depth,
        ));
    }

    fn assertion(
        &mut self,
        label: &str,
        target: &Assertion,
        args: &[Expr],
        subst: &Subst,
        pushed: &Expr,
        depth: usize,
    ) {
        let i = self.steps.len();
        let mut step = TraceStep::new(
            i,
            TraceKind::Assertion,
            Some(label.to_string()),
            pushed,
            depth,
        );
        step.args = args.iter().map(render).collect();
        step.subst = subst
            .iter()
            .map(|(v, body)| (v.clone(), render_body(body)))
            .collect();
        // Floats first, then essentials — the mandatory order the verifier
        // popped `args` in, so `hyps[k].after == args[k]`.
        for f in &target.frame.floats {
            let schema = crate::expr::make_expr(&f.typecode, [f.var.as_str()]);
            step.hyps.push(TraceHyp {
                label: f.label.clone(),
                before: render(&schema),
                after: render(&apply_subst(&schema, subst)),
            });
        }
        for h in &target.frame.essentials {
            step.hyps.push(TraceHyp {
                label: h.label.clone(),
                before: render(&h.expr),
                after: render(&apply_subst(&h.expr, subst)),
            });
        }
        self.steps.push(step);
    }

    fn save(&mut self, saved: &Expr, depth: usize) {
        let i = self.steps.len();
        self.steps
            .push(TraceStep::new(i, TraceKind::Save, None, saved, depth));
    }

    fn heap(&mut self, idx: usize, pushed: &Expr, depth: usize) {
        let i = self.steps.len();
        let mut step = TraceStep::new(i, TraceKind::HeapRef, None, pushed, depth);
        step.heap_index = Some(idx);
        self.steps.push(step);
    }
}

/// Replay `assertion`'s proof and record every step.
///
/// The replay is [`crate::verify::replay`] — the same stack/heap discipline,
/// the same typecode, hypothesis, and `$d` checks, in the same order — so a
/// successful trace *is* a successful verification and every recorded
/// substitution is the one the checker actually derived. An error is returned
/// verbatim when the proof does not verify. A `$a` axiom (no proof) traces to
/// an empty step list.
///
/// Compressed proofs keep their sharing: a `Z` save and a heap backreference
/// appear as their own steps ([`TraceKind::Save`] / [`TraceKind::HeapRef`])
/// rather than re-expanding the shared sub-proof, so the trace length is linear
/// in the encoded proof, not in its expansion.
pub fn proof_trace(db: &Database, assertion: &Assertion) -> Result<Vec<TraceStep>, MmError> {
    let mut rec = TraceRecorder::default();
    replay(db, assertion, &mut rec)?;
    Ok(rec.steps)
}

// ---------------------------------------------------------------------------
// One-way conclusion matching (the backward step)
// ---------------------------------------------------------------------------

/// Cap on the number of variable-segmentation choices explored by
/// [`match_conclusion`]. Exceeding it aborts the search and yields `None` — a
/// refusal, never a wrong answer.
const MATCH_BUDGET: usize = 200_000;

/// One-way match of a goal expression against `target`'s conclusion schema,
/// solving for `target`'s mandatory (frame) floating variables.
///
/// This is the backward proof step: "which substitution makes `target`'s
/// conclusion equal to what I am trying to prove?". It is *matching*, not
/// unification — symbols of `goal` are literals, only `target`'s frame float
/// variables are solved for. (A variable of the *ambient* database that happens
/// to share a name with a frame variable of `target` is therefore treated as a
/// literal on the goal side, which is correct: the two live in different
/// scopes.)
///
/// # Guarantee
///
/// If this returns `Some(σ)` then `apply_subst(&target.conclusion, &σ) == *goal`
/// **exactly** — that equality is re-checked before returning, so a bogus match
/// can never be reported as a success. Since a Metamath verifier compares
/// expressions as flat symbol sequences and nothing else, that is precisely the
/// condition under which applying `target` yields `goal`.
///
/// # What it does *not* guarantee
///
/// * **Typecodes / grammar.** Each variable is bound to a symbol *sequence*
///   only. Whether that sequence is a well-formed expression of the variable's
///   typecode is a grammar question, and this crate deliberately has no grammar
///   (see the crate docs). A match may therefore be grammatically nonsense; the
///   resulting `$f` subgoal will simply be unprovable. Callers must verify the
///   assembled proof.
/// * **Uniqueness.** Where the schema admits several segmentations, the first
///   found (leftmost variable, shortest binding first) is returned. `set.mm`'s
///   grammar is unambiguous, so in practice this is *the* match; a database with
///   an ambiguous grammar may have others.
/// * **Variables not determined by the conclusion.** A frame float occurring
///   only in `target`'s essential hypotheses cannot be solved from the goal and
///   is simply absent from the returned substitution. Callers should surface
///   those as unknowns rather than treating the map as total.
/// * **Completeness.** The search is bounded by [`MATCH_BUDGET`]; a pathological
///   schema aborts to `None` rather than running away.
///
/// Returns `None` if the typecodes differ, if no segmentation matches, or if the
/// budget is exhausted.
pub fn match_conclusion(_db: &Database, target: &Assertion, goal: &Expr) -> Option<Subst> {
    if target.conclusion.typecode != goal.typecode {
        return None;
    }
    // Only the mandatory floats are solvable variables.
    let vars: std::collections::HashSet<&str> =
        target.frame.floats.iter().map(|f| f.var.as_str()).collect();

    let mut subst: Subst = BTreeMap::new();
    let mut budget = MATCH_BUDGET;
    if !match_body(
        &target.conclusion.body,
        &goal.body,
        &vars,
        &mut subst,
        &mut budget,
    ) {
        return None;
    }
    // Re-derive and re-check: the returned substitution must reproduce the goal
    // exactly. This is what makes a wrong "success" impossible.
    if apply_subst(&target.conclusion, &subst) != *goal {
        return None;
    }
    Some(subst)
}

/// Backtracking match of a schema symbol sequence against a ground one.
///
/// Every variable binds to a **non-empty** sequence: a Metamath expression of
/// any typecode has at least one symbol, so an empty binding can never be a
/// legitimate match, and forbidding it both prunes the search and keeps the
/// result meaningful. Constants must match position-for-position; a variable's
/// second and later occurrences must reproduce their first binding.
fn match_body(
    schema: &[Symbol],
    goal: &[Symbol],
    vars: &std::collections::HashSet<&str>,
    subst: &mut Subst,
    budget: &mut usize,
) -> bool {
    let Some((head, rest)) = schema.split_first() else {
        return goal.is_empty();
    };
    if *budget == 0 {
        return false;
    }
    *budget -= 1;

    let name = head.as_str();
    if !vars.contains(name) {
        // A constant (or a variable not in the target's frame): literal match.
        return match goal.split_first() {
            Some((g, grest)) if g == head => match_body(rest, grest, vars, subst, budget),
            _ => false,
        };
    }

    if let Some(bound) = subst.get(name) {
        // Already solved: the goal must continue with exactly that sequence.
        if goal.len() < bound.len() || &goal[..bound.len()] != bound.as_slice() {
            return false;
        }
        let n = bound.len();
        return match_body(rest, &goal[n..], vars, subst, budget);
    }

    // Unsolved: try every non-empty split, shortest first. `rest` needs at
    // least one goal symbol per remaining schema symbol (each variable binds to
    // ≥1 symbol), which bounds how much this variable may consume.
    let max = goal.len().saturating_sub(rest.len());
    for take in 1..=max {
        subst.insert(name.to_string(), goal[..take].to_vec());
        if match_body(rest, &goal[take..], vars, subst, budget) {
            return true;
        }
        subst.remove(name);
        if *budget == 0 {
            return false;
        }
    }
    false
}

// TODO(cov:proof.metamath.proof-search, major): No bottom-up or iterative-deepening
// proof search — `match_conclusion` is a single backward step against one named
// assertion. A "find assertions whose conclusion matches this goal" sweep, and
// search over the resulting tree, are the next layer.

// PERF(cov:proof.metamath.match-conclusion-backtracking, minor): `match_body` is
// exponential in the number of consecutive schema variables in the worst case
// and is capped by `MATCH_BUDGET`. A typecode-driven grammar parse of the goal
// would make matching linear and would additionally rule out the grammatically
// ill-formed bindings documented on `match_conclusion`; that needs the deferred
// structured-tree encoding.

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::make_expr;
    use crate::parse::parse;

    /// The "demo0" database from the Metamath book, with a normal proof.
    const DEMO0: &str = "\
        $c 0 + = -> ( ) term wff |- $.\n\
        $v t r s P Q $.\n\
        tt $f term t $.\n\
        tr $f term r $.\n\
        ts $f term s $.\n\
        wp $f wff P $.\n\
        wq $f wff Q $.\n\
        tze $a term 0 $.\n\
        tpl $a term ( t + r ) $.\n\
        weq $a wff t = r $.\n\
        wim $a wff ( P -> Q ) $.\n\
        a1 $a |- ( t = r -> ( t = s -> r = s ) ) $.\n\
        a2 $a |- ( t + 0 ) = t $.\n\
        ${  min $e |- P $.  maj $e |- ( P -> Q ) $.\n\
            mp $a |- Q $.\n\
        $}\n\
        th1 $p |- t = t $= tt tze tpl tt weq tt tt weq tt a2 tt tze tpl \
            tt weq tt tze tpl tt weq tt tt weq wim tt a2 tt tze tpl \
            tt tt a1 mp mp $.\n\
    ";

    /// The same database, with `th1` compressed *and* using `Z` save markers.
    const DEMO0_COMPRESSED: &str = "\
        $c 0 + = -> ( ) term wff |- $.\n\
        $v t r s P Q $.\n\
        tt $f term t $.\n\
        tr $f term r $.\n\
        ts $f term s $.\n\
        wp $f wff P $.\n\
        wq $f wff Q $.\n\
        tze $a term 0 $.\n\
        tpl $a term ( t + r ) $.\n\
        weq $a wff t = r $.\n\
        wim $a wff ( P -> Q ) $.\n\
        a1 $a |- ( t = r -> ( t = s -> r = s ) ) $.\n\
        a2 $a |- ( t + 0 ) = t $.\n\
        ${  min $e |- P $.  maj $e |- ( P -> Q ) $.\n\
            mp $a |- Q $.\n\
        $}\n\
        th1 $p |- t = t $= ( tze tpl weq wim a2 a1 mp ) ABCADZAADZAFZIIJEKABCAAGHH $.\n\
    ";

    fn assertion<'a>(db: &'a Database, label: &str) -> &'a Assertion {
        match db.statement_by_label(label) {
            Some(crate::database::Statement::Assert(a)) => a,
            _ => panic!("no assertion `{label}`"),
        }
    }

    /// Every trace is internally coherent: indices are dense, the stack depth
    /// evolves exactly as the step kind demands, and the last step leaves
    /// exactly one expression — the conclusion — on the stack.
    fn check_coherent(steps: &[TraceStep], concl: &Expr) {
        let mut depth = 0usize;
        for (i, s) in steps.iter().enumerate() {
            assert_eq!(s.index, i, "trace indices must be dense and in order");
            match s.kind {
                // `Save` pushes nothing.
                TraceKind::Save => {}
                // Every other kind is a net +1 relative to what it consumed.
                TraceKind::Assertion => {
                    let popped = s.hyps.len();
                    assert!(depth >= popped, "step {i} underflows the stack");
                    depth -= popped;
                    depth += 1;
                }
                _ => depth += 1,
            }
            assert_eq!(s.stack_depth, depth, "step {i} reports the wrong depth");
        }
        assert_eq!(depth, 1, "a verified proof leaves exactly one result");
        assert_eq!(
            steps.last().expect("non-empty proof").expr,
            render(concl),
            "the final step must push the claimed conclusion"
        );
    }

    #[test]
    fn trace_normal_proof() {
        let db = parse(DEMO0).unwrap();
        let a = assertion(&db, "th1");
        let steps = proof_trace(&db, a).unwrap();

        // A normal proof has one step per label and no heap traffic.
        let Some(crate::database::Proof::Normal(labels)) = &a.proof else {
            panic!("th1 has a normal proof here");
        };
        assert_eq!(steps.len(), labels.len());
        assert_eq!(steps.len(), 34);
        assert!(steps.iter().all(|s| s.kind != TraceKind::Save));
        assert!(steps.iter().all(|s| s.kind != TraceKind::HeapRef));
        check_coherent(&steps, &a.conclusion);

        // The first step is the `tt` float hypothesis pushing `term t`.
        assert_eq!(steps[0].kind, TraceKind::FloatHyp);
        assert_eq!(steps[0].label.as_deref(), Some("tt"));
        assert_eq!(steps[0].expr, "term t");

        // The final step is the outer `mp`, and its recorded substitution is the
        // one the verifier actually used: Q := t = t.
        let last = steps.last().unwrap();
        assert_eq!(last.kind, TraceKind::Assertion);
        assert_eq!(last.label.as_deref(), Some("mp"));
        assert_eq!(last.expr, "|- t = t");
        let q = last
            .subst
            .iter()
            .find(|(v, _)| v == "Q")
            .expect("mp binds Q");
        assert_eq!(q.1, "t = t");

        // Its hypotheses line up with its arguments, after substitution.
        assert_eq!(last.hyps.len(), last.args.len());
        for (h, arg) in last.hyps.iter().zip(&last.args) {
            assert_eq!(
                &h.after, arg,
                "hypothesis {} must match its argument",
                h.label
            );
        }
        let maj = last.hyps.iter().find(|h| h.label == "maj").unwrap();
        assert_eq!(maj.before, "|- ( P -> Q )");
        assert_eq!(maj.after, "|- ( ( t + 0 ) = t -> t = t )");
    }

    #[test]
    fn trace_compressed_proof_preserves_sharing() {
        let db = parse(DEMO0_COMPRESSED).unwrap();
        let a = assertion(&db, "th1");
        let steps = proof_trace(&db, a).unwrap();

        check_coherent(&steps, &a.conclusion);

        // The `Z` markers and their backreferences are recorded as steps rather
        // than re-expanded, so the shared sub-proof appears once.
        let saves = steps.iter().filter(|s| s.kind == TraceKind::Save).count();
        let refs = steps
            .iter()
            .filter(|s| s.kind == TraceKind::HeapRef)
            .count();
        assert_eq!(saves, 3, "the letter block has three `Z` markers");
        assert!(refs > 0, "the saved sub-proofs must be re-used");
        // Sharing is a win: fewer steps than the 34 of the equivalent normal
        // proof, even counting the `Z` markers as steps of their own.
        assert!(
            steps.len() < 34,
            "sharing must shorten the trace (got {})",
            steps.len()
        );

        // A save records the expression it saved without changing the depth.
        let save = steps.iter().find(|s| s.kind == TraceKind::Save).unwrap();
        assert!(save.label.is_none());
        let before = &steps[save.index - 1];
        assert_eq!(save.expr, before.expr);
        assert_eq!(save.stack_depth, before.stack_depth);

        // A backreference re-pushes exactly what was saved.
        let href = steps.iter().find(|s| s.kind == TraceKind::HeapRef).unwrap();
        let idx = href.heap_index.expect("a heapRef records its heap index");
        let nth_save = steps
            .iter()
            .filter(|s| s.kind == TraceKind::Save)
            .nth(idx)
            .unwrap();
        assert_eq!(href.expr, nth_save.expr);
    }

    #[test]
    fn trace_axiom_is_empty() {
        let db = parse(DEMO0).unwrap();
        assert!(proof_trace(&db, assertion(&db, "a1")).unwrap().is_empty());
    }

    #[test]
    fn trace_rejects_a_bad_proof() {
        // The trace is a verifying replay: a broken proof must fail, not trace.
        let input = DEMO0.replace(
            "$= tt tze tpl tt weq tt tt weq tt a2 tt tze tpl \
            tt weq tt tze tpl tt weq tt tt weq wim tt a2 tt tze tpl \
            tt tt a1 mp mp $.",
            "$= tt tze tpl tt weq $.",
        );
        let db = parse(&input).unwrap();
        assert!(proof_trace(&db, assertion(&db, "th1")).is_err());
    }

    /// The real `hol.mm` fixture the crate's other tests use — a database with
    /// compressed proofs at a realistic scale.
    #[test]
    fn trace_hol_mm_fixture() {
        let src = include_str!("../tests/fixtures/hol.mm");
        let db = parse(src).unwrap();

        let mut traced = 0usize;
        for a in db.assertions() {
            if a.proof.is_none() {
                continue;
            }
            let steps = proof_trace(&db, a).unwrap();
            check_coherent(&steps, &a.conclusion);
            traced += 1;
        }
        assert!(traced > 100, "hol.mm should have many theorems ({traced})");
    }

    /// Every assertion application recorded in a real trace is reproducible:
    /// applying the recorded substitution to the applied assertion's conclusion
    /// gives the recorded pushed expression.
    #[test]
    fn hol_mm_traces_are_reproducible() {
        let src = include_str!("../tests/fixtures/hol.mm");
        let db = parse(src).unwrap();
        let a = db
            .assertions()
            .find(|a| a.proof.is_some() && a.frame.essentials.len() > 1)
            .expect("hol.mm has a theorem with essential hypotheses");
        let steps = proof_trace(&db, a).unwrap();
        for s in steps.iter().filter(|s| s.kind == TraceKind::Assertion) {
            let target = assertion(&db, s.label.as_deref().unwrap());
            let sub: Subst = s
                .subst
                .iter()
                .map(|(v, body)| {
                    (
                        v.clone(),
                        body.split_whitespace().map(Symbol::from).collect(),
                    )
                })
                .collect();
            assert_eq!(render(&apply_subst(&target.conclusion, &sub)), s.expr);
        }
    }

    // --- match_conclusion ---------------------------------------------------

    #[test]
    fn match_simple_conclusion() {
        let db = parse(DEMO0).unwrap();
        // a2's conclusion is `|- ( t + 0 ) = t`; match `|- ( 0 + 0 ) = 0`.
        let goal = make_expr("|-", ["(", "0", "+", "0", ")", "=", "0"]);
        let s = match_conclusion(&db, assertion(&db, "a2"), &goal).expect("a2 matches");
        assert_eq!(render_body(&s["t"]), "0");
        assert_eq!(apply_subst(&assertion(&db, "a2").conclusion, &s), goal);
    }

    #[test]
    fn match_solves_a_compound_variable() {
        let db = parse(DEMO0).unwrap();
        // wim's conclusion is `wff ( P -> Q )`; the variables must absorb whole
        // sub-expressions, which naive left-to-right greed gets wrong.
        let goal = make_expr(
            "wff",
            [
                "(", "(", "t", "=", "r", ")", "->", "(", "r", "=", "s", ")", ")",
            ],
        );
        let s = match_conclusion(&db, assertion(&db, "wim"), &goal).expect("wim matches");
        assert_eq!(render_body(&s["P"]), "( t = r )");
        assert_eq!(render_body(&s["Q"]), "( r = s )");
    }

    #[test]
    fn match_respects_repeated_variables() {
        let db = parse(DEMO0).unwrap();
        // weq's conclusion is `wff t = r`, with two *distinct* variables, so an
        // asymmetric goal is fine...
        let goal = make_expr("wff", ["0", "=", "(", "0", "+", "0", ")"]);
        let s = match_conclusion(&db, assertion(&db, "weq"), &goal).expect("weq matches");
        assert_eq!(render_body(&s["t"]), "0");
        assert_eq!(render_body(&s["r"]), "( 0 + 0 )");

        // ...but a2's conclusion `|- ( t + 0 ) = t` repeats `t`, so both
        // occurrences must agree. This one cannot, and must be refused.
        let goal = make_expr(
            "|-",
            ["(", "0", "+", "0", ")", "=", "(", "0", "+", "0", ")"],
        );
        assert!(
            match_conclusion(&db, assertion(&db, "a2"), &goal).is_none(),
            "must not invent a match where `t` would need two values"
        );
    }

    #[test]
    fn match_rejects_non_matches() {
        let db = parse(DEMO0).unwrap();
        let a2 = assertion(&db, "a2");

        // Wrong typecode.
        let goal = make_expr("wff", ["(", "0", "+", "0", ")", "=", "0"]);
        assert!(match_conclusion(&db, a2, &goal).is_none());

        // Wrong constant skeleton (`*` where the schema demands `+`).
        let goal = make_expr("|-", ["(", "0", "+", "0", ")", "=", "0"]);
        assert!(match_conclusion(&db, assertion(&db, "a1"), &goal).is_none());

        // Too short to fill the schema's constants.
        let goal = make_expr("|-", ["0"]);
        assert!(match_conclusion(&db, a2, &goal).is_none());

        // A variable may never bind to nothing: `wff t = r` cannot match `wff =`.
        let goal = make_expr("wff", ["="]);
        assert!(match_conclusion(&db, assertion(&db, "weq"), &goal).is_none());
    }

    #[test]
    fn match_never_reports_a_wrong_substitution() {
        // Whatever `match_conclusion` returns, re-applying it must rebuild the
        // goal exactly — checked here against every assertion of a real
        // database, so a wrong "success" anywhere would be caught.
        let src = include_str!("../tests/fixtures/hol.mm");
        let db = parse(src).unwrap();
        let goals: Vec<Expr> = db
            .assertions()
            .filter(|a| a.proof.is_some())
            .take(200)
            .map(|a| a.conclusion.clone())
            .collect();
        let mut hits = 0usize;
        for target in db.assertions() {
            for goal in &goals {
                if let Some(s) = match_conclusion(&db, target, goal) {
                    assert_eq!(
                        apply_subst(&target.conclusion, &s),
                        *goal,
                        "`{}` reported a substitution that does not rebuild the goal",
                        target.label
                    );
                    hits += 1;
                }
            }
        }
        assert!(hits > 0, "some assertion should match some goal");
    }

    #[test]
    fn match_is_one_way() {
        // The goal is literal: a *goal* variable is never solved for. `weq`'s
        // conclusion `wff t = r` matches the goal `wff t = r` only by binding
        // `t := t`, `r := r` — it does not unify in the other direction.
        let db = parse(DEMO0).unwrap();
        let goal = make_expr("wff", ["s", "=", "s"]);
        let s = match_conclusion(&db, assertion(&db, "weq"), &goal).expect("matches");
        assert_eq!(render_body(&s["t"]), "s");
        assert_eq!(render_body(&s["r"]), "s");
    }
}
