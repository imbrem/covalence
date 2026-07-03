//! **Metamath-PA → HOL replay** — the constructive `∃P.ValidProof ⟹ ⊢⟦S⟧`
//! bridge (`notes/vibes/theories-models-and-logics.md §5.6`).
//!
//! This mirrors the structure of `covalence-alethe`'s "untrusted proof → kernel
//! re-derivation": given a **verified** Metamath proof in the PA database
//! ([`crate::peano::mm_pa`]), [`replay_assertion`] walks the proof and builds
//! the kernel theorem `⊢ ⟦S⟧` **step by step**, re-deriving every step in the
//! kernel. **The Metamath proof is untrusted** — [`crate::metamath::verify`]'s
//! say-so is *not* trusted for the HOL theorem; the kernel re-checks each rule:
//!
//! | Metamath step                | HOL re-derivation                          |
//! |------------------------------|--------------------------------------------|
//! | PA-axiom instance `pa.i`     | its proven [`crate::init::nat`] denotation |
//! | modus ponens `ax.mp`         | [`Thm::imp_elim`]                          |
//! | generalisation `ax.gen`      | [`Thm::all_intro`]                         |
//! | induction `pa.ind` instance  | [`Thm::nat_induct`] on the *concrete* motive |
//!
//! ## The interpretation `⟦·⟧`
//!
//! A Metamath PA expression (`term`/`wff`/`|-` flat list) is parsed back into
//! the locally-nameless [`Fol`] AST by [`expr_to_term`] / [`expr_to_form`]
//! (named setvars → de Bruijn under `A.`/`E.`, free setvars → `Fol::FVar`), then
//! denoted into HOL `nat`/`bool` by [`crate::peano::deep::denote_closed`] — the
//! same standard interpretation the impredicative engine's `project` lands on.
//! So `⟦PA3⟧` *is* `init::nat::add_base`'s conclusion (up to β).
//!
//! ## How this sidesteps the motive wall
//!
//! The impredicative `Derivable_PA` engine could not *construct* an induction
//! derivation: its induction clause quantifies a motive `Q : 't→'r` and
//! instantiating a concrete arithmetic motive leaves the Church handlers
//! un-captured (`peano/SKELETONS.md`). Here the proof is a **concrete Metamath
//! object**: at the `pa.ind` step the motive `P(x)` is a *specific* wff on the
//! replay stack, so `denote_closed` turns it into a *specific* HOL predicate
//! `λn. ⟦P(n)⟧` and we hand it straight to [`Thm::nat_induct`] — **no HOAS
//! motive, no β-capture, no deduction theorem.** The wall was an artifact of the
//! encoding, not of the mathematics.

use std::collections::HashMap;

use covalence_core::{Error, Result, Term, Thm, Type};

use super::fol::Fol;
use super::{deep, mm_pa};
use crate::init::eq::beta_nf;
use crate::init::nat;
use crate::metamath::expr::{body_of, expr_symbols, typecode_of};
use crate::metamath::{Assertion, Database, Expr, Proof, Statement};

// ============================================================================
// Errors
// ============================================================================

fn replay_err(msg: impl Into<String>) -> Error {
    Error::ConnectiveRule(format!("mm-replay: {}", msg.into()))
}

// ============================================================================
// Expression → `Fol` parser (the interpretation's syntactic half)
// ============================================================================

/// A binder context for named→de-Bruijn conversion: the setvar names bound by
/// the enclosing `A.`/`E.`, innermost last.
type Scope<'a> = Vec<&'a str>;

/// Parse a Metamath `term`-typed expression back into a PA [`Fol`] term.
/// `free` assigns each *free* setvar a stable `Fol::FVar` index.
pub fn expr_to_term(e: &Expr, free: &mut FreeVars) -> Result<Fol> {
    let syms = expr_symbols(e).ok_or_else(|| replay_err("term expr is not a symbol list"))?;
    if syms.first() != Some(&"term") {
        return Err(replay_err(format!(
            "expected a `term` expression, got `{}`",
            crate::metamath::expr::render(e)
        )));
    }
    let (t, rest) = parse_term(&syms[1..], &Vec::new(), free)?;
    if !rest.is_empty() {
        return Err(replay_err("trailing symbols after term"));
    }
    Ok(t)
}

/// Parse a Metamath `wff`-typed expression back into a PA [`Fol`] formula.
pub fn expr_to_form(e: &Expr, free: &mut FreeVars) -> Result<Fol> {
    let syms = expr_symbols(e).ok_or_else(|| replay_err("wff expr is not a symbol list"))?;
    if syms.first() != Some(&"wff") {
        return Err(replay_err(format!(
            "expected a `wff` expression, got `{}`",
            crate::metamath::expr::render(e)
        )));
    }
    let (f, rest) = parse_form(&syms[1..], &Vec::new(), free)?;
    if !rest.is_empty() {
        return Err(replay_err("trailing symbols after wff"));
    }
    Ok(f)
}

/// Parse the body of a `|-` statement (drop the typecode) into a [`Fol`]
/// formula.
pub fn prov_to_form(e: &Expr, free: &mut FreeVars) -> Result<Fol> {
    if typecode_of(e) != Some("|-") {
        return Err(replay_err("expected a `|-` statement"));
    }
    let body = body_of(e).ok_or_else(|| replay_err("malformed |- statement"))?;
    let syms: Vec<&str> = body.iter().map(|s| s.as_str()).collect();
    let (f, rest) = parse_form(&syms, &Vec::new(), free)?;
    if !rest.is_empty() {
        return Err(replay_err("trailing symbols after |- formula"));
    }
    Ok(f)
}

/// A stable assignment of free setvar names to `Fol::FVar` indices, so the same
/// PA variable always denotes to the same HOL free variable `pa.v{k}`.
#[derive(Debug, Default, Clone)]
pub struct FreeVars {
    map: HashMap<String, u64>,
    next: u64,
}

impl FreeVars {
    pub fn new() -> Self {
        Self::default()
    }
    fn index(&mut self, name: &str) -> u64 {
        if let Some(k) = self.map.get(name) {
            return *k;
        }
        let k = self.next;
        self.next += 1;
        self.map.insert(name.to_string(), k);
        k
    }
}

/// Resolve a setvar name to a [`Fol`] variable: a bound name becomes the de
/// Bruijn `BVar` for its scope depth; a free name becomes a stable `FVar`.
fn resolve_var(name: &str, scope: &Scope, free: &mut FreeVars) -> Fol {
    // Innermost binder is last in `scope`; its de Bruijn index is 0.
    for (depth_from_inner, bound) in scope.iter().rev().enumerate() {
        if *bound == name {
            return Fol::BVar(depth_from_inner as u64);
        }
    }
    Fol::FVar(free.index(name))
}

/// Parse one PA term off the front of `syms`, returning it and the remaining
/// symbols. Grammar: `0` | `( S t )` | `( t + r )` | `( t x. r )` | setvar.
fn parse_term<'a>(
    syms: &'a [&'a str],
    scope: &Scope<'a>,
    free: &mut FreeVars,
) -> Result<(Fol, &'a [&'a str])> {
    let (head, rest) = syms
        .split_first()
        .ok_or_else(|| replay_err("unexpected end of term"))?;
    match *head {
        "0" => Ok((Fol::Zero, rest)),
        "(" => {
            // Two shapes opening with `(`: `( S t )` or `( a op b )`.
            let (peek, after) = rest
                .split_first()
                .ok_or_else(|| replay_err("empty parenthesised term"))?;
            if *peek == "S" {
                let (t, rest2) = parse_term(after, scope, free)?;
                let rest3 = expect(rest2, ")")?;
                Ok((Fol::Succ(Box::new(t)), rest3))
            } else {
                let (a, rest2) = parse_term(rest, scope, free)?;
                let (op, rest3) = rest2
                    .split_first()
                    .ok_or_else(|| replay_err("missing binary term operator"))?;
                let (b, rest4) = parse_term(rest3, scope, free)?;
                let rest5 = expect(rest4, ")")?;
                let node = match *op {
                    "+" => Fol::Add(Box::new(a), Box::new(b)),
                    "x." => Fol::Mul(Box::new(a), Box::new(b)),
                    other => return Err(replay_err(format!("unknown term operator `{other}`"))),
                };
                Ok((node, rest5))
            }
        }
        sym if mm_pa::SETVARS.contains(&sym) => Ok((resolve_var(sym, scope, free), rest)),
        other => Err(replay_err(format!("unexpected term token `{other}`"))),
    }
}

/// Parse one PA formula off the front of `syms`. Grammar:
/// `( a = b )` | `( ph -> ps )` | `( ph /\ ps )` | `( ph \/ ps )` |
/// `-. ph` | `A. x ph` | `E. x ph`.
fn parse_form<'a>(
    syms: &'a [&'a str],
    scope: &Scope<'a>,
    free: &mut FreeVars,
) -> Result<(Fol, &'a [&'a str])> {
    let (head, rest) = syms
        .split_first()
        .ok_or_else(|| replay_err("unexpected end of formula"))?;
    match *head {
        "-." => {
            let (f, rest2) = parse_form(rest, scope, free)?;
            Ok((Fol::Neg(Box::new(f)), rest2))
        }
        "A." | "E." => {
            let (var, rest2) = rest
                .split_first()
                .ok_or_else(|| replay_err("quantifier missing setvar"))?;
            if !mm_pa::SETVARS.contains(var) {
                return Err(replay_err(format!("`{var}` is not a setvar")));
            }
            let mut inner = scope.clone();
            inner.push(var);
            let (body, rest3) = parse_form(rest2, &inner, free)?;
            let node = if *head == "A." {
                Fol::All(Box::new(body))
            } else {
                Fol::Ex(Box::new(body))
            };
            Ok((node, rest3))
        }
        "(" => {
            // `( <A> op <B> )` where op ∈ { = (terms), ->, /\, \/ }.
            // `=` takes two *terms*; the connectives take two *formulas*.
            // Disambiguate by trying the equality (term/term) shape first via a
            // lookahead on the operator after the first operand.
            //
            // We parse the first operand ambiguously: peek whether the head is a
            // term-former. Simplest robust approach: try parsing as a term-eq; if
            // the operator slot is `=`, it is an equality; else re-parse as a
            // formula connective.
            parse_paren_form(rest, scope, free)
        }
        other => Err(replay_err(format!("unexpected formula token `{other}`"))),
    }
}

/// Parse the inside of a `( … )` formula (the open paren already consumed):
/// either `( t = r )` (atomic) or `( ph op ps )` (connective).
fn parse_paren_form<'a>(
    rest: &'a [&'a str],
    scope: &Scope<'a>,
    free: &mut FreeVars,
) -> Result<(Fol, &'a [&'a str])> {
    // The first operand is a term iff the formula is an equality. We decide by
    // the operator that follows the first operand. Both a term and a formula
    // begin unambiguously (`=` never starts an operand), so we parse the first
    // operand as a *term* on a trial basis only when the leading token can begin
    // a term AND is not a formula-only opener (`-.`, `A.`, `E.`).
    let first = rest
        .first()
        .ok_or_else(|| replay_err("empty parenthesised formula"))?;
    let starts_formula = matches!(*first, "-." | "A." | "E.");
    if !starts_formula {
        // Try equality first: parse a term, check the operator is `=`.
        if let Ok((a, after_a)) = parse_term(rest, scope, free)
            && after_a.first() == Some(&"=")
        {
            let (b, after_b) = parse_term(&after_a[1..], scope, free)?;
            let rest2 = expect(after_b, ")")?;
            return Ok((Fol::Eq(Box::new(a), Box::new(b)), rest2));
        }
    }
    // Otherwise it is a binary connective `( ph op ps )`.
    let (a, after_a) = parse_form(rest, scope, free)?;
    let (op, after_op) = after_a
        .split_first()
        .ok_or_else(|| replay_err("missing binary connective"))?;
    let (b, after_b) = parse_form(after_op, scope, free)?;
    let rest2 = expect(after_b, ")")?;
    let node = match *op {
        "->" => Fol::Imp(Box::new(a), Box::new(b)),
        "/\\" => Fol::And(Box::new(a), Box::new(b)),
        "\\/" => Fol::Or(Box::new(a), Box::new(b)),
        other => return Err(replay_err(format!("unknown connective `{other}`"))),
    };
    Ok((node, rest2))
}

fn expect<'a>(syms: &'a [&'a str], tok: &str) -> Result<&'a [&'a str]> {
    let (head, rest) = syms
        .split_first()
        .ok_or_else(|| replay_err(format!("expected `{tok}`, found end")))?;
    if *head != tok {
        return Err(replay_err(format!("expected `{tok}`, found `{head}`")));
    }
    Ok(rest)
}

// ============================================================================
// The replay stack
// ============================================================================

/// One slot on the replay stack, mirroring a pushed Metamath expression.
#[derive(Clone)]
enum Slot {
    /// A `term`/`wff` expression: only its parsed `Fol` matters (formulas need
    /// it to denote; terms are subterms of formulas).
    Syntax { expr: Expr, fol: Fol },
    /// A `|-` statement: the formula plus the genuine kernel theorem `⊢ ⟦form⟧`.
    Proved { form: Fol, thm: Thm },
}

impl Slot {
    fn expr(&self) -> Option<&Expr> {
        match self {
            Slot::Syntax { expr, .. } => Some(expr),
            Slot::Proved { .. } => None,
        }
    }
}

// ============================================================================
// The replay
// ============================================================================

/// **Replay a verified Metamath PA proof, re-deriving `⊢ ⟦S⟧` in the kernel.**
///
/// `assertion` must be a `$p` theorem of the PA database whose proof
/// [`crate::metamath::verify`] *accepts* (the caller is responsible for having
/// verified it; the replay re-derives the HOL theorem independently). Returns a
/// genuine, hypothesis-free kernel theorem of the conclusion's denotation.
pub fn replay_assertion(db: &Database, assertion: &Assertion) -> Result<Thm> {
    let labels = match assertion.proof.as_ref() {
        Some(Proof::Normal(labels)) => labels,
        Some(Proof::Compressed { .. }) => {
            return Err(replay_err(
                "compressed-proof replay is not supported (decompress to a normal proof first)",
            ));
        }
        None => return Err(replay_err("assertion has no proof to replay")),
    };

    let mut free = FreeVars::new();
    let mut stack: Vec<Slot> = Vec::new();

    for label in labels {
        let stmt = db
            .statement_by_label(label)
            .ok_or_else(|| replay_err(format!("unknown proof label `{label}`")))?;
        match stmt {
            Statement::Float(f) => {
                // Pushes `typecode var`; a setvar/wff-var placeholder. We carry
                // its parsed Fol so later rule applications can read it.
                let expr = crate::metamath::expr::make_expr(&f.typecode, [f.var.as_str()]);
                let fol = parse_syntax(&expr, &mut free)?;
                stack.push(Slot::Syntax { expr, fol });
            }
            Statement::Essential(_) => {
                return Err(replay_err(
                    "replaying a proof with open essential hypotheses is unsupported \
                     (replays must be of closed `$p` theorems)",
                ));
            }
            Statement::Assert(target) => {
                apply(db, target, label, &mut stack, &mut free)?;
            }
            _ => return Err(replay_err(format!("label `{label}` is not provable"))),
        }
    }

    match stack.as_slice() {
        [Slot::Proved { thm, .. }] => {
            // Sanity: the re-derived theorem must denote the claimed conclusion.
            let claimed = prov_to_form(&assertion.conclusion, &mut FreeVars::new())?;
            let want = beta_nf_term(deep::denote_closed(&claimed));
            let got = beta_nf_term(thm.concl().clone());
            if want != got {
                return Err(replay_err(format!(
                    "replayed theorem `{}` does not denote the claimed conclusion `{}`",
                    thm.concl(),
                    crate::metamath::expr::render(&assertion.conclusion),
                )));
            }
            Ok(thm.clone())
        }
        [_] => Err(replay_err("proof ended on a non-`|-` slot")),
        other => Err(replay_err(format!(
            "proof did not reduce to a single result (stack depth {})",
            other.len()
        ))),
    }
}

/// Parse a `term`/`wff` slot expression into a `Fol`.
fn parse_syntax(expr: &Expr, free: &mut FreeVars) -> Result<Fol> {
    match typecode_of(expr) {
        Some("term") => expr_to_term(expr, free),
        Some("wff") => expr_to_form(expr, free),
        other => Err(replay_err(format!(
            "expected a term/wff slot, got typecode {other:?}"
        ))),
    }
}

/// Apply a target assertion `label` during replay: pop its mandatory operands,
/// dispatch on the label, push the result slot.
fn apply(
    db: &Database,
    target: &Assertion,
    label: &str,
    stack: &mut Vec<Slot>,
    free: &mut FreeVars,
) -> Result<()> {
    let n = target.frame.mandatory_count();
    if stack.len() < n {
        return Err(replay_err(format!(
            "stack underflow applying `{label}` (need {n}, have {})",
            stack.len()
        )));
    }
    let args: Vec<Slot> = stack.split_off(stack.len() - n);

    // Term/wff formation: the result is just the substituted expression parsed
    // back to Fol. We recompute it from the *verifier's* substitution by
    // re-running the engine's apply on the expression stack — but for the
    // closed PA database it is simpler to dispatch structurally below and, for
    // pure formation labels, rebuild the expression from the operands.
    let result = match label {
        // --- term/wff formation: rebuild the syntactic result ---
        _ if is_syntax_former(target) => syntax_former(db, target, label, &args, free)?,
        // --- the PA rules and axioms (produce a `|-` theorem) ---
        "ax.mp" => rule_mp(&args)?,
        "ax.gen" => rule_gen(&args)?,
        "pa.ind" => rule_induct(&args)?,
        _ if label.starts_with("pa.") => axiom_instance(target, label, &args, free)?,
        other => return Err(replay_err(format!("no replay rule for `{other}`"))),
    };
    stack.push(result);
    Ok(())
}

/// Whether the target is a `term`/`wff` formation axiom (its conclusion's
/// typecode is `term` or `wff`).
fn is_syntax_former(target: &Assertion) -> bool {
    matches!(typecode_of(&target.conclusion), Some("term") | Some("wff"))
}

/// Rebuild a formation step's result expression by substituting the popped
/// operand expressions into the target's schema, then parse it to `Fol`.
fn syntax_former(
    _db: &Database,
    target: &Assertion,
    label: &str,
    args: &[Slot],
    free: &mut FreeVars,
) -> Result<Slot> {
    let expr = substitute_floats(target, label, args)?;
    let fol = parse_syntax(&expr, free)?;
    Ok(Slot::Syntax { expr, fol })
}

/// A PA axiom instance `pa.i` (i = 1..6). The mandatory `$f` operands are the
/// bound setvars the axiom abstracts; substituting them yields the instance's
/// `|-` formula, whose denotation we re-derive from the proven `init::nat`
/// theorem. Since the `nat` theorems are `∀`-closed, the bound-variable rename
/// is irrelevant to the denotation (alpha-invariance), so the bridge matches.
fn axiom_instance(
    target: &Assertion,
    label: &str,
    args: &[Slot],
    free: &mut FreeVars,
) -> Result<Slot> {
    // Substitute the float operands into the axiom conclusion (a setvar rename).
    let instance = substitute_floats(target, label, args)?;
    let form = prov_to_form(&instance, free)?;
    let thm = axiom_nat_thm(label)?;
    // Bridge the proven `init::nat` theorem to the denotation shape (they agree
    // up to β; both are the standard `nat`/`bool` form).
    let bridged = bridge_to_denotation(thm, &form)?;
    Ok(Slot::Proved { form, thm: bridged })
}

/// Compute the substituted conclusion of `target` from its mandatory `$f`
/// operands (in `args`, float-first frame order). Shared by axiom instances and
/// syntax formers.
fn substitute_floats(target: &Assertion, label: &str, args: &[Slot]) -> Result<Expr> {
    use crate::metamath::subst::{Subst, apply_subst};
    let frame = &target.frame;
    let mut subst = Subst::new();
    for (i, f) in frame.floats.iter().enumerate() {
        let arg_expr = args
            .get(i)
            .and_then(Slot::expr)
            .ok_or_else(|| replay_err(format!("`{label}`: operand {i} is not a syntax slot")))?;
        let body = body_of(arg_expr).unwrap_or(&[]).to_vec();
        subst.insert(f.var.clone(), body);
    }
    Ok(apply_subst(&target.conclusion, &subst))
}

/// The proven `init::nat` theorem that is PA axiom `label`'s denotation.
fn axiom_nat_thm(label: &str) -> Result<Thm> {
    Ok(match label {
        "pa.1" => nat::zero_ne_succ(),
        "pa.2" => nat::succ_inj(),
        "pa.3" => nat::add_base(),
        "pa.4" => nat::add_step(),
        "pa.5" => nat::mul_base(),
        "pa.6" => nat::mul_step(),
        other => return Err(replay_err(format!("`{other}` is not a PA axiom"))),
    })
}

/// **Modus ponens.** Operands (frame order: floats `ph`,`ps` then essentials
/// `min : |- ph`, `maj : |- ( ph -> ps )`) — re-derive `⊢ ⟦ps⟧` by
/// [`Thm::imp_elim`].
fn rule_mp(args: &[Slot]) -> Result<Slot> {
    // The two `|-` operands are the *essential* hypotheses, after the floats.
    let (min, maj) = two_proved(args, "ax.mp")?;
    let (form, thm) = mp_via_replay(min.form, min.thm, maj.form, maj.thm)?;
    Ok(Slot::Proved { form, thm })
}

/// **The modus-ponens mechanism (the replay's `ax.mp` core), reusable.** Given
/// `minor : ⊢ ⟦A⟧` and `major : ⊢ ⟦A ⟹ B⟧` (with `major_form = Fol::Imp(A, B)`),
/// re-derive `⊢ ⟦B⟧` by [`Thm::imp_elim`]. Since `⟦A ⟹ B⟧ = ⟦A⟧ ⟹ ⟦B⟧`
/// definitionally, the implication eliminates against the minor directly.
pub fn mp_via_replay(
    _minor_form: &Fol,
    minor: &Thm,
    major_form: &Fol,
    major: &Thm,
) -> Result<(Fol, Thm)> {
    let Fol::Imp(_, b) = major_form else {
        return Err(replay_err("ax.mp: major premise is not an implication"));
    };
    let thm = major.clone().imp_elim(minor.clone())?;
    Ok(((**b).clone(), thm))
}

/// **Generalisation.** Operands: floats `x`,`ph` then essential `h : |- ph`.
/// Re-derive `⊢ ⟦A. x ph⟧` by [`Thm::all_intro`] over the HOL free variable
/// the setvar `x` denotes to.
fn rule_gen(args: &[Slot]) -> Result<Slot> {
    // Float operands: `x` (a setvar syntax slot) and `ph` (a wff slot).
    // Essential operand: the proved premise `|- ph`.
    let proved = one_proved(args, "ax.gen")?;
    let xvar = setvar_slot(args, "ax.gen")?;
    // The setvar `x` denotes to the HOL free variable `pa.v{k}`. If `x` is free
    // in the premise, `all_intro` binds it; if not, the binder is vacuous — both
    // are sound `∀`-introduction and both match the denotation `⟦A. x ph⟧`
    // (which always introduces a fresh HOL binder).
    let Fol::FVar(k) = xvar else {
        return Err(replay_err(
            "ax.gen: the generalised operand is not a setvar",
        ));
    };
    let name = deep::fvar_hol_name(k);
    let thm = proved.thm.clone().all_intro(&name, Type::nat())?;
    // The denoted result `∀. ⟦ph⟧[x↦bvar]` — build via the Fol close so the
    // shape matches `denote_closed` (a no-op close if `x` is not free).
    let form = Fol::All(Box::new(proved.form.close(k)));
    // Bridge naming/β residue.
    let bridged = bridge_to_denotation(thm, &form)?;
    Ok(Slot::Proved { form, thm: bridged })
}

/// **Induction.** The `pa.ind` schema: floats `x`,`ph`,`ph0`,`phS`, essentials
/// `base : |- ph0` and `step : |- A. x ( ph -> phS )`. The motive `P(x)` is the
/// concrete wff `ph` on the stack; re-derive `⊢ ⟦A. x ph⟧` by
/// [`Thm::nat_induct`] on the *concrete* denoted motive — **this is where the
/// impredicative engine's motive wall is sidestepped**.
fn rule_induct(args: &[Slot]) -> Result<Slot> {
    // Identify operands by their roles. Frame order: floats (x, ph, ph0, phS)
    // then essentials (base, step). We read the *concrete* motive `ph` and the
    // bound setvar `x` from the syntax slots, and the two `|-` theorems.
    let (base, step) = two_proved(args, "pa.ind")?;

    // The bound setvar `x` is the first `term`-typed syntax slot.
    let xfvar = setvar_slot(args, "pa.ind")?;
    let k = match xfvar {
        Fol::FVar(k) => k,
        _ => {
            return Err(replay_err(
                "pa.ind: the induction variable must be a free setvar",
            ));
        }
    };

    // The motive body `ph = P(x)` is the `wff` syntax slot that is the body of
    // the conclusion `A. x ph` — i.e. the formula closed under `x`. We read it
    // off the first wff slot (the `ph` float operand).
    let motive_body = first_wff_slot(args, "pa.ind")?;

    let (form, thm) = induct_via_replay(&motive_body, k, base.thm.clone(), step.thm.clone())?;
    Ok(Slot::Proved { form, thm })
}

/// **The induction mechanism (the replay's `pa.ind` core), reusable.**
///
/// Given the *concrete* motive `motive` — an open [`Fol`] formula `P(x)` in
/// which the induction setvar appears as `Fol::FVar(k)` — and two **genuine
/// kernel theorems**:
///
/// - `base : ⊢ ⟦P(0)⟧`, and
/// - `step : ⊢ ⟦∀x. P(x) ⟹ P(S x)⟧` (a HOL `∀` over `pa.v{k}`),
///
/// re-derive `⊢ ⟦∀x. P(x)⟧` by **[`Thm::nat_induct`] on the concrete denoted
/// motive** `p = λn. ⟦P(n)⟧`, returning the result formula and theorem.
///
/// This is exactly the point where the impredicative engine's motive β-capture
/// wall is sidestepped: `p` is a *specific* HOL predicate (the motive is concrete
/// by replay time), handed directly to the kernel rule — no quantified `Q`, no
/// Church-handler capture, no deduction theorem.
pub fn induct_via_replay(motive: &Fol, k: u64, base: Thm, step: Thm) -> Result<(Fol, Thm)> {
    // Denote the motive as a HOL predicate `p = λn. ⟦P(n)⟧`.
    let p = motive_predicate(motive, k)?;

    // base : `⊢ ⟦P(0)⟧` → reshape to the applied form `⊢ p 0`.
    let base_ref = ProvedRef {
        form: motive,
        thm: &base,
    };
    let base_thm = reshape_to_applied(&p, &nat::zero(), &base_ref)?;

    // step : `⊢ ∀n. ⟦P(n)⟧ ⟹ ⟦P(S n)⟧` → `⊢ p n ⟹ p (S n)` for `n = pa.v{k}`.
    let step_ref = ProvedRef {
        form: motive,
        thm: &step,
    };
    let step_thm = induction_step(&p, k, &step_ref)?;

    let induct = Thm::nat_induct(base_thm, step_thm)?; // ⊢ ∀n. p n
    let induct = crate::init::eq::beta_nf_concl(induct)?; // ⊢ ∀n. ⟦P(n)⟧

    // Result formula: `A. x P` (close the setvar into the binder).
    let form = Fol::All(Box::new(motive.close(k)));
    let bridged = bridge_to_denotation(induct, &form)?;
    Ok((form, bridged))
}

// ============================================================================
// Replay helpers
// ============================================================================

/// Collect the proved (`|-`) operands in order.
fn proved_slots<'a>(args: &'a [Slot]) -> Vec<&'a Slot> {
    args.iter()
        .filter(|s| matches!(s, Slot::Proved { .. }))
        .collect()
}

/// Exactly one proved operand.
fn one_proved<'a>(args: &'a [Slot], rule: &str) -> Result<ProvedRef<'a>> {
    let ps = proved_slots(args);
    match ps.as_slice() {
        [Slot::Proved { form, thm }] => Ok(ProvedRef { form, thm }),
        _ => Err(replay_err(format!(
            "`{rule}` expects exactly one `|-` operand, got {}",
            ps.len()
        ))),
    }
}

/// Exactly two proved operands, in order.
fn two_proved<'a>(args: &'a [Slot], rule: &str) -> Result<(ProvedRef<'a>, ProvedRef<'a>)> {
    let ps = proved_slots(args);
    match ps.as_slice() {
        [
            Slot::Proved { form: f0, thm: t0 },
            Slot::Proved { form: f1, thm: t1 },
        ] => Ok((
            ProvedRef { form: f0, thm: t0 },
            ProvedRef { form: f1, thm: t1 },
        )),
        _ => Err(replay_err(format!(
            "`{rule}` expects exactly two `|-` operands, got {}",
            ps.len()
        ))),
    }
}

/// A borrow into a `Slot::Proved`.
struct ProvedRef<'a> {
    form: &'a Fol,
    thm: &'a Thm,
}

/// The first `term`-typed setvar operand's `Fol` (used to read the bound var).
fn setvar_slot(args: &[Slot], rule: &str) -> Result<Fol> {
    for s in args {
        if let Slot::Syntax { expr, fol } = s
            && typecode_of(expr) == Some("term")
            && matches!(fol, Fol::FVar(_))
        {
            return Ok(fol.clone());
        }
    }
    Err(replay_err(format!("`{rule}`: no setvar operand found")))
}

/// The first `wff`-typed operand's `Fol` (the motive `ph`).
fn first_wff_slot(args: &[Slot], rule: &str) -> Result<Fol> {
    for s in args {
        if let Slot::Syntax { expr, fol } = s
            && typecode_of(expr) == Some("wff")
        {
            return Ok(fol.clone());
        }
    }
    Err(replay_err(format!("`{rule}`: no wff operand found")))
}

/// Build the HOL motive predicate `p = λn:nat. ⟦P(n)⟧` from the *open* motive
/// formula `P` (which mentions setvar `k` as `Fol::FVar(k)`), by denoting the
/// formula with the free HOL variable `pa.v{k}` then abstracting it.
fn motive_predicate(motive: &Fol, k: u64) -> Result<Term> {
    let body = deep::denote_closed(motive); // ⟦P(pa.v_k)⟧
    let var_name = deep::fvar_hol_name(k);
    let closed = covalence_core::subst::close(&body, &var_name);
    Ok(Term::abs(Type::nat(), closed)) // λn. ⟦P(n)⟧
}

/// Reshape a proved `⊢ ⟦P(arg-denotation)⟧` into the applied form `⊢ p arg`,
/// by β-expanding `p arg` and rewriting through β-normal forms.
fn reshape_to_applied(p: &Term, arg: &Term, proved: &ProvedRef) -> Result<Thm> {
    // Target applied term `p arg`; its β-nf must match the proved conclusion's
    // β-nf. Bridge by normalising both.
    let applied = Term::app(p.clone(), arg.clone());
    bridge_concl(proved.thm.clone(), &applied)
}

/// From the step premise `⊢ ∀n. ⟦P(n)⟧ ⟹ ⟦P(S n)⟧`, build
/// `⊢ p n ⟹ p (S n)` for the free `n = pa.v{k}`, in `nat_induct` shape.
fn induction_step(p: &Term, k: u64, step: &ProvedRef) -> Result<Thm> {
    let n = deep::fvar_hol(k); // pa.v_k : nat
    // Specialise the ∀ to `n` (the same free var the motive uses).
    let specialised = step.thm.clone().all_elim(n.clone())?; // ⊢ ⟦P(n)⟧ ⟹ ⟦P(S n)⟧
    // Reshape both sides to `p`-applications. The applied target:
    let p_n = Term::app(p.clone(), n.clone());
    let s_n = nat::succ(n.clone());
    let p_sn = Term::app(p.clone(), s_n);
    let applied_imp = {
        use crate::init::ext::TermExt;
        p_n.imp(p_sn)?
    };
    bridge_concl(specialised, &applied_imp)
}

// ============================================================================
// β-normalisation bridges (the proof is genuine; these only re-shape syntax)
// ============================================================================

/// `beta_nf` of a term (the right-hand side of `beta_nf`'s equation).
fn beta_nf_term(t: Term) -> Term {
    beta_nf(t)
        .concl()
        .as_eq()
        .expect("beta_nf yields an equation")
        .1
        .clone()
}

/// Bridge `Γ ⊢ p` to `Γ ⊢ target` when `p` and `target` β-normalise to the same
/// term. Genuine: a kernel `eq_mp` through the β-equation, never an assumption.
fn bridge_concl(thm: Thm, target: &Term) -> Result<Thm> {
    if thm.concl() == target {
        return Ok(thm);
    }
    let from_nf = beta_nf(thm.concl().clone()); // ⊢ p = nf(p)
    let to_nf = beta_nf(target.clone()); // ⊢ target = nf(target)
    let eq = from_nf.trans(to_nf.sym()?)?; // ⊢ p = target  (iff nf(p) = nf(target))
    eq.eq_mp(thm)
}

/// Bridge a proven `init::nat`/derived theorem to the denotation `⟦form⟧` of a
/// `Fol` formula (they agree up to β).
fn bridge_to_denotation(thm: Thm, form: &Fol) -> Result<Thm> {
    let denotation = deep::denote_closed(form);
    bridge_concl(thm, &denotation)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::metamath::expr::make_expr;
    use crate::metamath::verify_assertion;
    use crate::peano::pa;

    fn assert_genuine(thm: &Thm) {
        assert!(
            thm.hyps().is_empty(),
            "replayed theorem must be hypothesis-free"
        );
        assert!(thm.has_no_obs(), "replayed theorem must be oracle-free");
    }

    /// The expression→Fol parser round-trips a PA formula: a `|-` statement
    /// parses back to the same `Fol` the database axiom denotes.
    #[test]
    fn parse_pa3_formula() {
        let db = mm_pa::database().unwrap();
        let Some(Statement::Assert(a)) = db.statement_by_label("pa.3") else {
            panic!()
        };
        let mut free = FreeVars::new();
        let parsed = prov_to_form(&a.conclusion, &mut free).unwrap();
        assert_eq!(parsed, pa::ax_add_base());
    }

    /// Parse each PA axiom and check it matches the `peano::pa` reference AST.
    #[test]
    fn parse_all_pa_axioms() {
        let db = mm_pa::database().unwrap();
        let refs = [
            ("pa.1", pa::ax_zero_ne_succ()),
            ("pa.2", pa::ax_succ_inj()),
            ("pa.3", pa::ax_add_base()),
            ("pa.4", pa::ax_add_step()),
            ("pa.5", pa::ax_mul_base()),
            ("pa.6", pa::ax_mul_step()),
        ];
        for (label, want) in refs {
            let Some(Statement::Assert(a)) = db.statement_by_label(label) else {
                panic!("{label}")
            };
            let mut free = FreeVars::new();
            let got = prov_to_form(&a.conclusion, &mut free).unwrap();
            assert_eq!(got, want, "{label} parse mismatch");
        }
    }

    /// **Non-induction end-to-end:** a `$p` theorem whose proof is the single
    /// axiom label `pa.3` is verified by the engine and replayed to a genuine
    /// kernel theorem `⊢ ⟦∀x. 0+x = x⟧` — which equals `init::nat::add_base`.
    #[test]
    fn replay_pa3_axiom() {
        let mut db = mm_pa::database().unwrap();
        let concl = make_expr(
            "|-",
            ["A.", "x", "(", "(", "0", "+", "x", ")", "=", "x", ")"],
        );
        // PA3's frame floats over the bound setvar `x`, so the proof first
        // pushes `term x` via the float `f.x`, then applies `pa.3`.
        db.add_assertion(
            "th.pa3".into(),
            concl,
            Some(Proof::Normal(vec!["f.x".into(), "pa.3".into()])),
        )
        .unwrap();
        let db = db.finish().unwrap();
        let Some(Statement::Assert(a)) = db.statement_by_label("th.pa3") else {
            panic!()
        };
        // The engine accepts the proof (untrusted input).
        verify_assertion(&db, a).unwrap();
        // The replay re-derives the HOL theorem independently.
        let thm = replay_assertion(&db, a).unwrap();
        assert_genuine(&thm);
        assert_eq!(thm.concl(), nat::add_base().concl());
    }

    /// All six PA axioms replay to their `init::nat` denotations.
    #[test]
    fn replay_all_pa_axioms() {
        // Each axiom's mandatory floats are its bound setvars (declaration
        // order), supplied as the leading proof labels.
        let want: [(&str, &[&str], Thm); 6] = [
            ("pa.1", &["f.x"], nat::zero_ne_succ()),
            ("pa.2", &["f.x", "f.y"], nat::succ_inj()),
            ("pa.3", &["f.x"], nat::add_base()),
            ("pa.4", &["f.x", "f.y"], nat::add_step()),
            ("pa.5", &["f.x"], nat::mul_base()),
            ("pa.6", &["f.x", "f.y"], nat::mul_step()),
        ];
        for (label, floats, refthm) in want {
            let mut db = mm_pa::database().unwrap();
            let Some(Statement::Assert(ax)) = db.statement_by_label(label) else {
                panic!()
            };
            let concl = ax.conclusion.clone();
            let pname = format!("th.{label}");
            let mut proof: Vec<String> = floats.iter().map(|s| s.to_string()).collect();
            proof.push(label.to_string());
            db.add_assertion(pname.clone(), concl, Some(Proof::Normal(proof)))
                .unwrap();
            let db = db.finish().unwrap();
            let Some(Statement::Assert(a)) = db.statement_by_label(&pname) else {
                panic!()
            };
            verify_assertion(&db, a).unwrap();
            let thm = replay_assertion(&db, a).unwrap();
            assert_genuine(&thm);
            assert_eq!(thm.concl(), refthm.concl(), "{label}");
        }
    }

    // ========================================================================
    // The induction mechanism (the headline) — `pa.ind` replay → `nat_induct`.
    //
    // These exercise [`induct_via_replay`], the exact core the `pa.ind` step of
    // a Metamath proof drives. The motive is a *concrete* `Fol` (so there is no
    // HOAS `Q`, no Church-handler β-capture — the impredicative engine's wall);
    // base and step are **genuine kernel theorems** (no postulates); the result
    // is a hypothesis-free `nat_induct` theorem.
    //
    // Authoring the base/step as *Metamath proof scripts* needs the proper
    // substitution apparatus `[ t / x ]` (base `[0/x]ph`, step `[Sx/x]ph`),
    // which is SKELETONed in `peano/SKELETONS.md` (the long Hilbert script). The
    // induction *mechanism* below is complete and genuine.
    // ========================================================================

    use crate::init::ext::{TermExt, ThmExt};
    use crate::init::nat::{add, succ, zero};
    use covalence_core::defs;

    /// `P(x) := (x + 0 = x)` as an open `Fol` whose setvar is `FVar(k)`.
    fn add_zero_motive(k: u64) -> Fol {
        Fol::Eq(
            Box::new(Fol::Add(Box::new(Fol::FVar(k)), Box::new(Fol::Zero))),
            Box::new(Fol::FVar(k)),
        )
    }

    /// **The headline, via the replay path.** Induction-on-`x` of
    /// `P(x) := x + 0 = x` discharges through `induct_via_replay` to a genuine
    /// hypothesis-free kernel theorem `⊢ ∀x. x + 0 = x` that **equals**
    /// `init::nat::add_zero` — landing exactly what the impredicative engine
    /// could not (`peano/SKELETONS.md`), through the `ValidProof` replay.
    #[test]
    fn induction_headline_add_zero() {
        let k = 0u64;
        let motive = add_zero_motive(k);
        let n = deep::fvar_hol(k); // pa.v0 : nat

        // base : ⊢ ⟦P(0)⟧ = `0 + 0 = 0`. Built genuinely from add_base.
        let base = nat::add_base().all_elim(zero()).unwrap(); // ⊢ 0 + 0 = 0

        // step : ⊢ ∀x. (x+0=x) ⟹ (Sx+0=Sx)  over the free `pa.v0`.
        //   (this is the induction step `init::nat::add_zero` itself proves —
        //    here re-built so its free variable is `pa.v0`, the motive's var.)
        let ih_concl = add(n.clone(), zero()).equals(n.clone()).unwrap(); // n+0=n
        let ih = Thm::assume(ih_concl.clone()).unwrap(); // {n+0=n} ⊢ n+0=n
        let s = nat::add_step()
            .all_elim(n.clone())
            .unwrap()
            .all_elim(zero())
            .unwrap(); // ⊢ S n + 0 = S(n + 0)
        let cong = ih.cong_arg(defs::nat_succ()).unwrap(); // {n+0=n} ⊢ S(n+0) = S n
        let step_open = s.trans(cong).unwrap().imp_intro(&ih_concl).unwrap(); // ⊢ (n+0=n) ⟹ (Sn+0=Sn)
        let step = step_open
            .all_intro(&deep::fvar_hol_name(k), Type::nat())
            .unwrap();

        // Run the replay's induction mechanism on the *concrete* motive.
        let (form, thm) = induct_via_replay(&motive, k, base, step).unwrap();

        // It is a genuine, hypothesis-free kernel theorem...
        assert_genuine(&thm);
        // ...whose formula is `∀x. x + 0 = x`...
        assert_eq!(form, Fol::All(Box::new(motive.close(k))));
        // ...and which is exactly `init::nat::add_zero` — the headline.
        assert_eq!(thm.concl(), nat::add_zero().concl());
        // Cross-check: it also equals the denotation of the result formula.
        assert_eq!(thm.concl(), &deep::denote_closed(&form));
    }

    /// **The `ax.mp` mechanism:** from genuine kernel theorems `⊢ ⟦A⟧` and
    /// `⊢ ⟦A ⟹ B⟧`, [`mp_via_replay`] re-derives `⊢ ⟦B⟧` by `imp_elim`. Here
    /// `A := (0+0 = 0)` (PA3-at-0) and `A ⟹ B` is `A ⟹ A` (so `B = A`), both
    /// built genuinely; the result is hypothesis-free.
    #[test]
    fn mp_mechanism() {
        // A := ⟦(0 + 0) = 0⟧, proved from add_base.
        let a_fol = Fol::Eq(
            Box::new(Fol::Add(Box::new(Fol::Zero), Box::new(Fol::Zero))),
            Box::new(Fol::Zero),
        );
        let minor = nat::add_base().all_elim(zero()).unwrap(); // ⊢ 0 + 0 = 0
        // A ⟹ A, via imp_intro of the assumption.
        let assumed = Thm::assume(minor.concl().clone()).unwrap();
        let imp = assumed.imp_intro(minor.concl()).unwrap(); // ⊢ (0+0=0) ⟹ (0+0=0)
        let imp_fol = Fol::Imp(Box::new(a_fol.clone()), Box::new(a_fol.clone()));

        let (b_form, thm) = mp_via_replay(&a_fol, &minor, &imp_fol, &imp).unwrap();
        assert_genuine(&thm);
        assert_eq!(b_form, a_fol);
        assert_eq!(thm.concl(), minor.concl());
    }

    /// **End-to-end `ax.gen`:** a real Metamath proof generalises PA1 over a
    /// fresh setvar `y`, proving `|- A. y A. x -.( 0 = ( S x ) )`. The engine
    /// verifies it; the replay re-derives `⊢ ∀y. ∀x. ¬(0 = S x)` by
    /// [`Thm::all_intro`] (a vacuous binder over `y`, sound) — a genuine,
    /// hypothesis-free kernel theorem.
    #[test]
    fn replay_gen_over_pa1() {
        let mut db = mm_pa::database().unwrap();
        // Build the `wff A. x -. ( 0 = ( S x ) )` on the stack, the premise
        // `|- A. x -. ( 0 = ( S x ) )` via `pa.1`, then `ax.gen` over `y`.
        // `w.all` floats are [x (term), ph (wff)], popped deeper→top, so the
        // `term x` operand must sit *below* the wff on the stack.
        let mk_pa1_wff = [
            "f.x", // term x      (the `w.all` setvar operand, pushed first)
            "t.0", // term 0
            "f.x", "t.S",   // term ( S x )
            "w.eq",  // wff ( 0 = ( S x ) )
            "w.neg", // wff -. ( 0 = ( S x ) )
            "w.all", // wff A. x -. ( 0 = ( S x ) )
        ];
        // `ax.gen` floats are [x' (gen var, term), ph (wff)] then essential
        // `gen.h : |- ph`. Stack (deeper→top): term y, wff <PA1 body>, |- <PA1>.
        let mut proof: Vec<&str> = Vec::new();
        proof.push("f.y"); // term y  (the generalisation variable)
        proof.extend(mk_pa1_wff); // wff A. x -. ( 0 = ( S x ) )  (the ph operand)
        proof.extend(["f.x", "pa.1"]); // |- A. x -. ( 0 = ( S x ) )  (the premise)
        proof.push("ax.gen");
        let proof: Vec<String> = proof.iter().map(|s| s.to_string()).collect();
        let concl = crate::metamath::expr::make_expr(
            "|-",
            [
                "A.", "y", "A.", "x", "-.", "(", "0", "=", "(", "S", "x", ")", ")",
            ],
        );
        db.add_assertion("th.gen".into(), concl, Some(Proof::Normal(proof)))
            .unwrap();
        let db = db.finish().unwrap();
        let Some(Statement::Assert(a)) = db.statement_by_label("th.gen") else {
            panic!()
        };
        verify_assertion(&db, a).unwrap();
        let thm = replay_assertion(&db, a).unwrap();
        assert_genuine(&thm);
        // ⟦A. y A. x ¬(0 = S x)⟧ = ∀y. ∀x. ¬(0 = S x).
        let want = Fol::All(Box::new(pa::ax_zero_ne_succ()));
        assert_eq!(thm.concl(), &deep::denote_closed(&want));
    }

    /// The induction mechanism also lands on a *degenerate* motive whose step
    /// doesn't use the induction hypothesis, confirming `nat_induct` fires on an
    /// arbitrary concrete motive (here `P(x) := (0 + x) = x`, i.e. PA3 re-proved
    /// by induction). Genuine, hypothesis-free.
    #[test]
    fn induction_reproves_pa3() {
        let k = 1u64;
        // P(x) := (0 + x) = x
        let motive = Fol::Eq(
            Box::new(Fol::Add(Box::new(Fol::Zero), Box::new(Fol::FVar(k)))),
            Box::new(Fol::FVar(k)),
        );
        let n = deep::fvar_hol(k);

        // base : ⊢ 0 + 0 = 0.
        let base = nat::add_base().all_elim(zero()).unwrap();
        // step : ⊢ ∀x. ((0+x)=x) ⟹ ((0+Sx)=Sx).  The consequent is PA3-at-(Sx),
        //   independent of the hypothesis — weaken it in.
        let conseq = nat::add_base().all_elim(succ(n.clone())).unwrap(); // ⊢ 0 + Sx = Sx
        let hyp = add(zero(), n.clone()).equals(n.clone()).unwrap(); // (0+x)=x
        let step_open = conseq.imp_intro(&hyp).unwrap(); // ⊢ ((0+x)=x) ⟹ ((0+Sx)=Sx)
        let step = step_open
            .all_intro(&deep::fvar_hol_name(k), Type::nat())
            .unwrap();

        let (_form, thm) = induct_via_replay(&motive, k, base, step).unwrap();
        assert_genuine(&thm);
        // ∀x. (0+x)=x  is `add_base` (up to the bound-var name = de Bruijn).
        assert_eq!(thm.concl(), nat::add_base().concl());
    }
}
