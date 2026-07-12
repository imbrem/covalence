//! The **separate proof-file format** (`hol-typed` feature) — an S-expression
//! interchange for proofs, keyed **by name**, replayed through the abstract
//! [`Hol`] / [`Nat`] traits so the checker is **backend-decoupled**.
//!
//! # The split
//!
//! A dialect *theorem* declares only a **name + statement** (an equation
//! expression; see [`crate::ast::Theorem`]). Its **proof lives in a separate
//! file**, in the S-expression format below, matched to the theorem **by name**.
//! The statement is therefore the stable interface — an interface/implementation
//! split — and a proof may come from a third-party producer that never touches
//! Haskell syntax, exactly as the [`crate::sexpr`] IR intends.
//!
//! # The grammar (reusing [`crate::sexpr`])
//!
//! A proof file is a sequence of `(proof NAME step+)` forms. Each **step** is a
//! rule application; the steps of a proof are numbered `1, 2, …` in order and a
//! step refers to an **earlier** step by the reference atom `#K`. The **last**
//! step's theorem is the proof's result.
//!
//! ```text
//! file  := (proof NAME step+)*
//! step  := (refl      term)          -- ⊢ t = t
//!        | (assume    term)          -- {t} ⊢ t
//!        | (lemma     NAME)          -- cite a Nat accessor / prior theorem
//!        | (sym       #K)            -- ⊢ a = b  ↦  ⊢ b = a
//!        | (trans     #J #K)         -- ⊢ a=b, ⊢ b=c  ↦  ⊢ a=c
//!        | (eq-mp     #J #K)         -- ⊢ a=b, ⊢ a   ↦  ⊢ b
//!        | (beta-conv term)          -- ⊢ (λx.t) u = t[u/x]
//!        | (inst      #K NAME term)  -- instantiate a free var
//!        | (all-elim  #K term)       -- ⊢ ∀x.p  ↦  ⊢ p[t/x]
//!        | (all-intro #K NAME type)  -- Γ⊢p  ↦  Γ⊢ ∀x.p
//!        | (imp-intro #K term)       -- Γ⊢q  ↦  Γ\{h}⊢ h⟹q
//!        | (imp-elim  #J #K)         -- ⊢ p⟹q, ⊢ p  ↦  ⊢ q
//! ```
//!
//! where a **term** and a **type** are the compact S-expression sub-grammars
//! read by [`read_term`] / [`read_type`]:
//!
//! ```text
//! type  := nat | bool | (tvar NAME) | (-> type type)
//! term  := (nat N) | (var NAME type) | (app f x)
//!        | (+ a b) | (* a b) | (== a b)   -- Nat::add / Nat::mul / Hol::eq
//! ```
//!
//! Every step and every term/type is built **only** through the `Hol` / `Nat`
//! trait methods — the replayer names no backend type except through the bound
//! `H: Hol + Nat`. Swapping the trusted kernel swaps the trait impl; this
//! replayer, the format, and any proof written in it are untouched. The checker
//! trusts **only** the `Hol` trait: a produced [`Hol::Thm`] is sound by
//! construction (each step is a real inference rule), and the linker's sole
//! remaining check is that the conclusion α-equals the lowered statement.

use std::collections::BTreeMap;

use covalence_hol_api::{Hol, Nat};

use crate::ast::Ty;
use crate::sexpr::SExpr;
use crate::typed::{self, Env, TypedError};

/// An error from parsing or replaying a proof.
#[derive(Clone, Debug)]
pub enum ProofError {
    /// The S-expression is not a well-formed proof/step/term/type.
    Malformed(String),
    /// A step referenced `#K` for a `K` that is out of range (or not yet
    /// defined at that point).
    BadRef(usize),
    /// A `(lemma NAME)` cited a name the linker's lemma table does not know.
    UnknownLemma(String),
    /// A type in a step could not be resolved / an expression could not lower.
    Typed(TypedError),
    /// A `Hol` / `Nat` trait method rejected the step (an unsound step attempt,
    /// an ill-typed application, …).
    Hol(covalence_hol_api::Error),
}

impl From<TypedError> for ProofError {
    fn from(e: TypedError) -> Self {
        ProofError::Typed(e)
    }
}
impl From<covalence_hol_api::Error> for ProofError {
    fn from(e: covalence_hol_api::Error) -> Self {
        ProofError::Hol(e)
    }
}

impl core::fmt::Display for ProofError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            ProofError::Malformed(m) => write!(f, "malformed proof: {m}"),
            ProofError::BadRef(k) => write!(f, "step reference #{k} out of range"),
            ProofError::UnknownLemma(n) => write!(f, "unknown lemma `{n}`"),
            ProofError::Typed(e) => write!(f, "{e}"),
            ProofError::Hol(e) => write!(f, "HOL error: {e}"),
        }
    }
}

impl std::error::Error for ProofError {}

/// The result type of proof parsing / replay.
pub type Result<T> = std::result::Result<T, ProofError>;

/// A parsed proof: a name and its ordered list of steps (still as [`SExpr`], to
/// keep parsing and replay separate — parse once, replay against any backend).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Proof {
    /// The theorem name this proof discharges (the link key).
    pub name: String,
    /// The proof steps, in order; the last one's theorem is the result.
    pub steps: Vec<SExpr>,
}

/// Parse all `(proof NAME step+)` forms in a proof-file's S-expression text.
///
/// Returns the proofs in file order; [`ProofSet`] indexes them by name for the
/// linker.
pub fn parse_proofs(src: &str) -> Result<Vec<Proof>> {
    let forms = crate::sexpr::parse_sexprs(src)
        .map_err(|e| ProofError::Malformed(format!("s-expression parse: {e}")))?;
    forms.iter().map(parse_proof_form).collect()
}

fn parse_proof_form(form: &SExpr) -> Result<Proof> {
    let items = as_list(form)?;
    match items {
        [head, name, rest @ ..] if is_sym(head, "proof") => {
            let name = sym_name(name)?;
            if rest.is_empty() {
                return Err(ProofError::Malformed(format!(
                    "proof `{name}` has no steps"
                )));
            }
            Ok(Proof {
                name,
                steps: rest.to_vec(),
            })
        }
        _ => Err(ProofError::Malformed(
            "expected a (proof NAME step+) form".into(),
        )),
    }
}

/// A name-indexed set of proofs — the proof-file half of the interface /
/// implementation split. [`ProofSet::get`] resolves a theorem name to its
/// proof (or `None` = an unproven **hole**).
#[derive(Clone, Debug, Default)]
pub struct ProofSet {
    by_name: BTreeMap<String, Proof>,
}

impl ProofSet {
    /// Build a proof set from the proofs parsed out of a file. A duplicate name
    /// is a [`ProofError::Malformed`].
    pub fn new(proofs: Vec<Proof>) -> Result<ProofSet> {
        let mut by_name = BTreeMap::new();
        for p in proofs {
            if by_name.contains_key(&p.name) {
                return Err(ProofError::Malformed(format!(
                    "duplicate proof for `{}`",
                    p.name
                )));
            }
            by_name.insert(p.name.clone(), p);
        }
        Ok(ProofSet { by_name })
    }

    /// Parse a proof file's text into a [`ProofSet`].
    pub fn parse(src: &str) -> Result<ProofSet> {
        ProofSet::new(parse_proofs(src)?)
    }

    /// The proof for `name`, or `None` (an unproven hole).
    pub fn get(&self, name: &str) -> Option<&Proof> {
        self.by_name.get(name)
    }
}

/// A **lemma table**: named theorems a `(lemma NAME)` step may cite — `Nat`
/// accessors and any prior dialect theorems already checked. Generic over the
/// backend's `Thm`, so it names no concrete kernel type.
pub struct Lemmas<H: Hol> {
    table: BTreeMap<String, H::Thm>,
}

impl<H: Hol> Default for Lemmas<H> {
    fn default() -> Self {
        Lemmas {
            table: BTreeMap::new(),
        }
    }
}

impl<H: Hol + Nat> Lemmas<H> {
    /// An empty lemma table.
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a named lemma (e.g. a just-checked dialect theorem).
    pub fn insert(&mut self, name: impl Into<String>, thm: H::Thm) {
        self.table.insert(name.into(), thm);
    }

    /// Look up a cited lemma.
    pub fn get(&self, name: &str) -> Option<&H::Thm> {
        self.table.get(name)
    }

    /// Pre-load the standard `Nat` Peano accessors (`add_base`, `add_step`,
    /// `add_comm`, …) so a proof may cite them by name. Each is a fallible
    /// derivation; a failure surfaces as a `Hol` error.
    pub fn with_nat_accessors(hol: &H) -> Result<Self> {
        let mut l = Self::new();
        // The workhorse Peano lemmas, by the name a proof cites.
        l.insert("succ_inj", hol.succ_inj()?);
        l.insert("zero_ne_succ", hol.zero_ne_succ()?);
        l.insert("add_base", hol.add_base()?);
        l.insert("add_step", hol.add_step()?);
        l.insert("mul_base", hol.mul_base()?);
        l.insert("mul_step", hol.mul_step()?);
        l.insert("add_zero", hol.add_zero()?);
        l.insert("add_succ_r", hol.add_succ_r()?);
        l.insert("add_comm", hol.add_comm()?);
        l.insert("add_assoc", hol.add_assoc()?);
        l.insert("add_cancel", hol.add_cancel()?);
        l.insert("mul_zero", hol.mul_zero()?);
        l.insert("mul_succ_r", hol.mul_succ_r()?);
        l.insert("mul_comm", hol.mul_comm()?);
        Ok(l)
    }
}

/// **Replay a proof** through the trait surface, producing its result theorem.
///
/// Steps are evaluated in order; each may reference an **earlier** step by `#K`
/// (1-based) and cite a lemma from `lemmas` via `(lemma NAME)`. The last step's
/// theorem is returned. This function names **no** backend type except through
/// `H: Hol + Nat` — the decoupling property.
pub fn replay<H: Hol + Nat>(hol: &H, lemmas: &Lemmas<H>, proof: &Proof) -> Result<H::Thm> {
    let mut done: Vec<H::Thm> = Vec::with_capacity(proof.steps.len());
    for step in &proof.steps {
        let thm = replay_step(hol, lemmas, &done, step)?;
        done.push(thm);
    }
    done.pop()
        .ok_or_else(|| ProofError::Malformed("empty proof".into()))
}

/// Resolve an earlier step reference `#K` (1-based) against the steps already
/// replayed.
fn resolve_ref<H: Hol>(done: &[H::Thm], r: &SExpr) -> Result<H::Thm> {
    let k = as_step_ref(r)?;
    if k == 0 || k > done.len() {
        return Err(ProofError::BadRef(k));
    }
    Ok(done[k - 1].clone())
}

fn replay_step<H: Hol + Nat>(
    hol: &H,
    lemmas: &Lemmas<H>,
    done: &[H::Thm],
    step: &SExpr,
) -> Result<H::Thm> {
    let items = as_list(step)?;
    let head = items
        .first()
        .ok_or_else(|| ProofError::Malformed("empty step".into()))?;
    let head = sym_name(head)?;
    let args = &items[1..];
    match (head.as_str(), args) {
        ("refl", [t]) => {
            let t = read_term(hol, t)?;
            Ok(hol.refl(t)?)
        }
        ("assume", [t]) => {
            let t = read_term(hol, t)?;
            Ok(hol.assume(t)?)
        }
        ("lemma", [n]) => {
            let name = sym_name(n)?;
            lemmas
                .get(&name)
                .cloned()
                .ok_or(ProofError::UnknownLemma(name))
        }
        ("sym", [r]) => Ok(hol.sym(resolve_ref::<H>(done, r)?)?),
        ("trans", [a, b]) => Ok(hol.trans(resolve_ref::<H>(done, a)?, resolve_ref::<H>(done, b)?)?),
        ("eq-mp", [eq, p]) => {
            Ok(hol.eq_mp(resolve_ref::<H>(done, eq)?, resolve_ref::<H>(done, p)?)?)
        }
        ("beta-conv", [t]) => {
            let t = read_term(hol, t)?;
            Ok(hol.beta_conv(t)?)
        }
        ("inst", [r, name, t]) => {
            let th = resolve_ref::<H>(done, r)?;
            let name = sym_name(name)?;
            let t = read_term(hol, t)?;
            Ok(hol.inst(th, &name, t)?)
        }
        ("all-elim", [r, t]) => {
            let th = resolve_ref::<H>(done, r)?;
            let t = read_term(hol, t)?;
            Ok(hol.all_elim(th, t)?)
        }
        ("all-intro", [r, name, ty]) => {
            let th = resolve_ref::<H>(done, r)?;
            let name = sym_name(name)?;
            let ty = read_type(hol, ty)?;
            Ok(hol.all_intro(th, &name, ty)?)
        }
        ("imp-intro", [r, h]) => {
            let th = resolve_ref::<H>(done, r)?;
            let h = read_term(hol, h)?;
            Ok(hol.imp_intro(th, &h)?)
        }
        ("imp-elim", [imp, ante]) => {
            Ok(hol.imp_elim(resolve_ref::<H>(done, imp)?, resolve_ref::<H>(done, ante)?)?)
        }
        (other, _) => Err(ProofError::Malformed(format!(
            "unknown or ill-formed step `{other}`"
        ))),
    }
}

// ---------------------------------------------------------------------------
// Term / type readers — the compact proof sub-grammars, built through the
// traits only (via `typed::resolve_ty` for types).
// ---------------------------------------------------------------------------

/// Read a **type** S-expression through the traits: `nat`, `bool`,
/// `(tvar NAME)`, `(-> a b)`. Delegates the actual construction to
/// [`typed::resolve_ty`] so the type surface stays in one place.
pub fn read_type<H: Hol + Nat>(hol: &H, e: &SExpr) -> Result<H::Type> {
    let ty = read_type_ast(e)?;
    Ok(typed::resolve_ty(hol, &ty)?)
}

/// Read a proof-format type S-expression into a dialect [`Ty`].
fn read_type_ast(e: &SExpr) -> Result<Ty> {
    match e {
        SExpr::Sym(s) if s == "nat" => Ok(Ty::base("nat")),
        SExpr::Sym(s) if s == "bool" => Ok(Ty::base("bool")),
        SExpr::List(items) => match items.as_slice() {
            [head, SExpr::Sym(name)] if is_sym(head, "tvar") => Ok(Ty::var(name.clone())),
            [head, a, b] if is_sym(head, "->") => Ok(Ty::fun(read_type_ast(a)?, read_type_ast(b)?)),
            _ => Err(ProofError::Malformed(format!("bad type: {e}"))),
        },
        _ => Err(ProofError::Malformed(format!("bad type: {e}"))),
    }
}

/// Read a **term** S-expression through the traits: `(nat N)`, `(var NAME ty)`,
/// `(app f x)`, `(+ a b)`, `(* a b)`, `(== a b)`. Built entirely through the
/// `Hol` / `Nat` methods.
pub fn read_term<H: Hol + Nat>(hol: &H, e: &SExpr) -> Result<H::Term> {
    let items = as_list(e)?;
    let head = items
        .first()
        .ok_or_else(|| ProofError::Malformed("empty term".into()))?;
    let head = sym_name(head)?;
    let args = &items[1..];
    match (head.as_str(), args) {
        ("nat", [SExpr::Nat(n)]) => {
            let small = u64::try_from(n)
                .map_err(|_| ProofError::Malformed("nat literal exceeds u64".into()))?;
            Ok(Nat::lit(hol, small))
        }
        ("var", [name, ty]) => {
            let name = sym_name(name)?;
            let ty = read_type(hol, ty)?;
            Ok(hol.var(&name, ty))
        }
        ("app", [f, x]) => {
            let f = read_term(hol, f)?;
            let x = read_term(hol, x)?;
            Ok(hol.app(f, x)?)
        }
        ("+", [a, b]) => {
            let (a, b) = (read_term(hol, a)?, read_term(hol, b)?);
            Ok(Nat::add(hol, a, b)?)
        }
        ("*", [a, b]) => {
            let (a, b) = (read_term(hol, a)?, read_term(hol, b)?);
            Ok(Nat::mul(hol, a, b)?)
        }
        ("==", [a, b]) => {
            let (a, b) = (read_term(hol, a)?, read_term(hol, b)?);
            Ok(hol.eq(a, b)?)
        }
        (other, _) => Err(ProofError::Malformed(format!("bad term head `{other}`"))),
    }
}

// ---------------------------------------------------------------------------
// The linker: match theorem statements to proofs by name, replay, and check.
// ---------------------------------------------------------------------------

/// The outcome of linking one theorem statement against the proof set.
#[derive(Clone, Debug)]
pub enum LinkOutcome<H: Hol> {
    /// A proof was found, replayed, and its conclusion α-equals the lowered
    /// statement. Carries the checked theorem.
    Proved(H::Thm),
    /// The declaration is an `axiom` — postulated, no proof expected.
    Axiom,
    /// No proof was found for this name — an unproven **hole** (reported, not
    /// fatal).
    Hole,
    /// A proof was found but replay failed or its conclusion did **not** match
    /// the statement — the proof is **rejected**.
    Mismatch(String),
}

/// Link one theorem: look up its proof by name, replay it, and check the
/// produced conclusion α-equals `statement` (the lowered `Term : bool`).
///
/// - no proof → [`LinkOutcome::Hole`];
/// - an axiom declaration → [`LinkOutcome::Axiom`] (no proof consulted);
/// - replay error or conclusion mismatch → [`LinkOutcome::Mismatch`];
/// - success → [`LinkOutcome::Proved`] with the checked theorem.
///
/// α-equality is the backend `Term`'s own equality (`PartialEq`); the native
/// kernel's terms are locally-nameless, so structural equality **is** α-equality.
pub fn link_theorem<H: Hol + Nat>(
    hol: &H,
    lemmas: &Lemmas<H>,
    proofs: &ProofSet,
    name: &str,
    statement: &H::Term,
    is_axiom: bool,
) -> LinkOutcome<H> {
    if is_axiom {
        return LinkOutcome::Axiom;
    }
    let Some(proof) = proofs.get(name) else {
        return LinkOutcome::Hole;
    };
    let thm = match replay(hol, lemmas, proof) {
        Ok(t) => t,
        Err(e) => return LinkOutcome::Mismatch(format!("replay failed: {e}")),
    };
    let concl = hol.concl(&thm);
    if &concl == statement {
        LinkOutcome::Proved(thm)
    } else {
        LinkOutcome::Mismatch(format!(
            "conclusion does not match statement\n  got:  {concl:?}\n  want: {statement:?}"
        ))
    }
}

// ---------------------------------------------------------------------------
// Small S-expression helpers.
// ---------------------------------------------------------------------------

/// A theorem statement's implicitly-∀-quantified variables: the free variables
/// of the statement expression that are **not** ambient theory operations.
///
/// A convenience for the linker: given the statement AST and the set of ambient
/// operation names (bound in the typing env but meant to stay free constants),
/// the rest of the free variables are the ones [`typed::lower_statement`] should
/// ∀-close.
pub fn statement_quantifiers(
    stmt: &crate::ast::Expr,
    ambient_ops: &std::collections::BTreeSet<String>,
) -> std::collections::BTreeSet<String> {
    typed::free_vars(stmt)
        .into_iter()
        .filter(|v| !ambient_ops.contains(v))
        .collect()
}

/// Lower a theorem statement to a proposition, ∀-closing every free variable
/// that is not an ambient operation. A thin convenience wrapper over
/// [`typed::lower_statement`] + [`statement_quantifiers`].
pub fn lower_theorem_statement<H: Hol + Nat>(
    hol: &H,
    env: &Env<H>,
    stmt: &crate::ast::Expr,
    ambient_ops: &std::collections::BTreeSet<String>,
) -> std::result::Result<H::Term, TypedError> {
    let quant = statement_quantifiers(stmt, ambient_ops);
    typed::lower_statement(hol, env, stmt, &quant)
}

fn as_list(e: &SExpr) -> Result<&[SExpr]> {
    match e {
        SExpr::List(items) => Ok(items),
        _ => Err(ProofError::Malformed(format!("expected a list, got {e}"))),
    }
}

fn is_sym(e: &SExpr, s: &str) -> bool {
    matches!(e, SExpr::Sym(x) if x == s)
}

fn sym_name(e: &SExpr) -> Result<String> {
    match e {
        SExpr::Sym(s) => Ok(s.clone()),
        _ => Err(ProofError::Malformed(format!("expected a symbol, got {e}"))),
    }
}

/// Read a step reference `#K` (a symbol like `#3`) into its 1-based index.
fn as_step_ref(e: &SExpr) -> Result<usize> {
    match e {
        SExpr::Sym(s) if s.starts_with('#') => s[1..]
            .parse::<usize>()
            .map_err(|_| ProofError::Malformed(format!("bad step reference `{s}`"))),
        _ => Err(ProofError::Malformed(format!(
            "expected a step reference #K, got {e}"
        ))),
    }
}
