//! **Reified first-order logic, locally-nameless, inside HOL** — the
//! reusable Phase-A framework the Peano-arithmetic development
//! (`notes/vibes/peano-arithmetic-plan.md`) is built on.
//!
//! This scales the proved propositional recipe in [`crate::init::prop`]
//! from *propositional* to *first-order* logic: the new ingredients are a
//! **term layer** (over a signature `0`, `S`, `+`, `·`) and **quantifiers**
//! (`∀`, `∃`), which means **binders**. We reify the syntax
//! **locally-nameless** — bound variables are de Bruijn indices (HOL-level
//! `nat`), free variables are `nat`-indexed atoms — exactly mirroring the
//! kernel's own [`covalence_core::subst`] representation. The single biggest
//! payoff: substitution becomes *shifting* and capture-avoidance disappears.
//!
//! ## The Church / impredicative encoding (same lane as `prop.rs`)
//!
//! As in [`crate::init::prop`], a formula is encoded at a **fresh result
//! type variable `'r`** as a polymorphic fold over a tuple of handlers, one
//! per constructor. We deliberately *do not* use the inductive engine
//! ([`crate::init::inductive`]): soundness is an induction over
//! *derivations*, discharged case-by-case by the kernel's connective rules,
//! and an impredicative encoding turns that induction into a single `inst`
//! of a higher-order predicate variable — no recursor, no freeness proofs,
//! no new TCB. The whole development rides on existing kernel primitives.
//!
//! **Two carriers, one result type.** A first-order *term* and a *formula*
//! both fold into `'r`, so we use a single combined handler tuple. Encoded
//! terms have type `Θ⟨'r⟩`; encoded formulas have type `Φ⟨'r⟩`. They share
//! the same fold algebra (the handler tuple `H⟨'r⟩`); the difference is only
//! *which* handler a constructor invokes. Concretely an encoded object is a
//! function `H⟨'r⟩ → 'r` and the constructors are the obvious folds.
//!
//! ## The signature (PA's, but the framework is generic in spirit)
//!
//! Handlers, in fold order:
//!
//! | slot   | type                  | meaning                          |
//! |--------|-----------------------|----------------------------------|
//! | `bvar` | `nat → 'r`            | bound variable (de Bruijn index) |
//! | `fvar` | `nat → 'r`            | free variable (atom index)       |
//! | `zero` | `'r`                  | the constant `0`                 |
//! | `succ` | `'r → 'r`             | successor `S`                    |
//! | `add`  | `'r → 'r → 'r`        | `+`                              |
//! | `mul`  | `'r → 'r → 'r`        | `·`                              |
//! | `eq`   | `'r → 'r → 'r`        | atomic `t = s`                   |
//! | `neg`  | `'r → 'r`             | `¬`                              |
//! | `and`  | `'r → 'r → 'r`        | `∧`                              |
//! | `or`   | `'r → 'r → 'r`        | `∨`                              |
//! | `imp`  | `'r → 'r → 'r`        | `⟹`                              |
//! | `all`  | `'r → 'r`             | `∀` (body folds the bound slot)  |
//! | `ex`   | `'r → 'r`             | `∃`                              |
//!
//! For a quantifier `∀x. φ`, the encoded body is a fold *of the formula
//! `φ`* in which the bound variable is `bvar 0` at the current depth; the
//! `all` handler receives that fold. The denotation re-binds it with a real
//! HOL `∀` (see [`denote`] in the PA module). The encoding is genuine
//! reified syntax — `enc(eq (fvar 0) zero)` is a distinct HOL term from its
//! meaning.

use covalence_core::subst::close;
use covalence_core::{Term, Type};
use covalence_types::Nat;

// ============================================================================
// Result type variable + base types
// ============================================================================

/// The fresh result type variable `'r` everything folds into.
pub fn rty() -> Type {
    Type::tfree("r")
}

pub(crate) fn nat() -> Type {
    Type::nat()
}

/// The thirteen handler binder names + slot-type builders, in fold order.
/// Each slot is parametric in the result type `r`.
pub const HANDLERS: [(&str, fn(&Type) -> Type); 13] = [
    ("bvar", idx_h_ty),
    ("fvar", idx_h_ty),
    ("zero", nul_h_ty),
    ("succ", un_h_ty),
    ("add", bin_h_ty),
    ("mul", bin_h_ty),
    ("eq", bin_h_ty),
    ("neg", un_h_ty),
    ("and", bin_h_ty),
    ("or", bin_h_ty),
    ("imp", bin_h_ty),
    ("all", un_h_ty),
    ("ex", un_h_ty),
];

/// `nat → r` — a variable handler slot (`bvar` / `fvar`).
fn idx_h_ty(r: &Type) -> Type {
    Type::fun(nat(), r.clone())
}

/// `r` — a nullary handler slot (`zero`).
fn nul_h_ty(r: &Type) -> Type {
    r.clone()
}

/// `r → r` — a unary handler slot (`succ` / `neg` / `all` / `ex`).
fn un_h_ty(r: &Type) -> Type {
    Type::fun(r.clone(), r.clone())
}

/// `r → r → r` — a binary handler slot.
fn bin_h_ty(r: &Type) -> Type {
    Type::fun(r.clone(), Type::fun(r.clone(), r.clone()))
}

/// `Φ⟨r⟩ = (bvar)→(fvar)→…→(ex)→r` — the type of an encoded term **or**
/// formula at result type `r`. (Terms and formulas share one carrier; the
/// distinction is which handlers a value invokes.)
pub fn phi_at(r: &Type) -> Type {
    let mut t = r.clone();
    // Innermost binder is the last handler (`ex`); wrap from the end.
    for (_, ty) in HANDLERS.iter().rev() {
        t = Type::fun(ty(r), t);
    }
    t
}

/// `Φ⟨'r⟩` — the canonical polymorphic carrier.
pub fn phi() -> Type {
    phi_at(&rty())
}

/// `Φ⟨bool⟩` — the carrier pinned at the denotation instance.
pub fn phi_at_bool() -> Type {
    phi_at(&Type::bool())
}

// ============================================================================
// Handler plumbing
// ============================================================================

/// A free handler variable by name, at result type `r`.
pub fn handler(r: &Type, name: &str) -> Term {
    let ty = HANDLERS
        .iter()
        .find(|(n, _)| *n == name)
        .map(|(_, t)| t(r))
        .expect("fol: unknown handler name");
    Term::free(name, ty)
}

/// `λbvar fvar … ex. body` — wrap a fold `body : r` in the thirteen handler
/// abstractions, yielding a `Φ⟨r⟩` value. Inverse of [`apply_handlers`] up
/// to β.
pub fn close_handlers(r: &Type, body: Term) -> Term {
    let mut t = body;
    for (name, ty) in HANDLERS.iter().rev() {
        t = Term::abs(ty(r), close(&t, name));
    }
    t
}

/// Apply an encoded value `enc : Φ⟨r⟩` to the thirteen handlers, producing
/// its fold `: r`. Inverse of [`close_handlers`] up to β.
pub fn apply_handlers(r: &Type, enc: Term) -> Term {
    let mut t = enc;
    for (name, _) in HANDLERS {
        t = Term::app(t, handler(r, name));
    }
    t
}

// ============================================================================
// Term constructors (the expression layer)
// ============================================================================

/// `enc(bvar i) : Φ⟨r⟩` — a de Bruijn bound variable (index `i : nat`).
pub fn bvar_at(r: &Type, i: Term) -> Term {
    close_handlers(r, Term::app(handler(r, "bvar"), i))
}

/// `enc(fvar k) : Φ⟨r⟩` — a free variable (atom index `k : nat`).
pub fn fvar_at(r: &Type, k: Term) -> Term {
    close_handlers(r, Term::app(handler(r, "fvar"), k))
}

/// `enc(0) : Φ⟨r⟩`.
pub fn zero_at(r: &Type) -> Term {
    close_handlers(r, handler(r, "zero"))
}

/// `enc(S t) : Φ⟨r⟩`.
pub fn succ_at(r: &Type, t: Term) -> Term {
    close_handlers(r, Term::app(handler(r, "succ"), apply_handlers(r, t)))
}

fn term_bin_at(r: &Type, op: &str, a: Term, b: Term) -> Term {
    let body = Term::app(
        Term::app(handler(r, op), apply_handlers(r, a)),
        apply_handlers(r, b),
    );
    close_handlers(r, body)
}

/// `enc(a + b) : Φ⟨r⟩`.
pub fn add_at(r: &Type, a: Term, b: Term) -> Term {
    term_bin_at(r, "add", a, b)
}

/// `enc(a · b) : Φ⟨r⟩`.
pub fn mul_at(r: &Type, a: Term, b: Term) -> Term {
    term_bin_at(r, "mul", a, b)
}

// ============================================================================
// Formula constructors (the FOL layer)
// ============================================================================

/// `enc(a = b) : Φ⟨r⟩` — the sole atomic formula (PA's one relation `=`).
pub fn eq_at(r: &Type, a: Term, b: Term) -> Term {
    term_bin_at(r, "eq", a, b)
}

/// `enc(¬A) : Φ⟨r⟩`.
pub fn neg_at(r: &Type, a: Term) -> Term {
    close_handlers(r, Term::app(handler(r, "neg"), apply_handlers(r, a)))
}

/// `enc(A ∧ B) : Φ⟨r⟩`.
pub fn and_at(r: &Type, a: Term, b: Term) -> Term {
    term_bin_at(r, "and", a, b)
}

/// `enc(A ∨ B) : Φ⟨r⟩`.
pub fn or_at(r: &Type, a: Term, b: Term) -> Term {
    term_bin_at(r, "or", a, b)
}

/// `enc(A ⟹ B) : Φ⟨r⟩`.
pub fn imp_at(r: &Type, a: Term, b: Term) -> Term {
    term_bin_at(r, "imp", a, b)
}

/// `enc(∀. A) : Φ⟨r⟩` — the body `A` is an already-encoded formula in which
/// the freshly-bound variable appears as `bvar 0` (locally-nameless). The
/// `all` handler folds it.
pub fn all_at(r: &Type, body: Term) -> Term {
    close_handlers(r, Term::app(handler(r, "all"), apply_handlers(r, body)))
}

/// `enc(∃. A) : Φ⟨r⟩`.
pub fn ex_at(r: &Type, body: Term) -> Term {
    close_handlers(r, Term::app(handler(r, "ex"), apply_handlers(r, body)))
}

// ============================================================================
// Polymorphic ('r) convenience builders
// ============================================================================

/// `nat` literal `k` as a term.
pub fn nat_lit(k: u64) -> Term {
    Term::nat_lit(Nat::from_inner(k.into()))
}

/// `enc(bvar i) : Φ⟨'r⟩`.
pub fn bvar(i: u64) -> Term {
    bvar_at(&rty(), nat_lit(i))
}
/// `enc(fvar k) : Φ⟨'r⟩`.
pub fn fvar(k: u64) -> Term {
    fvar_at(&rty(), nat_lit(k))
}
/// `enc(0) : Φ⟨'r⟩`.
pub fn zero() -> Term {
    zero_at(&rty())
}
/// `enc(S t) : Φ⟨'r⟩`.
pub fn succ(t: Term) -> Term {
    succ_at(&rty(), t)
}
/// `enc(a + b) : Φ⟨'r⟩`.
pub fn add(a: Term, b: Term) -> Term {
    add_at(&rty(), a, b)
}
/// `enc(a · b) : Φ⟨'r⟩`.
pub fn mul(a: Term, b: Term) -> Term {
    mul_at(&rty(), a, b)
}
/// `enc(a = b) : Φ⟨'r⟩`.
pub fn eq(a: Term, b: Term) -> Term {
    eq_at(&rty(), a, b)
}
/// `enc(¬A) : Φ⟨'r⟩`.
pub fn neg(a: Term) -> Term {
    neg_at(&rty(), a)
}
/// `enc(A ∧ B) : Φ⟨'r⟩`.
pub fn and(a: Term, b: Term) -> Term {
    and_at(&rty(), a, b)
}
/// `enc(A ∨ B) : Φ⟨'r⟩`.
pub fn or(a: Term, b: Term) -> Term {
    or_at(&rty(), a, b)
}
/// `enc(A ⟹ B) : Φ⟨'r⟩`.
pub fn imp(a: Term, b: Term) -> Term {
    imp_at(&rty(), a, b)
}
/// `enc(∀. A) : Φ⟨'r⟩`.
pub fn all(body: Term) -> Term {
    all_at(&rty(), body)
}
/// `enc(∃. A) : Φ⟨'r⟩`.
pub fn ex(body: Term) -> Term {
    ex_at(&rty(), body)
}

// ============================================================================
// A Rust-side AST + locally-nameless substitution (Phase A2)
//
// The encoded HOL terms above are the *object* the metatheory reasons about,
// but to *compute substitutions* structurally we keep a Rust-side mirror AST
// `Fol`, with `encode : Fol → Term` the analogue of the `p_*` builders. This
// is exactly the prop.rs pattern (Rust meta-functions build encoded HOL
// terms), extended with the one thing PA needs: substitution. The operations
// `open`/`close`/`shift`/`subst_fvar` mirror `covalence_core::subst` —
// locally-nameless, so substitution is *shifting*, capture-free.
// ============================================================================

/// A reified first-order term/formula as a Rust-side AST (the source the
/// encoder + substitution operate on). Bound variables are de Bruijn
/// indices; free variables are atom indices — locally-nameless.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Fol {
    /// Bound variable `bvar i` (de Bruijn, innermost binder = 0).
    BVar(u64),
    /// Free variable `fvar k` (atom index).
    FVar(u64),
    /// The constant `0`.
    Zero,
    /// Successor.
    Succ(Box<Fol>),
    /// Addition.
    Add(Box<Fol>, Box<Fol>),
    /// Multiplication.
    Mul(Box<Fol>, Box<Fol>),
    /// Atomic `a = b`.
    Eq(Box<Fol>, Box<Fol>),
    /// `¬A`.
    Neg(Box<Fol>),
    /// `A ∧ B`.
    And(Box<Fol>, Box<Fol>),
    /// `A ∨ B`.
    Or(Box<Fol>, Box<Fol>),
    /// `A ⟹ B`.
    Imp(Box<Fol>, Box<Fol>),
    /// `∀. A` — the body binds `BVar 0`.
    All(Box<Fol>),
    /// `∃. A`.
    Ex(Box<Fol>),
}

impl Fol {
    /// `encode(f) : Φ⟨r⟩` — the HOL encoding of this AST at result type `r`.
    pub fn encode_at(&self, r: &Type) -> Term {
        match self {
            Fol::BVar(i) => bvar_at(r, nat_lit(*i)),
            Fol::FVar(k) => fvar_at(r, nat_lit(*k)),
            Fol::Zero => zero_at(r),
            Fol::Succ(t) => succ_at(r, t.encode_at(r)),
            Fol::Add(a, b) => add_at(r, a.encode_at(r), b.encode_at(r)),
            Fol::Mul(a, b) => mul_at(r, a.encode_at(r), b.encode_at(r)),
            Fol::Eq(a, b) => eq_at(r, a.encode_at(r), b.encode_at(r)),
            Fol::Neg(a) => neg_at(r, a.encode_at(r)),
            Fol::And(a, b) => and_at(r, a.encode_at(r), b.encode_at(r)),
            Fol::Or(a, b) => or_at(r, a.encode_at(r), b.encode_at(r)),
            Fol::Imp(a, b) => imp_at(r, a.encode_at(r), b.encode_at(r)),
            Fol::All(a) => all_at(r, a.encode_at(r)),
            Fol::Ex(a) => ex_at(r, a.encode_at(r)),
        }
    }

    /// `encode(f) : Φ⟨'r⟩` at the polymorphic carrier.
    pub fn encode(&self) -> Term {
        self.encode_at(&rty())
    }

    /// **Shift** every `BVar i` with `i ≥ cutoff` by `delta`. Mirrors
    /// [`covalence_core::subst::shift_by`]: crossing a binder raises the
    /// cutoff. Used so a replacement term's bound vars keep pointing at the
    /// right outer binders when substituted under quantifiers.
    pub fn shift(&self, delta: i64, cutoff: u64) -> Fol {
        match self {
            Fol::BVar(i) => {
                if *i >= cutoff {
                    let new = (*i as i64) + delta;
                    assert!(new >= 0, "Fol::shift: BVar underflow");
                    Fol::BVar(new as u64)
                } else {
                    Fol::BVar(*i)
                }
            }
            Fol::FVar(k) => Fol::FVar(*k),
            Fol::Zero => Fol::Zero,
            Fol::Succ(t) => Fol::Succ(Box::new(t.shift(delta, cutoff))),
            Fol::Add(a, b) => Fol::Add(b1(a.shift(delta, cutoff)), b1(b.shift(delta, cutoff))),
            Fol::Mul(a, b) => Fol::Mul(b1(a.shift(delta, cutoff)), b1(b.shift(delta, cutoff))),
            Fol::Eq(a, b) => Fol::Eq(b1(a.shift(delta, cutoff)), b1(b.shift(delta, cutoff))),
            Fol::Neg(a) => Fol::Neg(b1(a.shift(delta, cutoff))),
            Fol::And(a, b) => Fol::And(b1(a.shift(delta, cutoff)), b1(b.shift(delta, cutoff))),
            Fol::Or(a, b) => Fol::Or(b1(a.shift(delta, cutoff)), b1(b.shift(delta, cutoff))),
            Fol::Imp(a, b) => Fol::Imp(b1(a.shift(delta, cutoff)), b1(b.shift(delta, cutoff))),
            // Crossing a binder raises the cutoff.
            Fol::All(a) => Fol::All(b1(a.shift(delta, cutoff + 1))),
            Fol::Ex(a) => Fol::Ex(b1(a.shift(delta, cutoff + 1))),
        }
    }

    /// **Open** the outermost binder of a body with the term `u`: replace
    /// `BVar 0` by `u` and decrement the deeper bound indices. Mirrors
    /// [`covalence_core::subst::open`]. `self` is the *body* of an `All`/`Ex`.
    pub fn open(&self, u: &Fol) -> Fol {
        self.inst(u, 0)
    }

    fn inst(&self, u: &Fol, depth: u64) -> Fol {
        match self {
            Fol::BVar(i) => match (*i).cmp(&depth) {
                std::cmp::Ordering::Less => Fol::BVar(*i),
                std::cmp::Ordering::Equal => u.shift(depth as i64, 0),
                std::cmp::Ordering::Greater => Fol::BVar(*i - 1),
            },
            Fol::FVar(k) => Fol::FVar(*k),
            Fol::Zero => Fol::Zero,
            Fol::Succ(t) => Fol::Succ(b1(t.inst(u, depth))),
            Fol::Add(a, b) => Fol::Add(b1(a.inst(u, depth)), b1(b.inst(u, depth))),
            Fol::Mul(a, b) => Fol::Mul(b1(a.inst(u, depth)), b1(b.inst(u, depth))),
            Fol::Eq(a, b) => Fol::Eq(b1(a.inst(u, depth)), b1(b.inst(u, depth))),
            Fol::Neg(a) => Fol::Neg(b1(a.inst(u, depth))),
            Fol::And(a, b) => Fol::And(b1(a.inst(u, depth)), b1(b.inst(u, depth))),
            Fol::Or(a, b) => Fol::Or(b1(a.inst(u, depth)), b1(b.inst(u, depth))),
            Fol::Imp(a, b) => Fol::Imp(b1(a.inst(u, depth)), b1(b.inst(u, depth))),
            Fol::All(a) => Fol::All(b1(a.inst(u, depth + 1))),
            Fol::Ex(a) => Fol::Ex(b1(a.inst(u, depth + 1))),
        }
    }

    /// **Close** a free variable `fvar k` into `BVar 0`, raising the index
    /// under deeper binders. Mirrors [`covalence_core::subst::close`]. The
    /// inverse of [`open`](Fol::open) at a fresh atom: builds the body of a
    /// quantifier from a formula mentioning the free atom `k`.
    pub fn close(&self, k: u64) -> Fol {
        self.close_at(k, 0)
    }

    fn close_at(&self, k: u64, depth: u64) -> Fol {
        match self {
            Fol::FVar(j) if *j == k => Fol::BVar(depth),
            Fol::FVar(j) => Fol::FVar(*j),
            Fol::BVar(i) => Fol::BVar(*i),
            Fol::Zero => Fol::Zero,
            Fol::Succ(t) => Fol::Succ(b1(t.close_at(k, depth))),
            Fol::Add(a, b) => Fol::Add(b1(a.close_at(k, depth)), b1(b.close_at(k, depth))),
            Fol::Mul(a, b) => Fol::Mul(b1(a.close_at(k, depth)), b1(b.close_at(k, depth))),
            Fol::Eq(a, b) => Fol::Eq(b1(a.close_at(k, depth)), b1(b.close_at(k, depth))),
            Fol::Neg(a) => Fol::Neg(b1(a.close_at(k, depth))),
            Fol::And(a, b) => Fol::And(b1(a.close_at(k, depth)), b1(b.close_at(k, depth))),
            Fol::Or(a, b) => Fol::Or(b1(a.close_at(k, depth)), b1(b.close_at(k, depth))),
            Fol::Imp(a, b) => Fol::Imp(b1(a.close_at(k, depth)), b1(b.close_at(k, depth))),
            Fol::All(a) => Fol::All(b1(a.close_at(k, depth + 1))),
            Fol::Ex(a) => Fol::Ex(b1(a.close_at(k, depth + 1))),
        }
    }

    /// **Substitute** the free variable `fvar k` by term `u` throughout
    /// (no binder is consumed; `u`'s bound indices are shifted to stay valid
    /// under the binders crossed). Mirrors
    /// [`covalence_core::subst::subst_free`].
    pub fn subst_fvar(&self, k: u64, u: &Fol) -> Fol {
        self.subst_at(k, u, 0)
    }

    fn subst_at(&self, k: u64, u: &Fol, depth: u64) -> Fol {
        match self {
            Fol::FVar(j) if *j == k => u.shift(depth as i64, 0),
            Fol::FVar(j) => Fol::FVar(*j),
            Fol::BVar(i) => Fol::BVar(*i),
            Fol::Zero => Fol::Zero,
            Fol::Succ(t) => Fol::Succ(b1(t.subst_at(k, u, depth))),
            Fol::Add(a, b) => Fol::Add(b1(a.subst_at(k, u, depth)), b1(b.subst_at(k, u, depth))),
            Fol::Mul(a, b) => Fol::Mul(b1(a.subst_at(k, u, depth)), b1(b.subst_at(k, u, depth))),
            Fol::Eq(a, b) => Fol::Eq(b1(a.subst_at(k, u, depth)), b1(b.subst_at(k, u, depth))),
            Fol::Neg(a) => Fol::Neg(b1(a.subst_at(k, u, depth))),
            Fol::And(a, b) => Fol::And(b1(a.subst_at(k, u, depth)), b1(b.subst_at(k, u, depth))),
            Fol::Or(a, b) => Fol::Or(b1(a.subst_at(k, u, depth)), b1(b.subst_at(k, u, depth))),
            Fol::Imp(a, b) => Fol::Imp(b1(a.subst_at(k, u, depth)), b1(b.subst_at(k, u, depth))),
            Fol::All(a) => Fol::All(b1(a.subst_at(k, u, depth + 1))),
            Fol::Ex(a) => Fol::Ex(b1(a.subst_at(k, u, depth + 1))),
        }
    }
}

fn b1(f: Fol) -> Box<Fol> {
    Box::new(f)
}

// -- ergonomic AST builders --------------------------------------------------

/// `∀x. body[fvar k := bvar 0]` — abstract the fresh atom `k` and wrap in
/// `All`. The natural way to build a quantified formula from an open one.
pub fn forall_atom(k: u64, body: Fol) -> Fol {
    Fol::All(b1(body.close(k)))
}

/// `∃x. body[fvar k := bvar 0]`.
pub fn exists_atom(k: u64, body: Fol) -> Fol {
    Fol::Ex(b1(body.close(k)))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::init::eq::beta_nf;

    fn norm(t: Term) -> Term {
        beta_nf(t).concl().as_eq().unwrap().1.clone()
    }

    /// Encoded terms/formulas are well-typed at the carrier `Φ⟨'r⟩`.
    #[test]
    fn constructors_are_typed() {
        assert_eq!(zero().type_of().unwrap(), phi());
        assert_eq!(bvar(0).type_of().unwrap(), phi());
        assert_eq!(fvar(0).type_of().unwrap(), phi());
        assert_eq!(succ(zero()).type_of().unwrap(), phi());
        assert_eq!(add(fvar(0), zero()).type_of().unwrap(), phi());
        assert_eq!(eq(fvar(0), zero()).type_of().unwrap(), phi());
        assert_eq!(all(eq(bvar(0), bvar(0))).type_of().unwrap(), phi());
        assert_eq!(
            imp(eq(fvar(0), zero()), neg(eq(fvar(1), zero())))
                .type_of()
                .unwrap(),
            phi()
        );
    }

    /// Genuine syntax: structurally different formulas are *distinct HOL
    /// terms* (after β-normalisation), not collapsed to their meanings.
    #[test]
    fn constructors_are_distinct() {
        assert_ne!(norm(zero()), norm(succ(zero())));
        assert_ne!(norm(fvar(0)), norm(fvar(1)));
        assert_ne!(norm(bvar(0)), norm(fvar(0)));
        assert_ne!(
            norm(eq(fvar(0), zero())),
            norm(eq(zero(), fvar(0))) // a = 0  ≠  0 = a
        );
        assert_ne!(
            norm(all(eq(bvar(0), zero()))),
            norm(ex(eq(bvar(0), zero())))
        );
        assert_ne!(norm(add(fvar(0), fvar(1))), norm(mul(fvar(0), fvar(1))));
    }

    /// `apply_handlers ∘ close_handlers = id` up to β at the carrier.
    #[test]
    fn fold_roundtrips() {
        let r = rty();
        // A well-typed fold body `: r`: `succ zero`.
        let body = Term::app(handler(&r, "succ"), handler(&r, "zero"));
        // (apply_handlers (close_handlers body)) β= body, structurally.
        let round = apply_handlers(&r, close_handlers(&r, body.clone()));
        assert_eq!(norm(round), norm(body));
    }

    // -- Phase A2: the AST + locally-nameless substitution -------------------

    /// `encode` of the AST agrees with the direct polymorphic builders.
    #[test]
    fn ast_encode_matches_builders() {
        let f = Fol::Imp(
            Box::new(Fol::Eq(Box::new(Fol::FVar(0)), Box::new(Fol::Zero))),
            Box::new(Fol::Neg(Box::new(Fol::Eq(
                Box::new(Fol::FVar(1)),
                Box::new(Fol::Zero),
            )))),
        );
        let direct = imp(eq(fvar(0), zero()), neg(eq(fvar(1), zero())));
        assert_eq!(norm(f.encode()), norm(direct));
    }

    /// `open` replaces `BVar 0` and decrements deeper indices.
    #[test]
    fn open_substitutes_bvar0() {
        // body = (bvar0 = bvar1) ; open with fvar 5
        let body = Fol::Eq(Box::new(Fol::BVar(0)), Box::new(Fol::BVar(1)));
        let opened = body.open(&Fol::FVar(5));
        // bvar0 -> fvar5, bvar1 -> bvar0
        assert_eq!(
            opened,
            Fol::Eq(Box::new(Fol::FVar(5)), Box::new(Fol::BVar(0)))
        );
    }

    /// `close` then `open` at a fresh atom round-trips (the locally-nameless
    /// `open ∘ close = id` law, the basis of the substitution lemma).
    #[test]
    fn close_open_roundtrip() {
        let phi = Fol::And(
            Box::new(Fol::Eq(Box::new(Fol::FVar(3)), Box::new(Fol::Zero))),
            Box::new(Fol::Neg(Box::new(Fol::Eq(
                Box::new(Fol::FVar(3)),
                Box::new(Fol::FVar(4)),
            )))),
        );
        // close atom 3 into bvar0, then open with fvar 3 → original.
        let closed = phi.close(3);
        let reopened = closed.open(&Fol::FVar(3));
        assert_eq!(reopened, phi);
    }

    /// `subst_fvar` under a quantifier shifts the replacement so its bound
    /// indices stay valid (capture-avoidance for free).
    #[test]
    fn subst_under_binder_shifts() {
        // ∀. (fvar0 = bvar0)   substitute fvar0 := (bvar0)  [a term that
        // refers to an OUTER binder]. Under the ∀, the replacement must
        // become bvar1 so it still points outside.
        let phi = Fol::All(Box::new(Fol::Eq(
            Box::new(Fol::FVar(0)),
            Box::new(Fol::BVar(0)),
        )));
        let out = phi.subst_fvar(0, &Fol::BVar(0));
        assert_eq!(
            out,
            Fol::All(Box::new(Fol::Eq(
                Box::new(Fol::BVar(1)),
                Box::new(Fol::BVar(0)),
            )))
        );
    }

    /// `forall_atom` builds a closed quantifier from an open formula.
    #[test]
    fn forall_atom_closes() {
        // ∀x. x = 0   from the open `fvar7 = 0`.
        let q = forall_atom(7, Fol::Eq(Box::new(Fol::FVar(7)), Box::new(Fol::Zero)));
        assert_eq!(
            q,
            Fol::All(Box::new(Fol::Eq(
                Box::new(Fol::BVar(0)),
                Box::new(Fol::Zero)
            )))
        );
    }
}
