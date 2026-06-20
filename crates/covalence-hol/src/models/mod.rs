//! `models` — the **minimal surface-compiler core**: the
//! `Logic`/`Model`/`Theory` triad of `docs/theories-models-and-logics.md`
//! §1, cut down to the smallest shape that makes the **objective function**
//! pass:
//!
//! > The SAME proof of `add_comm` (`∀a b. a + b = b + a`), written ONCE
//! > against the abstract `Nat` interface, checks at TWO different *models*
//! > of `Nat` in HOL — `nat/self` (carrier kernel `nat`) and `nat/unary`
//! > (carrier `list unit`) — each yielding a genuine (hyp-free) theorem at
//! > its own carrier.
//!
//! This is the *forcing function* that pins the metatheory abstractions in
//! code: prove once against the axioms, replay per model.
//!
//! # The shape that landed (warts and all)
//!
//! - [`NatSig`] is the `Nat` **signature** realized at a carrier: the carrier
//!   type `α` and the three operation terms `zero : α`, `succ : α→α`,
//!   `add : α→α→α`.
//! - [`NatModel`] is a **model** = a [`NatSig`] interpretation **plus** the
//!   four Peano-addition axioms proved at that carrier (`zero.add`,
//!   `add.zero`, `succ.add`, `add.succ`) **plus** an induction handler (the
//!   model's `Logic`-supplied tactic that realizes `(m.induct …)` for that
//!   carrier). The axiom-satisfaction proof IS the model.
//! - [`Logic`] is the trait of `theories-models §1.1` — an **interpreter for
//!   signatures**: it realizes the `Nat` signature at its carrier
//!   ([`Logic::nat_model`]) and lifts surface literals into its carrier
//!   ([`Logic::lift_int`] / [`lift_string`](Logic::lift_string) /
//!   [`lift_bytes`](Logic::lift_bytes)), each **model-relative and fallible**.
//! - [`NatSelf`] and [`NatUnary`] are the two `Logic` impls (the two carriers).
//!
//! Dispatch is the [`monoid_env`](crate::init::monoid::monoid_env) pattern: a
//! model installs its operators + axioms + induction handler into an [`Env`]
//! under the **abstract** names the `add_comm.cov` proof references
//! (`m.zero`/`m.succ`/`m.add`, `zero.add`/`add.zero`/`succ.add`/`add.succ`,
//! `m.induct`). The same `.cov` source runs against either env and proves the
//! same statement at the respective carrier — see [`prove_add_comm`].
//!
//! # What `nat/unary` pressured
//!
//! The `monoid` precedent dispatches only **rewrite laws** (uniform across
//! models). `add_comm` needs **induction**, which is *structurally* different
//! per carrier (`Thm::nat_induct` vs `list_induct`), so the abstraction had to
//! grow a handler whose **internals differ per model** while its surface
//! (`(m.induct VAR BASE STEP)`) stays identical — exactly the
//! "model = handler set + interpretation" split. And `nat/unary`'s `add.succ`
//! axiom (`cat xs (succ ys) = succ (cat xs ys)`) is *false for general lists*;
//! it holds for `list unit` only because every element is `unit.nil`
//! (`Thm::unit_eq`) — so the literal-lift conversion and the axiom proof both
//! lean on the singleton, the genuine new content the second model forces.

pub mod unary;

use std::sync::Arc;

use covalence_core::{Term, Thm, Type};
use covalence_types::Int;

use crate::script::{ConstDef, Env, Tactic};

/// The error a model-relative literal lift returns when the logic has no
/// sensible lowering for that literal kind (the `NoLiteral` of
/// `theories-models §1.1`). A diagnostic, never a silent coercion.
#[derive(Debug, Clone, thiserror::Error)]
#[error("this logic has no lift for a {kind} literal")]
pub struct NoLiteral {
    /// The literal kind that could not be lowered (`"int"`, `"string"`, …).
    pub kind: &'static str,
}

impl NoLiteral {
    fn of(kind: &'static str) -> Self {
        NoLiteral { kind }
    }
}

/// The **`Nat` signature realized at a carrier** — the interpretation half of
/// a model (`theories-models §1`): the carrier type `α` and the three
/// operation terms, *unapplied*.
#[derive(Clone)]
pub struct NatSig {
    /// The carrier type `α` (`nat`, `list unit`, …).
    pub carrier: Type,
    /// `zero : α`.
    pub zero: Term,
    /// `succ : α → α`.
    pub succ: Term,
    /// `add : α → α → α`.
    pub add: Term,
}

/// A **model of the `Nat` theory in HOL**: a [`NatSig`] interpretation plus
/// the four Peano-addition axioms proved at the carrier, plus the induction
/// handler the carrier's `Logic` supplies. Built by [`Logic::nat_model`].
///
/// The four axioms are stored `∀`-quantified (the `rw`-ready shape):
/// - `zero_add` : `⊢ ∀a. add zero a = a`
/// - `add_zero` : `⊢ ∀a. add a zero = a`
/// - `succ_add` : `⊢ ∀a b. add (succ a) b = succ (add a b)`
/// - `add_succ` : `⊢ ∀a b. add a (succ b) = succ (add a b)`
pub struct NatModel {
    /// The interpretation (carrier + ops).
    pub sig: NatSig,
    /// `⊢ ∀a. add zero a = a`.
    pub zero_add: Thm,
    /// `⊢ ∀a. add a zero = a`.
    pub add_zero: Thm,
    /// `⊢ ∀a b. add (succ a) b = succ (add a b)`.
    pub succ_add: Thm,
    /// `⊢ ∀a b. add a (succ b) = succ (add a b)`.
    pub add_succ: Thm,
    /// The model's induction tactic, registered as `m.induct` in its env —
    /// the proof-side dispatch (`theories-models §1.1`'s `HandlerSet`, here
    /// cut to its one load-bearing member).
    pub induct: Arc<dyn Tactic>,
}

impl NatModel {
    /// Install this model into an [`Env`] under the **abstract** names the
    /// `add_comm.cov` proof references — the [`monoid_env`](crate::init::monoid::monoid_env)
    /// pattern for `Nat`. A proof written against these names proves the same
    /// statement at *every* model's carrier.
    pub fn env(&self) -> Env {
        let mut e = Env::empty();
        e.define_const("m.zero", ConstDef::Op(self.sig.zero.clone()));
        e.define_const("m.succ", ConstDef::Op(self.sig.succ.clone()));
        e.define_const("m.add", ConstDef::Op(self.sig.add.clone()));
        e.define_lemma("zero.add", self.zero_add.clone());
        e.define_lemma("add.zero", self.add_zero.clone());
        e.define_lemma("succ.add", self.succ_add.clone());
        e.define_lemma("add.succ", self.add_succ.clone());
        e.register_tactic("m.induct", self.induct.clone());
        e
    }
}

/// The **`Logic` trait** of `theories-models §1.1`, cut to the minimum the
/// objective function needs: a logic is an **interpreter for the `Nat`
/// signature** (it realizes the ops at *its* carrier and supplies the
/// induction handler), plus the **model-relative, fallible literal lifts**.
///
/// (The full trait also carries `admits`/`handlers`/`interpret` over an
/// arbitrary `Signature`; here the signature is fixed to `Nat`, so
/// [`nat_model`](Logic::nat_model) *is* `interpret`+`handlers` specialized.
/// Generalizing to an arbitrary signature is the obvious next cut — see
/// `SKELETONS.md`.)
pub trait Logic {
    /// A short identifier for the model (`"nat/self"`, `"nat/unary"`).
    fn name(&self) -> &'static str;

    /// Realize the `Nat` signature at this logic's carrier **and** discharge
    /// the four addition axioms there — the whole model. Fallible: assembling
    /// the carrier's axiom proofs can fail in the kernel.
    fn nat_model(&self) -> Result<NatModel, covalence_core::Error>;

    /// **Literal lifting (model-relative, fallible).** Lower a surface integer
    /// literal `n ≥ 0` into this carrier. For `nat/self` this is the built-in
    /// `nat` literal; for `nat/unary` it runs a genuine builtin-nat → unary
    /// **conversion** (`3 ↦ cons unit.nil (cons unit.nil (cons unit.nil nil))`).
    /// A logic with no sensible lift returns `Err(NoLiteral)`.
    fn lift_int(&self, n: &Int) -> Result<Term, NoLiteral>;

    /// Lower a surface string literal into this carrier (default: no lift).
    fn lift_string(&self, _s: &str) -> Result<Term, NoLiteral> {
        Err(NoLiteral::of("string"))
    }

    /// Lower a surface bytes literal into this carrier (default: no lift).
    fn lift_bytes(&self, _b: &[u8]) -> Result<Term, NoLiteral> {
        Err(NoLiteral::of("bytes"))
    }
}

/// Run the abstract `add_comm.cov` proof against `model`'s env and return the
/// resulting **genuine** theorem at the model's carrier. The whole objective
/// function in one call: ONE `.cov` source, dispatched per model.
pub fn prove_add_comm(model: &NatModel) -> Result<Thm, crate::script::ScriptError> {
    let env = model.env();
    let theory = crate::script::run(
        include_str!("add_comm.cov"),
        move |name| match name {
            "core" => Some(Env::core()),
            "natmodel" => Some(env.clone()),
            _ => None,
        },
        |_| None,
    )?
    .resolve_blocking()?;
    Ok(theory.lemma("add.comm"))
}

// ============================================================================
// The two models.
// ============================================================================

/// `nat/self` — the carrier is the kernel `nat`; `0 ↦ nat.zero`,
/// `succ ↦ nat.succ`, `+ ↦ nat.add`; induction = HOL `nat_induct`.
pub struct NatSelf;

/// `nat/unary` — the carrier is `list unit`; `0 ↦ nil`,
/// `succ ↦ cons unit.nil`, `+ ↦ append (list.cat)`; induction = `list_induct`.
pub struct NatUnary;

impl Logic for NatSelf {
    fn name(&self) -> &'static str {
        "nat/self"
    }

    fn nat_model(&self) -> Result<NatModel, covalence_core::Error> {
        use crate::init::nat;
        let sig = NatSig {
            carrier: Type::nat(),
            zero: Term::nat_lit(0u32),
            succ: Term::succ(),
            add: covalence_core::defs::nat_add(),
        };
        // The induction handler is the kernel-`nat` `induct` tactic from
        // `core` — `nat/self`'s induction principle is HOL `nat_induct`.
        let induct = Env::core()
            .lookup_tactic("induct")
            .expect("core provides the nat `induct` tactic");
        Ok(NatModel {
            sig,
            zero_add: nat::add_base(),    // ∀m. 0 + m = m
            add_zero: nat::add_zero(),    // ∀a. a + 0 = a
            succ_add: nat::add_step(),    // ∀n m. S n + m = S(n + m)
            add_succ: nat::add_succ_r(),  // ∀a b. a + S b = S(a + b)
            induct,
        })
    }

    fn lift_int(&self, n: &Int) -> Result<Term, NoLiteral> {
        // A non-negative Int literal lifts to the built-in `nat` literal.
        let nat: covalence_types::Nat = n
            .clone()
            .try_into()
            .map_err(|_| NoLiteral::of("int (negative — not a Nat)"))?;
        Ok(Term::nat_lit(nat))
    }
}

impl Logic for NatUnary {
    fn name(&self) -> &'static str {
        "nat/unary"
    }

    fn nat_model(&self) -> Result<NatModel, covalence_core::Error> {
        let sig = NatSig {
            carrier: unary::carrier(),
            zero: unary::zero(),
            succ: unary::succ_op(),
            add: unary::add_op(),
        };
        Ok(NatModel {
            sig,
            zero_add: unary::zero_add()?,
            add_zero: unary::add_zero()?,
            succ_add: unary::succ_add()?,
            add_succ: unary::add_succ()?,
            induct: unary::induct_tactic(),
        })
    }

    fn lift_int(&self, n: &Int) -> Result<Term, NoLiteral> {
        // The builtin-nat → unary CONVERSION: `n ↦ cons unit.nil (… nil)`,
        // `n` copies of `unit.nil`. (A Nat literal is a non-negative Int.)
        let mut k: covalence_types::Nat = n
            .clone()
            .try_into()
            .map_err(|_| NoLiteral::of("int (negative — not a Nat)"))?;
        let mut acc = unary::zero();
        let succ = unary::succ_op();
        let one = covalence_types::Nat::from(1u32);
        let mut count = 0u64;
        while k > covalence_types::Nat::zero() {
            acc = Term::app(succ.clone(), acc);
            k = k.checked_sub(&one).expect("k > 0");
            count += 1;
            // Guard against absurd literals exhausting memory.
            if count > 1_000_000 {
                return Err(NoLiteral::of("int (too large for a unary lift)"));
            }
        }
        Ok(acc)
    }
}

#[cfg(test)]
mod tests;
