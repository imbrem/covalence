//! An honest **ACL2-flavoured dialect** (`hol` feature) — the first slice of
//! the `SExpr ⇒ Reduction ⇒ Lisp ⇒ ACL2` tower's top layer.
//!
//! ACL2 is an applicative, first-order Lisp with a definitional principle
//! (`defun` admitted only when it terminates) and a theorem event (`defthm`).
//! This module ships the *honest demo slice* of that discipline over the
//! existing value semantics ([`LispSemantics`], defun-as-hypothesis
//! recursion — see [`crate::defs`]):
//!
//! - **Primitives** — ACL2 spellings over the existing machinery: ternary
//!   `if` (no `cond`), `equal`, `consp` / `atom` / `endp`, `car` / `cdr` /
//!   `cons`, plus **ground** integer arithmetic `+` `-` `*` `<=` `=` `zp`
//!   `natp` (see below).
//! - **`defun`** — accepted only when it passes a *syntactic
//!   structural-recursion check* (every recursive call descends a `car`/`cdr`
//!   chain of the same formal; §admissibility below). This is a stated
//!   discipline, **not** a termination proof — no measures, no ordinals.
//!   Soundness never rests on it: an admitted `defun` still enters the kernel
//!   only as the *assumption* `{f = λ…} ⊢ f = λ…`, so even a wrongly-admitted
//!   non-terminating definition cannot mint a hypothesis-free falsehood.
//! - **`defthm`** — only what is genuinely provable *today*: **ground,
//!   decidable goals**. A ground `(equal LHS RHS)` over the reified fragment
//!   (quoted data, integer literals, and the mapped
//!   [`PrimRow`](covalence_init::init::acl2::prims::PrimRow) primitives —
//!   see [`row_spelling`]) is proved **through the S0–S3 ladder**
//!   ([`covalence_init::init::acl2`]): the dialect builds a
//!   `⊢ Derivable_ACL2 ⌜goal⌝` *certificate* (a hypothesis-free theorem
//!   about the reified derivability predicate), projects it through the
//!   machine-checked soundness metatheorem
//!   `⊢ ∀A. Derivable_ACL2 A ⟹ (∀σ. ¬(eval A σ = anil))`, and transports it
//!   to the **base-HOL model equation** that is stored and shown (e.g.
//!   `(defthm four (equal (+ 2 2) 4))` stores
//!   `⊢ aplus (aint 2) (aint 2) = aint 4`). Everything else falls back to
//!   the pre-ladder path: discharge by kernel reduction (drive to `T`, then
//!   `eqt_elim`). A goal with free variables is **rejected** with a message
//!   naming what is missing (induction — future work); a false ground goal
//!   is refuted, never faked. [`Acl2Session::theorem_entry`] records which
//!   path proved each stored theorem ([`Acl2Proof`]).
//!
//! # The honesty invariant
//!
//! Exactly the [`crate::session`] contract: every value printed by
//! [`Acl2Session::eval_cell`] is read off the right-hand side of a genuine
//! kernel theorem carried in the [`Acl2Outcome`]; every stored `defthm` is a
//! genuine kernel [`Thm`] whose hypotheses (if any) are exactly the `defun`
//! equations the proof used. Anything unprovable returns a clean `Err`.
//!
//! # Admissibility (the demo criterion, stated exactly)
//!
//! `(defun f (x₁ … xₙ) body)` is admitted iff:
//!
//! 1. every form in `body` is a known primitive, a previously admitted
//!    `defun`, or `f` itself, applied at the right arity (definition before
//!    use — no forward references);
//! 2. every atom in `body` (outside `quote`) is `t`, `nil`, or a formal; and
//! 3. if `body` calls `f`, there is a formal position `i` such that **every**
//!    recursive call passes, in position `i`, a non-empty `car`/`cdr` chain
//!    applied to the formal `xᵢ` (e.g. `(app (cdr x) y)` descends `x`).
//!
//! This accepts the Little-Schemer staples (`app`, `member?`, …) and rejects
//! `(defun bad (x) (bad x))` and `(defun grow (x) (grow (cons x x)))` with a
//! clear message. It is deliberately weaker than ACL2's measure-based
//! definitional principle (e.g. it does not verify the `endp`/`consp` guard);
//! termination *proofs* are future work — see the generated open-work index and
//! `notes/vibes/lisp/acl2-dialect.md`.
//!
//! # Integers (on the value semantics' [`IntBackend`] integration)
//!
//! Integers ride the value semantics' integer support (the
//! [`crate::int_backend::IntBackend`] seam, wired by default in
//! [`LispSemantics`]): numerals compile to kernel `int` literals and
//! `+ - * <= =` to the kernel `int.add` / `int.sub` / `int.mul` / `int.le` /
//! `(=):int` operators, whose reductions are **kernel-proved** computation
//! equations (never asserted). `zp` / `natp` are compiled as their integer
//! meanings (`zp n` ⇔ `n ≤ 0`, `natp n` ⇔ `0 ≤ n` — on `int`-typed terms
//! `integerp` is `t` by typing), and `equal` routes to integer `=` when
//! either side is syntactically arithmetic.
//!
//! One honest limitation: kernel integers are **typed `int` terms, not
//! `sexpr` data**, so mixed structures (`(cons 1 nil)`, an integer passed to
//! a list-typed formal) are not expressible — they are rejected with a clear
//! message, never mis-evaluated. Integer-*valued* recursion over lists
//! (e.g. `len`) works: the recursive head's return type is inferred as
//! `int`.

use std::collections::BTreeMap;
use std::sync::{LazyLock, Mutex};

use covalence_core::subst;
use covalence_hol_eval::EvalThm as Thm;
use covalence_hol_eval::derived::DerivedRules;
use covalence_hol_eval::{as_bool, as_int, mk_int};
use covalence_init::Term;
use covalence_init::init::acl2::append::{
    append_assoc_fact, append_count_strict_fact, append_definition_fact, append_nonempty_fact,
    append_of_cons_fact, append_when_consp_nil_fact, car_of_append_fact,
    car_of_append_when_consp_fact, cdr_of_append_fact, cdr_of_append_when_consp_fact,
    consp_of_append_fact, equal_when_append_same_fact, with_append, with_append_count_laws,
};
use covalence_init::init::acl2::carrier::acl2_payload;
use covalence_init::init::acl2::count::{
    acl2_count_car_strict_fact, acl2_count_car_weak_fact, acl2_count_cdr_strict_fact,
    acl2_count_cdr_weak_fact, acl2_count_cons_greater_fact, acl2_count_consp_positive_fact,
    acl2_count_natp_fact, acl2_count_sum_strict_fact, acl2_count_sum_weak_fact, with_acl2_count,
};
use covalence_init::init::acl2::defun::{
    Acl2Session as KernelAcl2Session, DefunSpec, admit_defun as admit_kernel_defun, defun_ground,
    defun_law,
};
use covalence_init::init::acl2::derivable::s6_env;
use covalence_init::init::acl2::derivable::{self as ladder, Acl2Env};
use covalence_init::init::acl2::fixers::with_fixers;
use covalence_init::init::acl2::hilbert::Fact;
use covalence_init::init::acl2::ordinal::with_ordinals;
use covalence_init::init::acl2::simplify::{
    FactCache, IndConfig, prove_by_induction, with_arith_rules,
};
use covalence_init::init::acl2::term::Terms;
use covalence_init::init::eq::{beta_expand, beta_reduce};
use covalence_init::init::ext::{TermExt, ThmExt};
use covalence_kernel_lisp::{
    AdmissionPolicy, AdmissionReplay, Definition as LispDefinition, Evaluation,
    EvaluationExistence, MayEvalReplay, MayEvalTransport, SourcedDefinition, TraceReplay, evaluate,
};
use covalence_repl_core::{Fuel, Reduction, RunToValue, Strategy};
use covalence_sexp::{Atom, SExpr};
use covalence_types::Int;

use crate::defs::{Defs, install_core_definition};
use crate::frontend::{
    Frontend, FrontendExpr, HostFrontendRuntime, HostSession, RuntimeEvaluation, SurfaceDialect,
};
use crate::hol::HolError;
use crate::reader::{ReadError, read_one};
use crate::relation::{LispMayEvalEvidence, LispRel};
use crate::semantics::{EquationalHostMayEvalEvidence, LispRepr, LispSemantics, ValueKind};

/// Step budget for a value reduction — recursion is admitted by a *syntactic*
/// check, not a proof, so the driver must stay fuel-bounded (divergence is a
/// clean error, never a hang).
const FUEL: u64 = 100_000;

/// The surface theorem shadow: structural induction plus the proved ordinal
/// pack and the premise-builder's oriented arithmetic rows. Building this
/// composition changes no trusted surface; each row carries and re-checks its
/// model theorem while the per-generation soundness proof consumes it.
fn shadow_env() -> covalence_core::Result<Acl2Env> {
    let structural = s6_env()?;
    let ordinal = with_ordinals(&structural)?;
    let fixers = with_fixers(&ordinal)?;
    let count = with_acl2_count(&fixers)?;
    let append = with_append(&count)?;
    let append_count = with_append_count_laws(&append)?;
    with_arith_rules(&append_count)
}

fn shadow_cache(env: &Acl2Env) -> covalence_core::Result<FactCache> {
    let cache = FactCache::default();
    for fact in [
        acl2_count_natp_fact(env)?,
        acl2_count_sum_strict_fact(env)?,
        acl2_count_sum_weak_fact(env)?,
        acl2_count_car_strict_fact(env)?,
        acl2_count_cdr_strict_fact(env)?,
        acl2_count_car_weak_fact(env)?,
        acl2_count_cdr_weak_fact(env)?,
        acl2_count_consp_positive_fact(env)?,
        acl2_count_cons_greater_fact(env)?,
        // Keep specific APPEND rules ahead of the generic defining equation:
        // lemma selection is deliberately deterministic and first-match, so
        // unfolding first would hide the stronger constructor/guard shapes.
        consp_of_append_fact(env)?,
        equal_when_append_same_fact(env)?,
        append_nonempty_fact(env)?,
        append_count_strict_fact(env)?,
        car_of_append_when_consp_fact(env)?,
        car_of_append_fact(env)?,
        cdr_of_append_when_consp_fact(env)?,
        cdr_of_append_fact(env)?,
        append_assoc_fact(env)?,
        append_of_cons_fact(env)?,
        append_when_consp_nil_fact(env)?,
        append_definition_fact(env)?,
    ] {
        cache.add_lemma(fact);
    }
    Ok(cache)
}

// ============================================================================
// Errors
// ============================================================================

/// An ACL2-cell error: read, evaluation, admissibility, or proof failure.
#[derive(Debug, thiserror::Error)]
pub enum Acl2Error {
    /// The cell text failed to parse as one S-expression.
    #[error(transparent)]
    Read(ReadError),
    /// Evaluation failed (stuck term, kernel error, fuel exhausted).
    #[error(transparent)]
    Eval(HolError),
    /// A `defun` failed the admissibility check.
    #[error("defun `{name}` not admitted: {reason}")]
    Inadmissible {
        /// The function name.
        name: String,
        /// Why it was rejected.
        reason: String,
    },
    /// A `defthm` goal could not be proved (and was NOT faked).
    #[error("defthm `{name}` rejected: {reason}")]
    Unprovable {
        /// The theorem name.
        name: String,
        /// Why it was rejected (what is missing).
        reason: String,
    },
    /// A malformed event or unsupported form.
    #[error("{0}")]
    Malformed(String),
}

impl From<HolError> for Acl2Error {
    fn from(e: HolError) -> Self {
        Acl2Error::Eval(e)
    }
}

fn kernel_err(e: impl core::fmt::Display) -> Acl2Error {
    Acl2Error::Eval(HolError::Kernel(e.to_string()))
}

fn bridge_kernel_err(e: impl core::fmt::Display) -> HolError {
    HolError::Kernel(e.to_string())
}

// ============================================================================
// Outcomes
// ============================================================================

/// The value-kind of an ACL2 outcome, for printing.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Acl2ValueKind {
    /// A `sexpr` datum (`atom` / `snil` / `scons` chains).
    Data,
    /// A `bool` literal (predicate / `equal` result) — printed `t` / `nil`.
    Bool,
    /// A kernel `int` literal (ground arithmetic) — printed as a decimal.
    Int,
}

/// The result of evaluating one ACL2 expression: the value term and the
/// kernel theorem backing it. The value is **always** the theorem's RHS.
#[derive(Clone, Debug)]
pub struct Acl2Outcome {
    /// The normal-form value term (the theorem's RHS).
    pub value: Term,
    /// `hyps ⊢ input = value` — the composite kernel theorem. The hypotheses,
    /// if any, are exactly the `defun` equations the reduction unfolded.
    pub thm: Thm,
    /// How to print `value`.
    pub kind: Acl2ValueKind,
}

/// How a stored `defthm` was proved (both paths mint genuine kernel
/// theorems; this records *which machinery* produced the stored one).
#[derive(Clone, Debug)]
pub enum Acl2Proof {
    /// Through the reified S0–S3 ladder: `derivation` is the
    /// hypothesis-free certificate `⊢ Derivable_ACL2 ⌜goal⌝`, which was
    /// projected through the machine-checked soundness metatheorem and
    /// transported ([`covalence_init::init::acl2::derivable::transport_equal`])
    /// to the stored base-HOL model equation.
    Certificate {
        /// `⊢ Derivable_ACL2 ⌜goal⌝` — the reified derivation itself.
        derivation: Thm,
    },
    /// By the generic S6 premise builder and structural induction, followed
    /// by the same soundness projection and open-goal transport.
    Induction {
        /// `⊢ Derivable_ACL2 ⌜goal⌝`.
        derivation: Thm,
        /// The object variable selected by the recursion-vote heuristic.
        variable: Option<Vec<u8>>,
    },
    /// By certified kernel value reduction (drive the goal to `T`, then
    /// `eqt_elim`) — the fallback for ground goals outside the reified
    /// fragment (its hypotheses, if any, are the `defun` equations used).
    Reduction,
}

/// A stored `defthm`: the kernel theorem plus how it was proved.
#[derive(Clone, Debug)]
pub struct Acl2Theorem {
    /// The stored kernel theorem. On the [`Acl2Proof::Certificate`] path
    /// this is the transported base-HOL **model equation** (e.g.
    /// `⊢ aplus (aint 2) (aint 2) = aint 4`); on the
    /// [`Acl2Proof::Reduction`] path it is `hyps ⊢ goal` over the value
    /// semantics.
    pub thm: Thm,
    /// Which path proved it.
    pub proof: Acl2Proof,
}

/// Plain structural-admission witness retained for an ACL2 `defun`.
///
/// This records what the surface checker established. It is not a theorem and
/// cannot totalize the function; the deep ACL2/HOL layer must replay suitable
/// evidence before gaining theorem authority.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Acl2Admission {
    pub recursive_calls: usize,
    pub decreasing_parameter: Option<usize>,
}

/// One ACL2 definition with source provenance and shared operational core.
pub type Acl2Definition = SourcedDefinition<String, SExpr, FrontendExpr>;

/// A conservative HOL definition produced by replaying an ACL2 admission.
///
/// Unlike [`Acl2Admission`], both fields are kernel objects: `model` is the
/// newly defined total function and `defining_equation` is its proved
/// equation. This still does not, by itself, identify the total model with
/// the generic partial Lisp execution relation; that bridge is a separate
/// existence/uniqueness obligation.
#[derive(Clone)]
pub struct Acl2HolDefinition {
    pub model: Term,
    pub defining_equation: Thm,
}

/// Proof-producing replay against one deep ACL2/HOL environment generation.
pub struct Acl2HolReplay<'a> {
    env: &'a Acl2Env,
}

impl<'a> Acl2HolReplay<'a> {
    pub fn new(env: &'a Acl2Env) -> Self {
        Self { env }
    }
}

/// The result of conservative definition replay. The returned environment is
/// a fresh generation containing the definition.
pub struct Acl2HolReplayEvidence {
    pub environment: Acl2Env,
    pub definition: Acl2HolDefinition,
}

/// Checked pointwise agreement between relational Lisp execution and ACL2's
/// conservatively admitted `APPEND` model.
///
/// `execution.reduction` proves that the common operational relation reaches
/// `execution.value`. `model_agreement` independently proves that ACL2's
/// total model at the same inputs equals that value. Both are closed kernel
/// theorems; the host driver below carries no theorem authority.
///
/// This is deliberately pointwise. The universal existence theorem is exposed
/// separately; universal uniqueness remains the admission-layer obligation.
#[derive(Clone)]
pub struct Acl2AppendExecutionEvidence {
    pub execution: LispMayEvalEvidence,
    pub model_agreement: Thm,
}

/// Replay one concrete ACL2 `APPEND` call through both semantic layers.
pub fn replay_acl2_append_execution(
    environment: &Acl2Env,
    left: Term,
    right: Term,
    fuel: usize,
) -> Result<Acl2AppendExecutionEvidence, HolError> {
    let relation = LispRel::over_acl2_carrier()?;
    if !relation.is_value(&left) || !relation.is_value(&right) {
        return Err(HolError::Stuck(
            "ACL2 APPEND execution inputs must be carrier values".into(),
        ));
    }
    let input = relation.append_of(left.clone(), right.clone())?;
    let evaluation = evaluate(&relation, input, fuel)
        .map_err(|error| HolError::Stuck(format!("ACL2 APPEND execution failed: {error:?}")))?;
    let Evaluation::Value(evaluation) = evaluation else {
        return Err(HolError::Stuck(
            "ACL2 APPEND relational execution ended stuck".into(),
        ));
    };
    let trace = relation.replay(&relation, &evaluation.trace)?;
    let execution = relation.replay_may_eval(&relation, &evaluation, &trace)?;
    let model_agreement = defun_ground(environment, "APPEND", &[left, right])
        .map_err(|error| HolError::Kernel(error.to_string()))?;
    let (_, model_value) = model_agreement
        .concl()
        .as_eq()
        .ok_or_else(|| HolError::Kernel("ACL2 APPEND model replay was not an equation".into()))?;
    if model_value != &execution.value || !model_agreement.hyps().is_empty() {
        return Err(HolError::Kernel(
            "ACL2 APPEND model and relational execution disagree".into(),
        ));
    }
    Ok(Acl2AppendExecutionEvidence {
        execution,
        model_agreement,
    })
}

/// Prove universal existence of relational execution for ACL2 `APPEND`.
///
/// The result is exactly
///
/// ```text
/// ⊢ ∀x y. Reduces (rel-append x y) (ACL2-APPEND-model x y)
/// ```
///
/// over ACL2's actual object carrier. The proof uses structural induction on
/// `x`, rule induction for the `Reduces` congruence under `cons`, and the
/// conservatively admitted APPEND equation. It performs no host execution.
pub fn replay_acl2_append_existence(
    environment: &Acl2Env,
) -> Result<EvaluationExistence<Thm>, HolError> {
    let (_, append) = environment
        .user("APPEND")
        .map_err(|error| HolError::Kernel(error.to_string()))?;
    let relation = LispRel::over_acl2_carrier()?;
    let tm = &*environment.tm;
    let carrier = tm.th.ty.clone();
    let x = Term::free("__append_total_x", carrier.clone());
    let y = Term::free("__append_total_y", carrier.clone());
    let relational = |left: Term, right: Term| relation.append_of(left, right);
    let model = |left: Term, right: Term| {
        append
            .model
            .clone()
            .apply(left)
            .map_err(|error| HolError::Kernel(error.to_string()))?
            .apply(right)
            .map_err(|error| HolError::Kernel(error.to_string()))
    };
    let body = relation.reduces_prop(
        &relational(x.clone(), y.clone())?,
        &model(x.clone(), y.clone())?,
    )?;
    let all_y = body
        .clone()
        .forall("__append_total_y", carrier.clone())
        .map_err(|error| HolError::Kernel(error.to_string()))?;
    let motive = Term::abs(carrier.clone(), subst::close(&all_y, "__append_total_x"));

    let leaf_case = |leaf: Term, step: Thm| -> Result<Thm, HolError> {
        let input = relational(leaf.clone(), y.clone())?;
        let raw = relation.reduces_step(&input, &y, &y, step, relation.reduces_refl(&y)?)?;
        let law = defun_law(environment, append, &[leaf.clone(), y.clone()])
            .map_err(|error| HolError::Kernel(error.to_string()))?;
        let model_value = model(leaf.clone(), y.clone())?;
        let retargeted = relation.retarget_reduces(
            &input,
            &y,
            &model_value,
            raw,
            law.sym().map_err(bridge_kernel_err)?,
        )?;
        let all_y = retargeted
            .all_intro("__append_total_y", carrier.clone())
            .map_err(bridge_kernel_err)?;
        beta_expand(&motive, leaf, all_y).map_err(bridge_kernel_err)
    };

    let payload = Term::free("b", acl2_payload());
    let atom = tm
        .th
        .atom
        .clone()
        .apply(payload.clone())
        .map_err(bridge_kernel_err)?;
    let case_atom = leaf_case(atom, relation.step_append_atom(&payload, &y)?)?;
    let case_nil = leaf_case(tm.th.nil.clone(), relation.step_append_nil(&y)?)?;
    let case_cons = {
        let h = Term::free("h", carrier.clone());
        let t = Term::free("t", carrier.clone());
        let ph = motive.clone().apply(h.clone()).map_err(bridge_kernel_err)?;
        let pt = motive.clone().apply(t.clone()).map_err(bridge_kernel_err)?;
        let recursive_input = relational(t.clone(), y.clone())?;
        let recursive_model = model(t.clone(), y.clone())?;
        let ih = beta_reduce(Thm::assume(pt.clone()).map_err(bridge_kernel_err)?)
            .map_err(bridge_kernel_err)?
            .all_elim(y.clone())
            .map_err(bridge_kernel_err)?;
        let lifted = relation.reduces_scons_tail(&h, &recursive_input, &recursive_model, ih)?;
        let cons = relation.scons(h.clone(), t.clone())?;
        let input = relational(cons.clone(), y.clone())?;
        let middle = relation.scons(h.clone(), recursive_input)?;
        let output = relation.scons(h.clone(), recursive_model)?;
        let step = relation.step_append_cons(&h, &t, &y)?;
        let raw = relation.reduces_step(&input, &middle, &output, step, lifted)?;
        let law = defun_law(environment, append, &[cons.clone(), y.clone()])
            .map_err(|error| HolError::Kernel(error.to_string()))?;
        let model_value = model(cons.clone(), y.clone())?;
        let retargeted = relation.retarget_reduces(
            &input,
            &output,
            &model_value,
            raw,
            law.sym().map_err(bridge_kernel_err)?,
        )?;
        let all_y = retargeted
            .all_intro("__append_total_y", carrier.clone())
            .map_err(bridge_kernel_err)?;
        beta_expand(&motive, cons, all_y)
            .map_err(bridge_kernel_err)?
            .imp_intro(&pt)
            .map_err(bridge_kernel_err)?
            .imp_intro(&ph)
            .map_err(bridge_kernel_err)?
    };
    let induction = tm
        .th
        .induct(&motive, vec![case_atom, case_nil, case_cons])
        .map_err(bridge_kernel_err)?;
    let theorem = beta_reduce(induction.all_elim(x.clone()).map_err(bridge_kernel_err)?)
        .map_err(bridge_kernel_err)?
        .all_intro("__append_total_x", carrier.clone())
        .map_err(bridge_kernel_err)?;
    let expected = body
        .forall("__append_total_y", carrier.clone())
        .map_err(bridge_kernel_err)?
        .forall("__append_total_x", carrier)
        .map_err(bridge_kernel_err)?;
    if !theorem.hyps().is_empty() || theorem.concl() != &expected {
        return Err(HolError::Kernel(
            "universal ACL2 APPEND existence proof has the wrong theorem shape".into(),
        ));
    }
    Ok(EvaluationExistence { theorem })
}

impl AdmissionReplay<Acl2Definition, Acl2Admission> for Acl2HolReplay<'_> {
    type Termination = Acl2HolReplayEvidence;
    type Error = String;

    fn replay_termination(
        &self,
        definition: &Acl2Definition,
        certificate: &Acl2Admission,
    ) -> Result<Self::Termination, Self::Error> {
        let tm = &*self.env.tm;
        if definition.core.rest.is_some() {
            return Err("ACL2 logical definitions must have fixed arity".into());
        }
        let body = deep_encode(tm, &definition.source_body, &definition.core.parameters)?;
        let spec = DefunSpec {
            name: definition.core.name.to_ascii_uppercase().into(),
            formals: definition
                .core
                .parameters
                .iter()
                .map(|parameter| parameter.to_ascii_uppercase().into())
                .collect(),
            body,
            rec_formal: certificate.decreasing_parameter,
        };
        let environment = admit_kernel_defun(self.env, &spec).map_err(|error| error.to_string())?;
        let row = environment
            .users
            .last()
            .ok_or_else(|| "deep ACL2 replay returned no admitted definition".to_string())?;
        if row.name != spec.name {
            return Err("deep ACL2 replay returned the wrong definition".into());
        }
        Ok(Acl2HolReplayEvidence {
            definition: Acl2HolDefinition {
                model: row.model.clone(),
                defining_equation: row.def_eq_model.clone(),
            },
            environment,
        })
    }
}

// ============================================================================
// The session
// ============================================================================

/// An ACL2-dialect REPL session, mirroring [`crate::session::Session`]'s
/// `eval_cell` / `render` shape (phase-2 integration into the `#lang`
/// dispatch is a thin wrapper around this).
///
/// State: the admitted `defun` dictionary (kernel *hypotheses*, never axioms
/// — [`crate::defs`]) and the proved `defthm` table (genuine kernel
/// theorems, retrievable via [`theorem`](Acl2Session::theorem)).
pub struct Acl2Session {
    defs: Defs,
    admissions: BTreeMap<String, Acl2Admission>,
    definitions: BTreeMap<String, Acl2Definition>,
    hol_definitions: BTreeMap<String, Acl2HolDefinition>,
    /// The same definitions in the shared partial Lisp relation. Checked
    /// finite traces from this session carry no totality claim; they are the
    /// operational side of the future execution-adequacy theorem.
    operational: HostSession,
    thms: BTreeMap<String, Acl2Theorem>,
    /// A definition-free semantics for structural helpers (`tau`, renderers).
    sem0: LispSemantics,
    /// Shadow S6 environment for the sound generic premise builder. Defuns
    /// outside its conservative template remain available to the value
    /// semantics but are simply absent here; a theorem mentioning one then
    /// fails the deep translation honestly.
    deep: KernelAcl2Session,
    deep_cache: Mutex<FactCache>,
}

impl Acl2Session {
    /// Build a session over the process-global kernel theories, with no
    /// definitions and no theorems.
    pub fn new() -> Result<Self, Acl2Error> {
        let env = shadow_env().map_err(kernel_err)?;
        let cache = shadow_cache(&env).map_err(kernel_err)?;
        Ok(Acl2Session {
            defs: Defs::new(),
            admissions: BTreeMap::new(),
            definitions: BTreeMap::new(),
            hol_definitions: BTreeMap::new(),
            operational: HostSession::new(SurfaceDialect::Acl2Core, FUEL as usize),
            thms: BTreeMap::new(),
            sem0: LispSemantics::new()?,
            deep: KernelAcl2Session::new(env),
            deep_cache: Mutex::new(cache),
        })
    }

    /// The admitted `defun` dictionary.
    pub fn defs(&self) -> &Defs {
        &self.defs
    }

    pub fn admission(&self, name: &str) -> Option<&Acl2Admission> {
        self.admissions.get(name)
    }

    /// Source provenance and shared lowered operational definition.
    pub fn definition(&self, name: &str) -> Option<&Acl2Definition> {
        self.definitions.get(name)
    }

    /// The conservatively defined deep-HOL model, when this definition lies
    /// in the deep replay layer's currently supported template.
    pub fn hol_definition(&self, name: &str) -> Option<&Acl2HolDefinition> {
        self.hol_definitions.get(name)
    }

    /// Evaluate a closed ACL2 expression in the common partial Lisp machine
    /// and retain checked `MayEval` evidence.
    ///
    /// This deliberately proves only one finite execution. ACL2 admission
    /// still owes universal existence and uniqueness before totalization.
    pub fn operational_evidence(
        &self,
        form: &SExpr,
    ) -> Result<RuntimeEvaluation<HostFrontendRuntime>, Acl2Error> {
        let translated = self.translate(form, &[], None)?;
        let core = Frontend::new(SurfaceDialect::Acl2Core)
            .lower(&translated)
            .map_err(|error| Acl2Error::Malformed(error.to_string()))?;
        self.operational
            .evaluate_core_evidence(&core)
            .map_err(|error| Acl2Error::Malformed(format!("shared Lisp execution failed: {error}")))
    }

    /// Replay one concrete common-machine execution into the equational HOL
    /// backend used by this ACL2 generation.
    ///
    /// The returned theorem retains every definition equation it used as a
    /// hypothesis. This connects concrete ACL2 execution to kernel authority,
    /// but intentionally does not establish the universal existence and
    /// uniqueness required by [`covalence_kernel_lisp::ExecutionAdequacyReplay`].
    pub fn operational_hol_evidence(
        &self,
        form: &SExpr,
    ) -> Result<EquationalHostMayEvalEvidence, Acl2Error> {
        let evaluation = self.operational_evidence(form)?;
        LispSemantics::with_defs(self.defs.clone())?
            .transport_may_eval(&evaluation)
            .map_err(Acl2Error::Eval)
    }

    /// A proved `defthm` by name — the genuine kernel theorem (its hypotheses
    /// are the `defun` equations the proof used; empty for pure-arithmetic
    /// goals and for everything on the certificate path).
    pub fn theorem(&self, name: &str) -> Option<&Thm> {
        self.thms.get(name).map(|t| &t.thm)
    }

    /// A proved `defthm` by name, with its provenance: the theorem plus
    /// *which path* proved it (the reified [`Acl2Proof::Certificate`], or
    /// the [`Acl2Proof::Reduction`] fallback).
    pub fn theorem_entry(&self, name: &str) -> Option<&Acl2Theorem> {
        self.thms.get(name)
    }

    /// The checked deep ACL2 environment against which induction lemmas can
    /// be constructed.
    ///
    /// This is a deliberately ACL2-facing seam: reusable law packs such as
    /// ACL2-COUNT build genuine [`Fact`]s here, then register them with
    /// [`add_induction_lemma`](Self::add_induction_lemma). Merely constructing
    /// or registering a fact does not make a theorem authoritative.
    pub fn induction_env(&self) -> &Acl2Env {
        self.deep.env()
    }

    /// Add a caller-supplied derived fact as an induction/simplification hint
    /// for the current deep-environment generation.
    ///
    /// Registration is untrusted. It first checks that the theorem is closed
    /// and states this generation's exact `Derivable` target; the
    /// simplifier's `add_lemma` path then replays every selected instance with
    /// checked `INST`/`MP`. A stale-generation, forged, or mismatched [`Fact`]
    /// therefore causes registration or proof failure, never theorem
    /// production.
    ///
    /// Admitting another deep `defun` intentionally discards the hint along
    /// with the rest of the per-generation cache. Facts contain derivations
    /// for one exact `Acl2Env`; a reusable law pack must rebuild them against
    /// [`induction_env`](Self::induction_env) after the definition world is
    /// established.
    pub fn add_induction_lemma(&self, lemma: Fact) -> Result<(), Acl2Error> {
        let target =
            ladder::derivable(self.deep.env(), &lemma.phi).map_err(|e| Acl2Error::Unprovable {
                name: "<lemma-registration>".into(),
                reason: format!("could not form the current generation's lemma target: {e}"),
            })?;
        if !lemma.thm.hyps().is_empty() || *lemma.thm.concl() != target {
            return Err(Acl2Error::Unprovable {
                name: "<lemma-registration>".into(),
                reason: "lemma theorem is not a closed derivation in the current ACL2 generation"
                    .into(),
            });
        }
        let cache = self.deep_cache.lock().map_err(|_| Acl2Error::Unprovable {
            name: "<lemma-registration>".into(),
            reason: "kernel induction cache lock was poisoned".into(),
        })?;
        cache.add_lemma(lemma);
        Ok(())
    }

    /// Parse → dispatch (event or expression) → render, for one cell of
    /// source. `defun` / `defthm` events return their name on success (the
    /// ACL2 convention); an expression returns its value, read off the
    /// backing theorem's RHS.
    pub fn eval_cell(&mut self, src: &str) -> Result<String, Acl2Error> {
        let form = read_one(src.trim()).map_err(Acl2Error::Read)?;
        if let Some(name) = self.try_event(&form)? {
            return Ok(name);
        }
        let out = self.reduce(&form)?;
        Ok(self.render(&out))
    }

    /// Is this form an ACL2 **event** (`defun` / `defthm`, including the
    /// `defund` / `defthmd` rule-disable variants)? If so, admit it and
    /// return its name (the ACL2 convention), else `Ok(None)` — the caller
    /// evaluates the form as an expression. Rule enablement has no meaning
    /// in this slice, so the `d` variants share the same honest admission
    /// paths. This is the seam the `#lang acl2`
    /// [`session::Session`](crate::session::Session) dispatch uses.
    pub fn try_event(&mut self, form: &SExpr) -> Result<Option<String>, Acl2Error> {
        if let SExpr::List(items) = form {
            match items.first().and_then(SExpr::as_symbol) {
                Some("defun" | "defund") => return self.admit_defun(items).map(Some),
                Some("defthm" | "defthmd") => return self.admit_defthm(items).map(Some),
                _ => {}
            }
        }
        Ok(None)
    }

    /// Drop all session state (the `defun` dictionary and the `defthm`
    /// table) — infallible, used by the `#lang` switch reset.
    pub fn reset(&mut self) {
        self.defs = Defs::new();
        self.admissions = BTreeMap::new();
        self.definitions = BTreeMap::new();
        self.hol_definitions = BTreeMap::new();
        self.operational = HostSession::new(SurfaceDialect::Acl2Core, FUEL as usize);
        self.thms = BTreeMap::new();
        if let Ok(env) = shadow_env() {
            let cache = shadow_cache(&env).unwrap_or_default();
            self.deep = KernelAcl2Session::new(env);
            self.deep_cache = Mutex::new(cache);
        }
    }

    // ------------------------------------------------------------------
    // Expression evaluation
    // ------------------------------------------------------------------

    /// Evaluate one ACL2 expression to an [`Acl2Outcome`]: translate the
    /// ACL2 spellings and drive the value semantics (which carries the
    /// integer backend). A top-level non-arithmetic `equal` additionally
    /// gets the structural fallback ([`reduce_equal`](Self::reduce_equal)).
    pub fn reduce(&self, form: &SExpr) -> Result<Acl2Outcome, Acl2Error> {
        if let SExpr::List(items) = form
            && items.len() == 3
            && items[0].as_symbol() == Some("equal")
            && !is_int_form(&items[1])
            && !is_int_form(&items[2])
        {
            return self.reduce_equal(&items[1], &items[2]);
        }
        let translated = self.translate(form, &[], None)?;
        self.reduce_value(&translated)
    }

    /// Drive a (translated) form through the value semantics to a normal
    /// form, fuel-bounded, packaging the composite theorem.
    fn reduce_value(&self, form: &SExpr) -> Result<Acl2Outcome, Acl2Error> {
        let sem = LispSemantics::with_defs(self.defs.clone())?;
        let core = Frontend::new(SurfaceDialect::Acl2Core)
            .lower(form)
            .map_err(|error| Acl2Error::Malformed(error.to_string()))?;
        let term = sem.compile_core(&core)?;
        let mut red: Reduction<LispRepr, LispSemantics> = Reduction::start(term);
        RunToValue.drive(&sem, &mut red, Fuel::steps(FUEL))?;
        let status = red.status();
        let (value, composite) = red.into_parts();
        let kind = match sem.value_kind(&value) {
            Some(ValueKind::Data) => Acl2ValueKind::Data,
            Some(ValueKind::Bool) => Acl2ValueKind::Bool,
            Some(ValueKind::Int) => Acl2ValueKind::Int,
            None => {
                return Err(Acl2Error::Eval(HolError::Stuck(format!(
                    "did not reach a value in {FUEL} steps (status {status:?}) — \
                     the definition may not terminate"
                ))));
            }
        };
        let thm = match composite {
            Some(t) => t,
            None => Thm::refl(value.clone()).map_err(kernel_err)?,
        };
        Ok(Acl2Outcome { value, thm, kind })
    }

    /// `(equal a b)` outside arithmetic: first try the `eq?` reduction (which
    /// genuinely decides atom (dis)equality); if that gets stuck (composite
    /// operands), fall back to reducing both operands and — **only when the
    /// value terms are syntactically identical** — minting
    /// `hyps ⊢ (a = b) = T` by `trans`/`sym` + `eqt_intro`. Distinct
    /// composite values are a clean error (deciding their *dis*equality needs
    /// the `scons` discrimination laws — future work, see the generated open-work index).
    fn reduce_equal(&self, a: &SExpr, b: &SExpr) -> Result<Acl2Outcome, Acl2Error> {
        let eq_form = SExpr::List(vec![
            SExpr::Atom(Atom::Symbol("eq?".into())),
            self.translate(a, &[], None)?,
            self.translate(b, &[], None)?,
        ]);
        match self.reduce_value(&eq_form) {
            Ok(out) => Ok(out),
            Err(first) => self.reduce_equal_structural(a, b).map_err(|e| {
                // Prefer the structural path's message when it is the honest
                // "cannot decide" one; else surface the original failure.
                match e {
                    Acl2Error::Malformed(_) => e,
                    _ => first,
                }
            }),
        }
    }

    /// The structural-identity `equal` fallback (values must coincide).
    fn reduce_equal_structural(&self, a: &SExpr, b: &SExpr) -> Result<Acl2Outcome, Acl2Error> {
        let oa = self.reduce_value(&self.translate(a, &[], None)?)?;
        let ob = self.reduce_value(&self.translate(b, &[], None)?)?;
        if oa.value != ob.value {
            return Err(Acl2Error::Malformed(
                "equal: cannot decide disequality of composite values in this slice \
                 (only atom disequality is decidable — `scons` discrimination laws \
                 are future work)"
                    .into(),
            ));
        }
        // oa.thm : H₁ ⊢ a = v ; ob.thm : H₂ ⊢ b = v ; so H₁∪H₂ ⊢ a = b, and
        // eqt_intro gives H₁∪H₂ ⊢ (a = b) = T.
        let eq = oa
            .thm
            .trans(ob.thm.sym().map_err(kernel_err)?)
            .map_err(kernel_err)?;
        let thm = eq.eqt_intro().map_err(kernel_err)?;
        let value = rhs_of(&thm)?;
        Ok(Acl2Outcome {
            value,
            thm,
            kind: Acl2ValueKind::Bool,
        })
    }

    /// Render an outcome's value — **off the theorem's RHS only**.
    pub fn render(&self, out: &Acl2Outcome) -> String {
        match out.kind {
            Acl2ValueKind::Bool => match as_bool(&out.value) {
                Some(true) => "t".into(),
                Some(false) => "nil".into(),
                None => format!("{}", out.value),
            },
            Acl2ValueKind::Int => match as_int(&out.value) {
                Some(n) => n.to_string(),
                None => format!("{}", out.value),
            },
            Acl2ValueKind::Data => self.render_data(&out.value),
        }
    }

    /// A `sexpr` datum → Lisp text (mirrors `session::Session::render_data`).
    fn render_data(&self, v: &Term) -> String {
        if self.sem0.is_snil(v) {
            return "()".into();
        }
        if let Some(bytes) = self.sem0.atom_bytes(v) {
            return String::from_utf8_lossy(&bytes).into_owned();
        }
        if self.sem0.as_scons(v).is_some() {
            let mut out = String::from("(");
            let mut cur = v.clone();
            let mut first = true;
            while let Some((h, t)) = self.sem0.as_scons(&cur) {
                if !first {
                    out.push(' ');
                }
                first = false;
                out.push_str(&self.render_data(&h));
                if self.sem0.is_snil(&t) {
                    break;
                }
                if self.sem0.as_scons(&t).is_none() {
                    out.push_str(" . ");
                    out.push_str(&self.render_data(&t));
                    break;
                }
                cur = t;
            }
            out.push(')');
            return out;
        }
        format!("{v}")
    }

    // ------------------------------------------------------------------
    // defun — admissibility + install
    // ------------------------------------------------------------------

    /// `(defun name (params) [doc-string] [declare …]* body)`: run the
    /// admissibility check, then install the definition as an assumed
    /// equation (never an axiom).
    ///
    /// ACL2 declarations (most commonly `(declare (xargs …))`) guide ACL2's
    /// admission machinery but are not executable body forms.  This dialect
    /// records no claim that it checked those hints: it ignores them and
    /// applies its own, explicitly weaker structural-recursion check to the
    /// sole body form.
    fn admit_defun(&mut self, items: &[SExpr]) -> Result<String, Acl2Error> {
        if items.len() < 4 {
            return Err(Acl2Error::Malformed(
                "defun: expected (defun name (params) [doc-string] [declare ...]* body)".into(),
            ));
        }
        let name = items[1]
            .as_symbol()
            .ok_or_else(|| Acl2Error::Malformed("defun: name is not a symbol".into()))?
            .to_string();
        let inadmissible = |reason: String| Acl2Error::Inadmissible {
            name: name.clone(),
            reason,
        };
        if reserved_head(&name).is_some() || matches!(name.as_str(), "t" | "nil") {
            return Err(inadmissible("the name is a reserved primitive".into()));
        }
        let params = param_names(&items[2]).map_err(&inadmissible)?;
        let body = defun_body(items).map_err(Acl2Error::Malformed)?;
        let translated = self.translate(body, &params, Some(&name))?;
        let core_body = Frontend::new(SurfaceDialect::Acl2Core)
            .lower(&translated)
            .map_err(|error| inadmissible(error.to_string()))?;
        let definition = Acl2Definition::new(
            LispDefinition::fixed(name.clone(), params.clone(), core_body),
            body.clone(),
        );
        let admission = AdmissionPolicy::inspect(self, &definition).map_err(&inadmissible)?;
        let mut operational = self.operational.clone();
        operational
            .define_core(definition.core.clone())
            .map_err(|error| {
                inadmissible(format!(
                    "shared partial Lisp installation failed after admission: {error}"
                ))
            })?;
        self.install(&definition.core)?;
        self.operational = operational;
        self.try_admit_deep_defun(&definition, &admission);
        self.definitions.insert(name.clone(), definition);
        self.admissions.insert(name.clone(), admission);
        Ok(name)
    }

    /// Mirror a surface definition into the conservative kernel ACL2
    /// generation when it lies in that generation's exact S4 template.
    /// Failure is intentionally non-fatal: the value semantics supports a
    /// wider language, while any later deep theorem mentioning the omitted
    /// function will be rejected during translation.
    fn try_admit_deep_defun(&mut self, definition: &Acl2Definition, admission: &Acl2Admission) {
        if let Ok(evidence) =
            Acl2HolReplay::new(self.deep.env()).replay_termination(definition, admission)
        {
            self.hol_definitions
                .insert(definition.core.name.clone(), evidence.definition);
            let cache = shadow_cache(&evidence.environment).unwrap_or_default();
            self.deep = KernelAcl2Session::new(evidence.environment);
            self.deep_cache = Mutex::new(cache);
        }
    }

    /// The syntactic admissibility check (see the module docs for the exact
    /// criterion). Errors carry a human-readable reason.
    fn check_admissible(
        &self,
        name: &str,
        params: &[String],
        body: &SExpr,
    ) -> Result<Acl2Admission, String> {
        let mut calls: Vec<&[SExpr]> = Vec::new();
        self.check_body(name, params, body, &mut calls)?;
        if calls.is_empty() {
            return Ok(Acl2Admission {
                recursive_calls: 0,
                decreasing_parameter: None,
            });
        }
        let decreasing_parameter = (0..params.len()).find(|&i| {
            calls
                .iter()
                .all(|args| is_proper_projection(&args[i], &params[i]))
        });
        if let Some(decreasing_parameter) = decreasing_parameter {
            Ok(Acl2Admission {
                recursive_calls: calls.len(),
                decreasing_parameter: Some(decreasing_parameter),
            })
        } else {
            Err(format!(
                "not structurally recursive: no formal position decreases — every \
                 recursive call to `{name}` must pass a car/cdr-projection of the \
                 same formal in that formal's position (general measures / \
                 termination proofs are future work)"
            ))
        }
    }

    /// Walk a `defun` body: validate every head and atom, collecting the
    /// argument lists of recursive calls.
    fn check_body<'a>(
        &self,
        name: &str,
        params: &[String],
        e: &'a SExpr,
        calls: &mut Vec<&'a [SExpr]>,
    ) -> Result<(), String> {
        match e {
            SExpr::Atom(Atom::Str { .. }) => Ok(()),
            SExpr::Atom(Atom::Symbol(s)) => {
                let s = s.as_str();
                if s == "t"
                    || s == "nil"
                    || params.iter().any(|p| p == s)
                    || s.parse::<Int>().is_ok()
                {
                    Ok(())
                } else {
                    Err(format!("unbound variable `{s}` in the body"))
                }
            }
            SExpr::List(items) => {
                let Some((head, args)) = items.split_first() else {
                    return Err("empty application `()`".into());
                };
                let Some(h) = head.as_symbol() else {
                    return Err("application head is not a symbol (no higher-order \
                                forms in the ACL2 slice)"
                        .into());
                };
                if h == "quote" {
                    return if args.len() == 1 {
                        Ok(()) // quoted data: no code inside
                    } else {
                        Err("quote takes exactly one argument".into())
                    };
                }
                if let Some(ops) = composed_accessor(h) {
                    if args.len() != 1 {
                        return Err(format!("`{h}` expects 1 argument, got {}", args.len()));
                    }
                    self.check_body(name, params, &args[0], calls)?;
                    // The expansion is a car/cdr chain, so no additional
                    // callable heads need validation.
                    debug_assert!(!ops.is_empty());
                    return Ok(());
                }
                let expected = if let Some(arity) = int_op_arity(h) {
                    arity
                } else if let Some(arity) = reserved_head(h) {
                    arity
                } else if h == name {
                    calls.push(args);
                    params.len()
                } else if let Some(def) = self.defs.get(h) {
                    def.params.len()
                } else {
                    return Err(format!(
                        "call to undefined function `{h}` — ACL2 requires \
                         definition before use"
                    ));
                };
                if args.len() != expected {
                    return Err(format!(
                        "`{h}` expects {expected} argument(s), got {}",
                        args.len()
                    ));
                }
                for a in args {
                    self.check_body(name, params, a, calls)?;
                }
                Ok(())
            }
        }
    }

    /// Install an admissible definition: compile the (translated) body with
    /// the recursive head pre-registered, and enter `{f = λ…} ⊢ f = λ…` into
    /// the dictionary. Return-type disambiguation extends
    /// `session::Session::install`'s trick: try `bool` (predicates), then
    /// `sexpr` (data functions), then `int` (integer-valued functions, e.g.
    /// `len`); the wrong choices fail to type-check.
    fn install(
        &mut self,
        definition: &LispDefinition<String, FrontendExpr>,
    ) -> Result<(), Acl2Error> {
        self.defs = install_core_definition(&self.defs, definition).map_err(|error| {
            Acl2Error::Inadmissible {
                name: definition.name.clone(),
                reason: error.to_string(),
            }
        })?;
        Ok(())
    }

    // ------------------------------------------------------------------
    // defthm — ground decidable goals only
    // ------------------------------------------------------------------

    /// `(defthm name goal)`: prove `goal`, or reject. A ground
    /// `(equal LHS RHS)` over the reified fragment goes **through the
    /// S0–S3 ladder** ([`prove_certified`](Self::prove_certified)); every
    /// other goal takes the reduction fallback
    /// ([`prove_ground`](Self::prove_ground)). Only **ground** goals are
    /// accepted; a goal with free variables is a universally quantified
    /// claim this slice cannot prove (induction is not implemented) and is
    /// rejected saying so.
    fn admit_defthm(&mut self, items: &[SExpr]) -> Result<String, Acl2Error> {
        if items.len() != 3 {
            return Err(Acl2Error::Malformed(
                "defthm: expected (defthm name goal)".into(),
            ));
        }
        let name = items[1]
            .as_symbol()
            .ok_or_else(|| Acl2Error::Malformed("defthm: name is not a symbol".into()))?
            .to_string();
        let mut vars = Vec::new();
        self.scan_free(&items[2], &mut vars);
        let entry = if !vars.is_empty() {
            self.prove_inductive(&name, &items[2])?
        } else {
            match self.prove_certified(&items[2])? {
                Some(entry) => entry,
                None => Acl2Theorem {
                    thm: self.prove_ground(&name, &items[2])?,
                    proof: Acl2Proof::Reduction,
                },
            }
        };
        self.thms.insert(name.clone(), entry);
        Ok(name)
    }

    /// Prove an open surface theorem through the generic, derivation-emitting
    /// S6 premise builder. The returned theorem is the transported deep-model
    /// statement, with no assumptions.
    fn prove_inductive(&self, name: &str, goal: &SExpr) -> Result<Acl2Theorem, Acl2Error> {
        let tm = &*self.deep.env().tm;
        let phi = deep_encode(tm, goal, &[]).map_err(|reason| Acl2Error::Unprovable {
            name: name.to_string(),
            reason: format!("kernel induction path cannot encode goal: {reason}"),
        })?;
        let cache = self.deep_cache.lock().map_err(|_| Acl2Error::Unprovable {
            name: name.to_string(),
            reason: "kernel induction cache lock was poisoned".into(),
        })?;
        let proof =
            prove_by_induction(&self.deep, &cache, &phi, &IndConfig::default()).map_err(|e| {
                Acl2Error::Unprovable {
                    name: name.to_string(),
                    reason: format!("kernel induction failed: {e}"),
                }
            })?;
        Ok(Acl2Theorem {
            thm: proof.transported,
            proof: Acl2Proof::Induction {
                derivation: proof.derivation,
                variable: proof.var,
            },
        })
    }

    /// Try the **reified-certificate path** for a ground `(equal LHS RHS)`
    /// goal over the supported fragment: build the hypothesis-free
    /// `⊢ Derivable_ACL2 ⌜goal⌝` certificate bottom-up (the `derive_*`
    /// constructors of [`covalence_init::init::acl2::derivable`]), project
    /// it through the soundness metatheorem, and transport the result to
    /// the base-HOL model equation. `Ok(None)` = out of fragment, or the
    /// two sides compute to *different* model values — the caller falls
    /// back to the reduction path, which proves, honestly refutes, or
    /// rejects. Nothing is ever minted on a failed path.
    fn prove_certified(&self, goal: &SExpr) -> Result<Option<Acl2Theorem>, Acl2Error> {
        let SExpr::List(items) = goal else {
            return Ok(None);
        };
        if items.len() != 3
            || !matches!(items[0].as_symbol(), Some("equal") | Some("="))
            || !cert_fragment(&items[1])
            || !cert_fragment(&items[2])
        {
            return Ok(None);
        }
        // The engine (env + the soundness metatheorem) is only built once a
        // goal actually lies in the fragment — `soundness` is not cheap.
        let eng = cert_engine()?;
        let Some(l) = eng.eval_cert(&items[1])? else {
            return Ok(None);
        };
        let Some(r) = eng.eval_cert(&items[2])? else {
            return Ok(None);
        };
        if l.value != r.value {
            return Ok(None); // not certifiably equal — fall back (refutation)
        }
        let tm = eng.tm();
        let qv = tm.quote(&l.value).map_err(kernel_err)?;
        // Splice the per-side derivations at the shared quoted value:
        //   l.der : ⊢ D ⌜(EQUAL encL 'v)⌝,  r.der : ⊢ D ⌜(EQUAL encR 'v)⌝
        //   ⟹ (symm, trans)  ⊢ D ⌜(EQUAL encL encR)⌝.
        let der = if r.enc == qv {
            l.der.clone() // RHS is the quoted value itself: l.der IS the goal
        } else {
            let r_sym = eng.symm_cert(&r.enc, &qv, r.der)?; // D ⌜(EQUAL 'v encR)⌝
            eng.trans_cert(&l.enc, &qv, &r.enc, l.der, r_sym)?
        };
        let phi = tm.mk_equal(&l.enc, &r.enc).map_err(kernel_err)?;
        let projected = ladder::project_with(&eng.snd, &phi, der.clone()).map_err(kernel_err)?;
        let thm = ladder::transport_equal(&eng.env, &projected).map_err(kernel_err)?;
        Ok(Some(Acl2Theorem {
            thm,
            proof: Acl2Proof::Certificate { derivation: der },
        }))
    }

    /// Prove a ground goal: reduce it to a boolean literal by the kernel and
    /// conclude `hyps ⊢ goal` when (and only when) it lands on `T`.
    fn prove_ground(&self, name: &str, goal: &SExpr) -> Result<Thm, Acl2Error> {
        let unprovable = |reason: String| Acl2Error::Unprovable {
            name: name.to_string(),
            reason,
        };
        // Groundness first, for the honest rejection message.
        let mut vars = Vec::new();
        self.scan_free(goal, &mut vars);
        if !vars.is_empty() {
            vars.sort();
            vars.dedup();
            return Err(unprovable(format!(
                "the goal has free variables ({}) — a universally quantified claim \
                 needs induction, which this slice does not implement; only ground \
                 decidable goals are accepted",
                vars.join(", ")
            )));
        }
        let out = self.reduce(goal).map_err(|e| match e {
            Acl2Error::Unprovable { .. } | Acl2Error::Inadmissible { .. } => e,
            other => unprovable(format!("the goal did not reduce: {other}")),
        })?;
        if out.kind == Acl2ValueKind::Data || out.kind == Acl2ValueKind::Int {
            return Err(unprovable(
                "the goal is not a boolean form (it reduces to data, not t/nil)".into(),
            ));
        }
        match as_bool(&out.value) {
            // out.thm : hyps ⊢ goal = T ; eqt_elim : hyps ⊢ goal.
            Some(true) => out.thm.eqt_elim().map_err(kernel_err),
            Some(false) => Err(unprovable(
                "the goal is FALSE: it reduces to nil (refuted by computation)".into(),
            )),
            None => Err(unprovable(
                "the goal did not decide to a boolean literal".into(),
            )),
        }
    }

    /// Collect the free variables of a form: non-`t`/`nil`, non-numeral
    /// symbols in operand position, outside `quote` (function heads are
    /// validated separately by [`translate`](Self::translate)).
    fn scan_free(&self, e: &SExpr, vars: &mut Vec<String>) {
        match e {
            SExpr::Atom(Atom::Str { .. }) => {}
            SExpr::Atom(Atom::Symbol(s)) => {
                let s = s.as_str();
                if s != "t" && s != "nil" && s.parse::<Int>().is_err() {
                    vars.push(s.to_string());
                }
            }
            SExpr::List(items) => {
                if items.first().and_then(SExpr::as_symbol) == Some("quote") {
                    return;
                }
                for a in items.iter().skip(1) {
                    self.scan_free(a, vars);
                }
            }
        }
    }

    // ------------------------------------------------------------------
    // Surface translation (ACL2 spellings → the value-semantics dialect)
    // ------------------------------------------------------------------

    /// Rewrite an ACL2 form into the value-semantics dialect (`equal` →
    /// integer `=` or `eq?`, `endp` → `null?`, `atom` → `atom?`, `zp n` →
    /// `(<= n 0)`, `natp n` → `(<= 0 n)`), validating heads, arities, and
    /// variable scope as it goes. `vars` are the in-scope formals; `self_name`
    /// is the function being defined (its recursive calls are legal).
    fn translate(
        &self,
        e: &SExpr,
        vars: &[String],
        self_name: Option<&str>,
    ) -> Result<SExpr, Acl2Error> {
        match e {
            SExpr::Atom(Atom::Str { .. }) => Ok(e.clone()),
            SExpr::Atom(Atom::Symbol(s)) => {
                let s = s.as_str();
                if s == "t" || s == "nil" || vars.iter().any(|p| p == s) || s.parse::<Int>().is_ok()
                {
                    Ok(e.clone())
                } else {
                    Err(Acl2Error::Malformed(format!("unbound variable `{s}`")))
                }
            }
            SExpr::List(items) => {
                let Some((head, args)) = items.split_first() else {
                    return Err(Acl2Error::Malformed("empty application `()`".into()));
                };
                let Some(h) = head.as_symbol() else {
                    return Err(Acl2Error::Malformed(
                        "application head is not a symbol (no higher-order forms in \
                         the ACL2 slice)"
                            .into(),
                    ));
                };
                if h == "quote" {
                    if args.len() != 1 {
                        return Err(Acl2Error::Malformed(
                            "quote takes exactly one argument".into(),
                        ));
                    }
                    return Ok(e.clone()); // data — no translation inside
                }
                if h == "cond" {
                    return Err(Acl2Error::Malformed(
                        "the ACL2 slice uses ternary `if`, not `cond`".into(),
                    ));
                }
                if let Some(ops) = composed_accessor(h) {
                    if args.len() != 1 {
                        return Err(Acl2Error::Malformed(format!(
                            "`{h}` expects 1 argument, got {}",
                            args.len()
                        )));
                    }
                    let mut out = self.translate(&args[0], vars, self_name)?;
                    // ACL2 names operations from the inside out: CDDR is
                    // (cdr (cdr x)), CADR is (car (cdr x)).
                    for op in ops.iter().rev() {
                        out = SExpr::List(vec![
                            SExpr::Atom(Atom::Symbol(
                                if *op == b'a' { "car" } else { "cdr" }.into(),
                            )),
                            out,
                        ]);
                    }
                    return Ok(out);
                }
                // `zp n` / `natp n` — integer sugar for `n ≤ 0` / `0 ≤ n`
                // (on `int`-typed terms `integerp` is `t` by typing).
                if h == "zp" || h == "natp" {
                    if args.len() != 1 {
                        return Err(Acl2Error::Malformed(format!(
                            "`{h}` expects 1 argument, got {}",
                            args.len()
                        )));
                    }
                    let n = self.translate(&args[0], vars, self_name)?;
                    let zero = SExpr::Atom(Atom::Symbol("0".into()));
                    let (a, b) = if h == "zp" { (n, zero) } else { (zero, n) };
                    return Ok(SExpr::List(vec![
                        SExpr::Atom(Atom::Symbol("<=".into())),
                        a,
                        b,
                    ]));
                }
                let (new_head, expected) = if let Some(arity) = int_op_arity(h) {
                    (h.to_string(), arity)
                } else if let Some(arity) = reserved_head(h) {
                    let renamed = match h {
                        // `equal` is generic in ACL2: route it to integer `=`
                        // when either side is syntactically arithmetic, else
                        // to the sexpr `eq?` (atoms, plus the structural
                        // fallback in `reduce_equal`).
                        "equal" if args.iter().any(is_int_form) => "=",
                        "equal" => "eq?",
                        "endp" => "null?",
                        "atom" => "atom?",
                        other => other,
                    };
                    (renamed.to_string(), arity)
                } else if Some(h) == self_name {
                    (h.to_string(), vars.len())
                } else if let Some(def) = self.defs.get(h) {
                    (h.to_string(), def.params.len())
                } else {
                    return Err(Acl2Error::Malformed(format!(
                        "call to undefined function `{h}` — ACL2 requires definition \
                         before use"
                    )));
                };
                if args.len() != expected {
                    return Err(Acl2Error::Malformed(format!(
                        "`{h}` expects {expected} argument(s), got {}",
                        args.len()
                    )));
                }
                // Kernel integers are typed `int` terms, not sexpr data — an
                // arithmetic form in a list-typed position is rejected with a
                // clear message (instead of leaving a stuck ill-typed term).
                if sexpr_positions(&new_head)
                    && let Some(bad) = args.iter().find(|a| is_int_form(a))
                {
                    return Err(Acl2Error::Malformed(format!(
                        "integer `{bad:?}` in a list position of `{h}` — kernel \
                         integers are typed `int` terms, not sexpr data; mixed \
                         integer/list structure is not supported in this slice"
                    )));
                }
                let mut out = Vec::with_capacity(items.len());
                out.push(SExpr::Atom(Atom::Symbol(new_head.into())));
                for a in args {
                    out.push(self.translate(a, vars, self_name)?);
                }
                Ok(SExpr::List(out))
            }
        }
    }
}

impl AdmissionPolicy<Acl2Definition> for Acl2Session {
    type Certificate = Acl2Admission;
    type Error = String;

    fn inspect(&self, definition: &Acl2Definition) -> Result<Self::Certificate, Self::Error> {
        self.check_admissible(
            &definition.core.name,
            &definition.core.parameters,
            &definition.source_body,
        )
    }
}

// ============================================================================
// The reified-certificate engine (defthm through the S0–S3 ladder)
// ============================================================================

/// Map a **surface head to its PrimRow spelling** (per
/// [`covalence_init::init::acl2::term::Terms`]'s encoders): the reified
/// fragment. `-`, `*`, `<=`, `zp`, `natp`, `atom`, `endp`, and `if` are
/// deliberately absent: `atom`/`endp`/`<=`/binary-`-` are defuns/macros
/// (not table rows), `if` is a special form, and `BINARY-*`/`UNARY--`/`<`
/// have no *public* ground model-folding law yet (only `Prims::plus_lit`
/// is exported) — all of these take the honest reduction fallback.
fn row_spelling(head: &str) -> Option<&'static str> {
    match head {
        "car" => Some("CAR"),
        "cdr" => Some("CDR"),
        "cons" => Some("CONS"),
        "consp" => Some("CONSP"),
        "equal" | "=" => Some("EQUAL"),
        "+" => Some("BINARY-+"),
        _ => None,
    }
}

/// Cheap syntactic pre-check: is this form in the certificate fragment
/// (quoted data, integer literals, `t`/`nil`, applications of the mapped
/// heads)? Keeps the expensive engine build off goals that can never take
/// the certificate path. (The engine can still return `None` later — e.g.
/// arithmetic on non-literal values.)
fn cert_fragment(e: &SExpr) -> bool {
    match e {
        SExpr::Atom(Atom::Symbol(s)) => {
            let s = s.as_str();
            s == "t" || s == "nil" || s.parse::<Int>().is_ok()
        }
        SExpr::Atom(_) => false,
        SExpr::List(items) => match items.split_first() {
            Some((h, args)) => match h.as_symbol() {
                Some("quote") => args.len() == 1 && quotable(&args[0]),
                Some(h) => row_spelling(h).is_some() && args.iter().all(cert_fragment),
                None => false,
            },
            None => false,
        },
    }
}

/// Is this quoted datum encodable as a carrier value (symbols, numerals,
/// proper lists — no string atoms)?
fn quotable(d: &SExpr) -> bool {
    match d {
        SExpr::Atom(Atom::Symbol(_)) => true,
        SExpr::Atom(_) => false,
        SExpr::List(items) => items.iter().all(quotable),
    }
}

/// A certificate-evaluated subterm: its pseudo-term encoding `enc`, its
/// canonical model value, and the derivation
/// `⊢ Derivable_ACL2 ⌜(EQUAL enc 'value)⌝`.
struct CertVal {
    enc: Term,
    value: Term,
    der: Thm,
}

/// The certificate engine: the ground S3 environment plus its (expensive,
/// proved-once-per-process) soundness metatheorem
/// `⊢ ∀A. Derivable_ACL2 A ⟹ (∀σ. ¬(eval A σ = anil))`.
struct CertEngine {
    env: Acl2Env,
    snd: Thm,
}

/// The process-global certificate engine (kernel theories are
/// process-global, so this is shared across sessions like the S3 tests'
/// own `LazyLock` soundness).
fn cert_engine() -> Result<&'static CertEngine, Acl2Error> {
    static ENGINE: LazyLock<std::result::Result<CertEngine, String>> = LazyLock::new(|| {
        let env = ladder::ground_env().map_err(|e| e.to_string())?;
        let snd = ladder::soundness(&env).map_err(|e| e.to_string())?;
        Ok(CertEngine { env, snd })
    });
    ENGINE
        .as_ref()
        .map_err(|e| kernel_err(format!("acl2 certificate engine failed to build: {e}")))
}

impl CertEngine {
    fn tm(&self) -> &Terms {
        &self.env.tm
    }

    /// INST an env axiom at a ground substitution and return the folded
    /// derivation (axiom → `derive_inst_ground`).
    fn inst_axiom(&self, name: &str, binds: &[(&[u8], Term)]) -> Result<Thm, Acl2Error> {
        let (_, ax) = self.env.axiom(name).map_err(kernel_err)?;
        let ax = ax.clone();
        let d_ax = ladder::derive_axiom(&self.env, name).map_err(kernel_err)?;
        let s = ladder::finite_sigma(self.tm(), binds).map_err(kernel_err)?;
        ladder::derive_inst_ground(&self.env, &ax, &s, d_ax).map_err(kernel_err)
    }

    /// `⊢ D ⌜(EQUAL 'v 'v)⌝` — `equal-refl` INSTed at `X ↦ 'v`.
    fn refl_cert(&self, qv: &Term) -> Result<Thm, Acl2Error> {
        self.inst_axiom("equal-refl", &[(b"X", qv.clone())])
    }

    /// From `der_ab : ⊢ D ⌜(EQUAL a b)⌝` derive `⊢ D ⌜(EQUAL b a)⌝` —
    /// `equal-symm` INSTed at `{X ↦ a, Y ↦ b}`, then MP.
    fn symm_cert(&self, a: &Term, b: &Term, der_ab: Thm) -> Result<Thm, Acl2Error> {
        let tm = self.tm();
        let d_inst = self.inst_axiom("equal-symm", &[(b"X", a.clone()), (b"Y", b.clone())])?;
        let eq_ab = tm.mk_equal(a, b).map_err(kernel_err)?;
        let eq_ba = tm.mk_equal(b, a).map_err(kernel_err)?;
        ladder::derive_mp(&self.env, &eq_ab, &eq_ba, d_inst, der_ab).map_err(kernel_err)
    }

    /// From `der_ab : ⊢ D ⌜(EQUAL a b)⌝` and `der_bc : ⊢ D ⌜(EQUAL b c)⌝`
    /// derive `⊢ D ⌜(EQUAL a c)⌝` — `equal-trans` INSTed at
    /// `{X ↦ a, Y ↦ b, Z ↦ c}`, then MP twice.
    fn trans_cert(
        &self,
        a: &Term,
        b: &Term,
        c: &Term,
        der_ab: Thm,
        der_bc: Thm,
    ) -> Result<Thm, Acl2Error> {
        let tm = self.tm();
        let d_inst = self.inst_axiom(
            "equal-trans",
            &[(b"X", a.clone()), (b"Y", b.clone()), (b"Z", c.clone())],
        )?;
        let eq_ab = tm.mk_equal(a, b).map_err(kernel_err)?;
        let eq_bc = tm.mk_equal(b, c).map_err(kernel_err)?;
        let eq_ac = tm.mk_equal(a, c).map_err(kernel_err)?;
        let inner = tm.mk_implies(&eq_bc, &eq_ac).map_err(kernel_err)?;
        let step =
            ladder::derive_mp(&self.env, &eq_ab, &inner, d_inst, der_ab).map_err(kernel_err)?;
        ladder::derive_mp(&self.env, &eq_bc, &eq_ac, step, der_bc).map_err(kernel_err)
    }

    /// A leaf value `v`: encoding `'v`, derivation
    /// `⊢ D ⌜(EQUAL 'v 'v)⌝` (the reflexivity certificate).
    fn leaf(&self, v: Term) -> Result<CertVal, Acl2Error> {
        let qv = self.tm().quote(&v).map_err(kernel_err)?;
        let der = self.refl_cert(&qv)?;
        Ok(CertVal {
            enc: qv,
            value: v,
            der,
        })
    }

    /// A quoted datum → its carrier value: numerals → `aint`, `nil`/`t`
    /// (any case) → the canonical booleans `anil` / `t` (never
    /// `asym "NIL"` — the representation contract), other symbols →
    /// `asym` of the bytes as written, proper lists → `acons` chains.
    fn datum(&self, d: &SExpr) -> Result<Option<Term>, Acl2Error> {
        let tm = self.tm();
        match d {
            SExpr::Atom(Atom::Symbol(s)) => {
                let s = s.as_str();
                let v = if let Ok(n) = s.parse::<Int>() {
                    tm.th.aint_at(&mk_int(n)).map_err(kernel_err)?
                } else if s.eq_ignore_ascii_case("nil") {
                    tm.th.nil.clone()
                } else if s.eq_ignore_ascii_case("t") {
                    tm.pr.t.clone()
                } else {
                    tm.sym(s.as_bytes()).map_err(kernel_err)?
                };
                Ok(Some(v))
            }
            SExpr::Atom(_) => Ok(None),
            SExpr::List(items) => {
                let mut acc = tm.th.nil.clone();
                for it in items.iter().rev() {
                    let Some(v) = self.datum(it)? else {
                        return Ok(None);
                    };
                    acc = tm
                        .th
                        .cons
                        .clone()
                        .apply(v)
                        .map_err(kernel_err)?
                        .apply(acc)
                        .map_err(kernel_err)?;
                }
                Ok(Some(acc))
            }
        }
    }

    /// Certificate-evaluate a surface form bottom-up: encode it as an S2
    /// pseudo-term, compute its canonical model value, and build the
    /// derivation `⊢ D ⌜(EQUAL enc 'value)⌝` (leaves by `equal-refl`+INST;
    /// applications by congruence + the computation clause folded by an S1
    /// model law, spliced with `equal-trans`+MP). `Ok(None)` = out of
    /// fragment (free variable, unmapped head, or no folding law at these
    /// values).
    fn eval_cert(&self, e: &SExpr) -> Result<Option<CertVal>, Acl2Error> {
        let tm = self.tm();
        match e {
            SExpr::Atom(Atom::Symbol(s)) => {
                let s = s.as_str();
                let v = if let Ok(n) = s.parse::<Int>() {
                    tm.th.aint_at(&mk_int(n)).map_err(kernel_err)?
                } else if s == "t" {
                    tm.pr.t.clone()
                } else if s == "nil" {
                    tm.th.nil.clone()
                } else {
                    return Ok(None); // free variable — not ground
                };
                self.leaf(v).map(Some)
            }
            SExpr::Atom(_) => Ok(None),
            SExpr::List(items) => {
                let Some((head, args)) = items.split_first() else {
                    return Ok(None);
                };
                let Some(h) = head.as_symbol() else {
                    return Ok(None);
                };
                if h == "quote" {
                    if args.len() != 1 {
                        return Ok(None);
                    }
                    let Some(v) = self.datum(&args[0])? else {
                        return Ok(None);
                    };
                    return self.leaf(v).map(Some);
                }
                let Some(sym) = row_spelling(h) else {
                    return Ok(None);
                };
                let k = self.env.row(sym).map_err(kernel_err)?;
                if args.len() != self.env.rows[k].arity {
                    return Ok(None);
                }
                let mut kids = Vec::with_capacity(args.len());
                for a in args {
                    match self.eval_cert(a)? {
                        Some(cv) => kids.push(cv),
                        None => return Ok(None),
                    }
                }
                let vals: Vec<Term> = kids.iter().map(|c| c.value.clone()).collect();
                // Computation first (cheap failure): ⊢ D ⌜(EQUAL (F 'v⃗) 'w)⌝
                // with the model image folded to the canonical value w.
                let Some((w, d_comp)) = self.comp_cert(k, sym, &vals)? else {
                    return Ok(None);
                };
                // Congruence: ⊢ D ⌜(EQUAL (F enc⃗) (F 'v⃗))⌝.
                let qvals: Vec<Term> = vals
                    .iter()
                    .map(|v| tm.quote(v))
                    .collect::<Result<_, _>>()
                    .map_err(kernel_err)?;
                let pairs: Vec<(Term, Term)> = kids
                    .iter()
                    .zip(&qvals)
                    .map(|(c, q)| (c.enc.clone(), q.clone()))
                    .collect();
                let ders: Vec<Thm> = kids.iter().map(|c| c.der.clone()).collect();
                let d_cong = ladder::derive_cong(&self.env, k, &pairs, ders).map_err(kernel_err)?;
                // Splice: (F enc⃗) = (F 'v⃗) = 'w.
                let encs: Vec<Term> = kids.iter().map(|c| c.enc.clone()).collect();
                let enc = tm.app(sym.as_bytes(), &encs).map_err(kernel_err)?;
                let f_qv = tm.app(sym.as_bytes(), &qvals).map_err(kernel_err)?;
                let qw = tm.quote(&w).map_err(kernel_err)?;
                let der = self.trans_cert(&enc, &f_qv, &qw, d_cong, d_comp)?;
                Ok(Some(CertVal { enc, value: w, der }))
            }
        }
    }

    /// The computation-clause certificate for row `k` at canonical values:
    /// `(w, ⊢ D ⌜(EQUAL (F 'v⃗) 'w)⌝)` — [`ladder::derive_comp`] with the
    /// model image folded by a **public S1 model-computation law**
    /// ([`ladder::derive_comp_folded`]). `Ok(None)` when no law covers
    /// these values (e.g. arithmetic on non-integer values) — the caller
    /// falls back.
    fn comp_cert(
        &self,
        k: usize,
        sym: &str,
        vals: &[Term],
    ) -> Result<Option<(Term, Thm)>, Acl2Error> {
        let tm = self.tm();
        let pr = tm.pr;
        // CONS needs no fold: `acons v₀ v₁` IS the canonical value.
        if sym == "CONS" {
            let w = tm
                .th
                .cons
                .clone()
                .apply(vals[0].clone())
                .map_err(kernel_err)?
                .apply(vals[1].clone())
                .map_err(kernel_err)?;
            let der = ladder::derive_comp(&self.env, k, vals).map_err(kernel_err)?;
            return Ok(Some((w, der)));
        }
        let law: Option<Thm> = match sym {
            "CAR" | "CDR" => {
                let cdr = sym == "CDR";
                let v = &vals[0];
                if let Some((h, t)) = as_acons(tm, v) {
                    let l = if cdr { pr.cdr_cons() } else { pr.car_cons() }.map_err(kernel_err)?;
                    Some(
                        l.all_elim(h)
                            .map_err(kernel_err)?
                            .all_elim(t)
                            .map_err(kernel_err)?,
                    )
                } else if *v == tm.th.nil {
                    Some(if cdr { pr.cdr_nil() } else { pr.car_nil() }.map_err(kernel_err)?)
                } else if let Some(i) = as_aint_arg(tm, v) {
                    let l = if cdr { pr.cdr_int() } else { pr.car_int() }.map_err(kernel_err)?;
                    Some(l.all_elim(i).map_err(kernel_err)?)
                } else if let Some(s) = as_asym_arg(tm, v) {
                    let l = if cdr { pr.cdr_sym() } else { pr.car_sym() }.map_err(kernel_err)?;
                    Some(l.all_elim(s).map_err(kernel_err)?)
                } else {
                    None // e.g. the defined constant `t` — no direct law
                }
            }
            "CONSP" => {
                let v = &vals[0];
                if let Some((h, t)) = as_acons(tm, v) {
                    Some(
                        pr.consp_cons()
                            .map_err(kernel_err)?
                            .all_elim(h)
                            .map_err(kernel_err)?
                            .all_elim(t)
                            .map_err(kernel_err)?,
                    )
                } else if *v == tm.th.nil {
                    Some(pr.consp_nil().map_err(kernel_err)?)
                } else {
                    None // aint/asym: no public direct law — fall back
                }
            }
            "EQUAL" => {
                if vals[0] == vals[1] {
                    Some(
                        pr.equal_refl()
                            .map_err(kernel_err)?
                            .all_elim(vals[0].clone())
                            .map_err(kernel_err)?,
                    )
                } else if let (Some(i), Some(j)) =
                    (as_aint_lit(tm, &vals[0]), as_aint_lit(tm, &vals[1]))
                {
                    // Distinct integer literals: genuinely disequal.
                    let ne = pr.int_ne(i, j).map_err(kernel_err)?;
                    Some(
                        pr.equal_ne()
                            .map_err(kernel_err)?
                            .all_elim(vals[0].clone())
                            .map_err(kernel_err)?
                            .all_elim(vals[1].clone())
                            .map_err(kernel_err)?
                            .imp_elim(ne)
                            .map_err(kernel_err)?,
                    )
                } else {
                    None // distinct non-int values: no discrimination law yet
                }
            }
            "BINARY-+" => match (as_aint_lit(tm, &vals[0]), as_aint_lit(tm, &vals[1])) {
                (Some(i), Some(j)) => Some(pr.plus_lit(i, j).map_err(kernel_err)?),
                _ => None, // completion arithmetic (non-numbers read as 0): no public law
            },
            _ => None,
        };
        let Some(law) = law else {
            return Ok(None);
        };
        let w = law
            .concl()
            .as_eq()
            .ok_or_else(|| kernel_err("acl2 cert: model law is not an equation"))?
            .1
            .clone();
        let der = ladder::derive_comp_folded(&self.env, k, vals, &law).map_err(kernel_err)?;
        Ok(Some((w, der)))
    }
}

/// Split `acons h t` into `(h, t)`.
fn as_acons(tm: &Terms, v: &Term) -> Option<(Term, Term)> {
    let (ch, t) = v.as_app()?;
    let (c, h) = ch.as_app()?;
    if *c != tm.th.cons {
        return None;
    }
    Some((h.clone(), t.clone()))
}

/// The payload term of `aint i`.
fn as_aint_arg(tm: &Terms, v: &Term) -> Option<Term> {
    let (f, i) = v.as_app()?;
    (*f == tm.th.aint).then(|| i.clone())
}

/// The payload term of `asym s`.
fn as_asym_arg(tm: &Terms, v: &Term) -> Option<Term> {
    let (f, s) = v.as_app()?;
    (*f == tm.th.asym).then(|| s.clone())
}

/// The literal of `aint ⌜i⌝` as an `i128` (the S1 lit-law input type).
fn as_aint_lit(tm: &Terms, v: &Term) -> Option<i128> {
    let i = as_aint_arg(tm, v)?;
    i128::try_from(&as_int(&i)?).ok()
}

// ============================================================================
// The ACL2 surface tables
// ============================================================================

/// The non-arithmetic primitive heads and their arities. (Note ternary `if`;
/// there is no `cond` in this dialect.)
fn reserved_head(name: &str) -> Option<usize> {
    match name {
        "car" | "cdr" | "consp" | "atom" | "endp" => Some(1),
        "cons" | "equal" => Some(2),
        "if" => Some(3),
        _ => None,
    }
}

/// ACL2/Common Lisp's composed list accessors (`caar` through `cddddr`).
fn composed_accessor(name: &str) -> Option<&[u8]> {
    let bytes = name.as_bytes();
    if bytes.len() >= 3
        && bytes.len() <= 6
        && bytes.first() == Some(&b'c')
        && bytes.last() == Some(&b'r')
        && bytes[1..bytes.len() - 1]
            .iter()
            .all(|b| matches!(b, b'a' | b'd'))
    {
        Some(&bytes[1..bytes.len() - 1])
    } else {
        None
    }
}

/// The ground-arithmetic operator heads.
const INT_OPS: [&str; 7] = ["+", "-", "*", "<=", "=", "zp", "natp"];

/// The arity of a ground-arithmetic operator head (`+ - * <= =` binary,
/// `zp` / `natp` unary); `None` for non-arithmetic heads.
fn int_op_arity(name: &str) -> Option<usize> {
    match name {
        "+" | "-" | "*" | "<=" | "=" => Some(2),
        "zp" | "natp" => Some(1),
        _ => None,
    }
}

/// Is a form **syntactically arithmetic**: a numeral, an arithmetic-op form,
/// or an `equal` with an arithmetic side? Used to route `equal` (integer `=`
/// vs sexpr `eq?`) and to reject integers in list-typed positions. Syntactic
/// on purpose — a user call is never classified arithmetic, even if it
/// returns an integer.
fn is_int_form(e: &SExpr) -> bool {
    match e {
        SExpr::Atom(Atom::Symbol(s)) => s.parse::<Int>().is_ok(),
        SExpr::Atom(_) => false,
        SExpr::List(items) => match items.first().and_then(SExpr::as_symbol) {
            Some(h) if int_op_arity(h).is_some() => true,
            Some("equal") if items.len() == 3 => is_int_form(&items[1]) || is_int_form(&items[2]),
            _ => false,
        },
    }
}

/// Do this (translated) head's arguments sit in `sexpr`-typed positions?
/// True for the list primitives, `eq?`, and user calls (whose formals are
/// always `sexpr`-typed); false for the arithmetic operators and `if` (whose
/// branches may legitimately be integers).
fn sexpr_positions(head: &str) -> bool {
    head != "if" && int_op_arity(head).is_none()
}

// ============================================================================
// Small helpers
// ============================================================================

/// The RHS of an equational conclusion.
fn rhs_of(thm: &Thm) -> Result<Term, Acl2Error> {
    thm.concl()
        .as_eq()
        .map(|(_, r)| r.clone())
        .ok_or_else(|| kernel_err("theorem conclusion is not an equation"))
}

/// The parameter names of a `(p₁ … pₙ)` formal list — distinct plain symbols.
fn param_names(params: &SExpr) -> Result<Vec<String>, String> {
    let SExpr::List(items) = params else {
        return Err("parameter list is not a list".into());
    };
    let mut out = Vec::with_capacity(items.len());
    for p in items {
        let Some(s) = p.as_symbol() else {
            return Err("parameter is not a symbol".into());
        };
        if matches!(s, "t" | "nil") || reserved_head(s).is_some() || INT_OPS.contains(&s) {
            return Err(format!("parameter `{s}` shadows a primitive"));
        }
        if s.parse::<Int>().is_ok() {
            return Err(format!("parameter `{s}` is a numeral"));
        }
        if out.iter().any(|q| q == s) {
            return Err(format!("duplicate parameter `{s}`"));
        }
        out.push(s.to_string());
    }
    Ok(out)
}

/// Select the executable body from ACL2's common extended `defun` syntax.
///
/// A doc string may occur first, followed by any number of `declare` forms.
/// There must then be exactly one body.  Keeping this syntax handling here
/// ensures declarations are never accidentally treated as executable calls.
fn defun_body(items: &[SExpr]) -> Result<&SExpr, String> {
    let mut rest = &items[3..];
    if matches!(rest.first(), Some(SExpr::Atom(Atom::Str { .. }))) {
        rest = &rest[1..];
    }
    while rest
        .first()
        .is_some_and(|e| matches!(e, SExpr::List(xs) if xs.first().and_then(SExpr::as_symbol) == Some("declare")))
    {
        rest = &rest[1..];
    }
    match rest {
        [body] => Ok(body),
        [] => Err("defun: missing body after doc string/declarations".into()),
        _ => Err("defun: expected exactly one body after optional doc string/declarations".into()),
    }
}

/// Encode the conservative surface subset as an ACL2 pseudo-term. This is
/// syntax translation only; every use is subsequently checked by the
/// definitional principle or the derivation kernel.
fn deep_encode(tm: &Terms, e: &SExpr, formals: &[String]) -> Result<Term, String> {
    fn datum(tm: &Terms, d: &SExpr) -> Result<Term, String> {
        match d {
            SExpr::Atom(Atom::Symbol(s)) => {
                if let Ok(n) = s.parse::<Int>() {
                    tm.th.aint_at(&mk_int(n)).map_err(|e| e.to_string())
                } else if s.eq_ignore_ascii_case("nil") {
                    Ok(tm.th.nil.clone())
                } else if s.eq_ignore_ascii_case("t") {
                    Ok(tm.pr.t.clone())
                } else {
                    tm.sym(s.to_ascii_uppercase().as_bytes())
                        .map_err(|e| e.to_string())
                }
            }
            SExpr::List(xs) => {
                let mut out = tm.th.nil.clone();
                for x in xs.iter().rev() {
                    out = tm
                        .th
                        .cons
                        .clone()
                        .apply(datum(tm, x)?)
                        .and_then(|f| f.apply(out))
                        .map_err(|e| e.to_string())?;
                }
                Ok(out)
            }
            SExpr::Atom(_) => Err("strings are outside the ACL2 carrier fragment".into()),
        }
    }
    match e {
        SExpr::Atom(Atom::Symbol(s)) => {
            if formals.iter().any(|p| p == s) {
                tm.sym(s.to_ascii_uppercase().as_bytes())
                    .map_err(|e| e.to_string())
            } else if let Ok(n) = s.parse::<Int>() {
                tm.quote(&tm.th.aint_at(&mk_int(n)).map_err(|e| e.to_string())?)
                    .map_err(|e| e.to_string())
            } else if s.eq_ignore_ascii_case("nil") {
                tm.quote(&tm.th.nil).map_err(|e| e.to_string())
            } else if s.eq_ignore_ascii_case("t") {
                tm.quote(&tm.pr.t).map_err(|e| e.to_string())
            } else {
                // A non-constant atom is an object variable in theorem
                // position; defun admission has already rejected non-formals.
                tm.sym(s.to_ascii_uppercase().as_bytes())
                    .map_err(|e| e.to_string())
            }
        }
        SExpr::Atom(_) => Err("strings are outside the ACL2 pseudo-term fragment".into()),
        SExpr::List(items) => {
            let (head, args) = items
                .split_first()
                .ok_or_else(|| "empty application".to_string())?;
            let head = head
                .as_symbol()
                .ok_or_else(|| "computed function position".to_string())?;
            if head == "quote" {
                if args.len() != 1 {
                    return Err("quote expects one argument".into());
                }
                return tm.quote(&datum(tm, &args[0])?).map_err(|e| e.to_string());
            }
            // ACL2's ENDP is `(not (consp x))`. The conservative kernel
            // defun template is deliberately phrased with a positive CONSP
            // guard, so normalize `(if (endp x) base step)` to
            // `(if (consp x) step base)` before encoding. This is a macro
            // expansion, and the admitted defining equation is checked
            // against the resulting body by the kernel.
            if head == "if"
                && args.len() == 3
                && let SExpr::List(g) = &args[0]
                && g.len() == 2
                && g[0].as_symbol() == Some("endp")
            {
                let c = deep_encode(tm, &g[1], formals)?;
                let guard = tm.app(b"CONSP", &[c]).map_err(|e| e.to_string())?;
                let step = deep_encode(tm, &args[2], formals)?;
                let base = deep_encode(tm, &args[1], formals)?;
                return tm.mk_if(&guard, &step, &base).map_err(|e| e.to_string());
            }
            let enc_args: Vec<Term> = args
                .iter()
                .map(|a| deep_encode(tm, a, formals))
                .collect::<Result<_, _>>()?;
            match head {
                "and" => {
                    let mut out = tm.quote(&tm.pr.t).map_err(|e| e.to_string())?;
                    let nil = tm.quote(&tm.th.nil).map_err(|e| e.to_string())?;
                    for arg in enc_args.iter().rev() {
                        out = tm.mk_if(arg, &out, &nil).map_err(|e| e.to_string())?;
                    }
                    Ok(out)
                }
                "or" => {
                    let mut out = tm.quote(&tm.th.nil).map_err(|e| e.to_string())?;
                    for arg in enc_args.iter().rev() {
                        out = tm.mk_if(arg, arg, &out).map_err(|e| e.to_string())?;
                    }
                    Ok(out)
                }
                "not" if enc_args.len() == 1 => tm
                    .mk_if(
                        &enc_args[0],
                        &tm.quote(&tm.th.nil).map_err(|e| e.to_string())?,
                        &tm.quote(&tm.pr.t).map_err(|e| e.to_string())?,
                    )
                    .map_err(|e| e.to_string()),
                "if" if enc_args.len() == 3 => tm
                    .mk_if(&enc_args[0], &enc_args[1], &enc_args[2])
                    .map_err(|e| e.to_string()),
                "equal" | "=" if enc_args.len() == 2 => tm
                    .mk_equal(&enc_args[0], &enc_args[1])
                    .map_err(|e| e.to_string()),
                "implies" if enc_args.len() == 2 => tm
                    .mk_implies(&enc_args[0], &enc_args[1])
                    .map_err(|e| e.to_string()),
                ">" if enc_args.len() == 2 => tm
                    .app(b"<", &[enc_args[1].clone(), enc_args[0].clone()])
                    .map_err(|e| e.to_string()),
                "<=" if enc_args.len() == 2 => {
                    let lt = tm
                        .app(b"<", &[enc_args[1].clone(), enc_args[0].clone()])
                        .map_err(|e| e.to_string())?;
                    tm.mk_if(
                        &lt,
                        &tm.quote(&tm.th.nil).map_err(|e| e.to_string())?,
                        &tm.quote(&tm.pr.t).map_err(|e| e.to_string())?,
                    )
                    .map_err(|e| e.to_string())
                }
                ">=" if enc_args.len() == 2 => {
                    let lt = tm
                        .app(b"<", &[enc_args[0].clone(), enc_args[1].clone()])
                        .map_err(|e| e.to_string())?;
                    tm.mk_if(
                        &lt,
                        &tm.quote(&tm.th.nil).map_err(|e| e.to_string())?,
                        &tm.quote(&tm.pr.t).map_err(|e| e.to_string())?,
                    )
                    .map_err(|e| e.to_string())
                }
                _ => {
                    let spelling = match head {
                        "car" => "CAR",
                        "cdr" => "CDR",
                        "cons" => "CONS",
                        "consp" => "CONSP",
                        "integerp" => "INTEGERP",
                        "symbolp" => "SYMBOLP",
                        "+" => "BINARY-+",
                        "*" => "BINARY-*",
                        "<" => "<",
                        _ => {
                            return tm
                                .app(head.to_ascii_uppercase().as_bytes(), &enc_args)
                                .map_err(|e| e.to_string());
                        }
                    };
                    tm.app(spelling.as_bytes(), &enc_args)
                        .map_err(|e| e.to_string())
                }
            }
        }
    }
}

/// Is `e` a **non-empty** `car`/`cdr` chain applied to exactly the formal
/// `formal`? (`(cdr x)`, `(car (cdr x))`, … — the structural-descent shape.)
fn is_proper_projection(e: &SExpr, formal: &str) -> bool {
    fn depth(e: &SExpr, formal: &str) -> Option<usize> {
        match e {
            SExpr::Atom(Atom::Symbol(s)) if s.as_str() == formal => Some(0),
            SExpr::List(items) if items.len() == 2 => match items[0].as_symbol() {
                Some("car") | Some("cdr") => depth(&items[1], formal).map(|d| d + 1),
                Some(h) if composed_accessor(h).is_some() => {
                    depth(&items[1], formal).map(|d| d + composed_accessor(h).unwrap().len())
                }
                _ => None,
            },
            _ => None,
        }
    }
    depth(e, formal).is_some_and(|d| d >= 1)
}
