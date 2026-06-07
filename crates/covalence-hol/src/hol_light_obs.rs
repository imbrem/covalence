//! HOL Light bootstrap on top of `covalence-pure`.
//!
//! ## What this module is
//!
//! A single Rust `enum` ([`HolLight`]) that carries every HOL Light
//! primitive — `bool`, `=`, `T`, `F`, `⟹`, `¬`, `∧`, `∨`, `↔`, `∀`,
//! `∃`, `ε`, plus `Trueprop` — as variants of one observer family.
//! Because all variants share one Rust type, they share one
//! parametric-ε family in Pure's soundness story, which lets
//! [`Thm::obs_eq`], [`Thm::obs_true`], and [`Thm::obs_imp`] mint
//! HOL theorems with the kernel's blessing.
//!
//! All observers and the [`HolLightCtx`] handle are process-global
//! lazy statics. Constructing a `HolLightCtx` is free; it just gives
//! you method syntax over module-level functions.
//!
//! ## Mapping to Isabelle/HOL
//!
//! `covalence-pure` plays the role of Isabelle/Pure: the meta-logic
//! with `prop`, meta-`⋀`, meta-`⟹`, meta-`≡`, plus assume,
//! `⟹`/`⋀`-intro/elim, refl/trans/sym/cong_app/cong_abs, β/η, and
//! `eq_mp` (the meta-EQ_MP).
//!
//! `covalence-hol` plays the role of Isabelle/HOL: HOL as a *theory*
//! built on top of the meta-logic. Standard Isabelle/HOL ships with:
//!
//! - `bool` as a separate type.
//! - `Trueprop : bool ⇒ prop` as the explicit coercion.
//! - HOL `=` as a constant at `'a ⇒ 'a ⇒ bool` returning bool.
//! - One bridge axiom: `eq_reflection : (x = y) ⟹ (x ≡ y)` where
//!   the LHS is HOL-eq at any type and the RHS is meta-eq. From this
//!   axiom plus Pure's rules, Isabelle derives HOL Light's 10
//!   primitive rules.
//!
//! Our setup parallels this exactly:
//!
//! - HOL `bool` ↔ `TyConObs(Bool_obs, "bool", [])`. A distinct type
//!   from Pure prop (different `Arc` identity).
//! - HOL `=` ↔ `Term::obs(Eq_obs, α → α → bool)`. Returns HOL bool,
//!   never prop. All HOL primitives are `Term::obs` over global
//!   observers in the `HolLight` family.
//! - `Trueprop : bool → prop` ↔ `Term::obs(Trueprop_obs, bool → prop)`.
//!   A HOL theorem `⊢_HOL p` (with p : bool) is internally the Pure
//!   theorem `⊢_Pure Trueprop p`.
//!
//! ## Where we diverge from Isabelle/HOL
//!
//! Isabelle/HOL **uses** the `eq_reflection` axiom to bridge HOL `=`
//! and Pure `≡`, then derives every HOL Light rule by composing Pure
//! rules through that bridge. Each derivation traces a chain of Pure
//! inferences and produces a real Pure theorem.
//!
//! Covalence-HOL **bypasses** the eq_reflection bridge entirely. The
//! [`HolLight`] observer's [`ObsImp`] / [`ObsTrue`] policies directly
//! recognise HOL-Light-derivable shapes (structural pattern checks)
//! and mint matching Pure theorems via Pure's observer-rule
//! primitives. Soundness comes from Pure's *parametric-ε model*:
//! any prop-typed observation can be interpreted as ⊤ in the model,
//! so any rule the policy asserts is consistent with that model.
//! The whole `HolLight` family shares one ε-family, so the policy
//! choices for HOL primitives don't interact with policies for
//! unrelated observer types.
//!
//! Both approaches yield the same theorems. The covalence approach
//! avoids one axiom in the trusted base and has cheaper bookkeeping
//! (no eq_reflection-application chains), at the cost of less direct
//! correspondence to the Isabelle/HOL derivation chain.
//!
//! ## Tarski-T encoding
//!
//! HOL judgements live in Pure as `⊢_Pure Trueprop p`. A HOL theorem
//! `Γ ⊢_HOL p` (with `p : bool` and each `h ∈ Γ : bool`) is the Pure
//! theorem
//!
//! ```text
//! {Trueprop h | h ∈ Γ}  ⊢_Pure  Trueprop p
//! ```
//!
//! Pure's hypothesis set carries the HOL hypotheses (lifted through
//! Trueprop), and the Pure conclusion carries the HOL conclusion
//! (also lifted). This is the standard "Tarski-T" encoding — same
//! shape Isabelle/HOL uses.
//!
//! ## The 10 HOL Light rules
//!
//! Status w.r.t. this implementation:
//!
//! | HOL Light rule    | Status     | Mechanism                          |
//! |-------------------|------------|------------------------------------|
//! | REFL              | ✅ direct  | [`ObsTrue`] policy (no hyps)       |
//! | TRANS             | ✅ direct  | [`ObsImp`] policy (2 hyps)         |
//! | MK_COMB           | ✅ direct  | [`ObsImp`] policy (2 hyps)         |
//! | BETA              | ✅ direct  | [`ObsTrue`] policy (no hyps)       |
//! | ASSUME            | ✅ direct  | `Pure::Thm::assume` on `Trueprop p`|
//! | EQ_MP             | ✅ direct  | [`ObsImp`] policy (2 hyps)         |
//! | (HOL `sym`)       | ✅ direct  | [`ObsImp`] policy (1 hyp)          |
//! | ABS               | ⚠ adapter | Needs Pure `cong_abs` (hyp-side-condition) |
//! | INST              | ⚠ adapter | Needs uniform hyp+concl substitution |
//! | INST_TYPE         | ⚠ adapter | Pure `inst_tfree` directly         |
//! | DEDUCT_ANTISYM    | ⚠ adapter | Pure `imp_intro` on both sides     |
//!
//! "Direct" rules fit the lazy-theorem pattern: the implication
//! `⊢ hyps ⟹ ... ⟹ concl` is sound under any meta-level instance
//! because the rule has no hypothesis-side-condition and no need to
//! transform source theorems' hypotheses.
//!
//! "Adapter" rules (ABS, INST, INST_TYPE, DEDUCT_ANTISYM) **cannot**
//! safely fit the lazy-theorem pattern. They either:
//!
//! - require a side-condition on the source theorem's hypotheses
//!   (ABS: binder var not free in hyps), or
//! - need to transform the source theorem's hypotheses as well as
//!   its conclusion (INST, INST_TYPE), or
//! - need to manipulate hypothesis SETS (DEDUCT_ANTISYM).
//!
//! These constraints can't be encoded as a Pure lazy theorem. They
//! belong in the (forthcoming) `PureHol` adapter that implements
//! `HolLightKernel`, where each rule takes the actual source theorems
//! and applies Pure's existing rules with the correct discipline.
//!
//! ## Why naive ABS via `obs_imp` is unsound
//!
//! A naive ABS implementation would mint the lazy theorem
//!
//! ```text
//! ⊢_Pure Trueprop (Eq s t) ⟹ Trueprop (Eq (λx. close(s, x)) (λx. close(t, x)))
//! ```
//!
//! This is FALSE in general. Take `s = x` (free), `t = c` (constant):
//! the antecedent is `x = c`, the consequent is `(λx. x) = (λx. c)`,
//! i.e., `id = const c`. A single `x = c` does not imply the function
//! equation (which would require `c = c, c = c, …` for every input
//! value). HOL Light prevents this by requiring `x` to not be free
//! in the source theorem's hypotheses — but that check requires
//! looking at the source theorem at rule-application time, which
//! `obs_imp` policy can't do.
//!
//! ## Why naive INST via `obs_imp` is unsound
//!
//! A naive INST would mint
//!
//! ```text
//! ⊢_Pure Trueprop p ⟹ Trueprop p[x := y]
//! ```
//!
//! Take `p = "x = 5"`, `y = 10`: antecedent `x = 5` (true at x = 5),
//! consequent `10 = 5` (false). HOL Light's INST avoids this by
//! applying the substitution to *both* hypotheses and conclusion of
//! the source theorem (so a hypothesis `x = 5` would become `10 = 5`,
//! a contradictory hypothesis — the result has empty content). The
//! lazy-theorem pattern only transforms the conclusion; it can't
//! soundly do INST in the general case.
//!
//! The previous version of this module had unsound `check_abs_pattern`
//! and `check_inst_pattern` in the [`ObsImp`] policy. They were
//! removed in commit X (this audit). The adapter approach is the
//! correct path forward for ABS, INST, INST_TYPE, DEDUCT_ANTISYM.
//!
//! ## Soundness summary
//!
//! [`Thm::obs_true`] and [`Thm::obs_imp`] are sound under Pure's
//! parametric-ε model regardless of the policy's return value. So
//! the kernel TCB is unaffected by anything the [`HolLight`] policy
//! does — at worst a buggy policy refuses sound theorems or asserts
//! propositions that are valid in the model (i.e., they have ⊤
//! interpretation). It cannot produce a false `Thm`.
//!
//! What soundness does require: the **lazy theorem** itself must be
//! a true implication chain under the standard model where HOL `=`
//! is logical equality, `Trueprop p ↔ ⟦p⟧`, etc. That's the audit
//! gate: every shape we add to the policy must be a valid HOL
//! implication. Sym, trans, MK_COMB, EQ_MP at bool, refl, beta all
//! pass that gate. ABS and INST do not, as analysed above.

use std::any::Any;
use std::fmt;
use std::sync::LazyLock;

use covalence_pure::{ObsEq, ObsImp, ObsTrue, Object, Observer, Term, TermKind, Type};

// ============================================================================
// Process-global lazy statics
// ============================================================================
//
// One `Object` per HolLight variant, allocated on first access and reused
// for the whole process. [`HolLightCtx`] is a zero-sized handle over these
// globals — constructing one is free, and every `HolLightCtx` produces the
// same theory (the HOL Light theory).

static BOOL_OBS: LazyLock<Object> = LazyLock::new(|| Object::new(HolLight::Bool));
static EQ_OBS: LazyLock<Object> = LazyLock::new(|| Object::new(HolLight::Eq));
static TRUE_OBS: LazyLock<Object> = LazyLock::new(|| Object::new(HolLight::True));
static FALSE_OBS: LazyLock<Object> = LazyLock::new(|| Object::new(HolLight::False));
static IMP_OBS: LazyLock<Object> = LazyLock::new(|| Object::new(HolLight::Imp));
static NOT_OBS: LazyLock<Object> = LazyLock::new(|| Object::new(HolLight::Not));
static AND_OBS: LazyLock<Object> = LazyLock::new(|| Object::new(HolLight::And));
static OR_OBS: LazyLock<Object> = LazyLock::new(|| Object::new(HolLight::Or));
static IFF_OBS: LazyLock<Object> = LazyLock::new(|| Object::new(HolLight::Iff));
static FORALL_OBS: LazyLock<Object> = LazyLock::new(|| Object::new(HolLight::Forall));
static EXISTS_OBS: LazyLock<Object> = LazyLock::new(|| Object::new(HolLight::Exists));
static SELECT_OBS: LazyLock<Object> = LazyLock::new(|| Object::new(HolLight::Select));
static TRUEPROP_OBS: LazyLock<Object> = LazyLock::new(|| Object::new(HolLight::Trueprop));

// ============================================================================
// The HolLight observer family
// ============================================================================

/// The HOL Light observer family. One Rust variant per HOL Light
/// primitive — all sharing a single Rust type, hence a single ε-family
/// in Pure's soundness model. See the module documentation for how
/// this enables the bootstrap.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum HolLight {
    // -- Type constructor --
    /// HOL `bool` — type of truth values. Distinct from Pure `prop`.
    Bool,

    // -- Equality --
    /// HOL `=` at polymorphic type `'a → 'a → bool`. The instance
    /// type is carried as the term's `Type` field.
    Eq,

    // -- Truth values --
    /// HOL `T : bool`.
    True,
    /// HOL `F : bool`.
    False,

    // -- Connectives --
    /// `⟹` (implication) at `bool → bool → bool`.
    Imp,
    /// `¬` (negation) at `bool → bool`.
    Not,
    /// `∧` (conjunction) at `bool → bool → bool`.
    And,
    /// `∨` (disjunction) at `bool → bool → bool`.
    Or,
    /// `⟺` (iff) at `bool → bool → bool`. Coincides with `Eq` at bool
    /// in the standard model; exposed separately as a distinct
    /// observer to match HOL Light's naming.
    Iff,

    // -- Quantifiers --
    /// `∀` at `('a → bool) → bool`.
    Forall,
    /// `∃` at `('a → bool) → bool`.
    Exists,
    /// `ε` (Hilbert's choice) at `('a → bool) → 'a`.
    Select,

    /// `Trueprop : bool → prop` — explicit coercion from HOL bool to
    /// Pure prop. A HOL theorem `⊢_HOL p` is the Pure theorem
    /// `⊢_Pure Trueprop p`. Mirrors Isabelle/HOL's `Trueprop`.
    Trueprop,
}

impl HolLight {
    /// Human-readable label used in display output. Matches HOL Light's
    /// printable surface forms (`=`, `==>`, `~`, `/\`, `\/`, `<=>`,
    /// `!`, `?`, `@`, `T`, `F`, `bool`).
    pub fn label(&self) -> &'static str {
        match self {
            HolLight::Bool => "bool",
            HolLight::Eq => "=",
            HolLight::True => "T",
            HolLight::False => "F",
            HolLight::Imp => "==>",
            HolLight::Not => "~",
            HolLight::And => "/\\",
            HolLight::Or => "\\/",
            HolLight::Iff => "<=>",
            HolLight::Forall => "!",
            HolLight::Exists => "?",
            HolLight::Select => "@",
            HolLight::Trueprop => "Trueprop",
        }
    }
}

impl fmt::Display for HolLight {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.label())
    }
}

// ============================================================================
// ObsEq policy — meta-equations between HOL-typed terms
// ============================================================================

/// `obs_eq` policy for [`HolLight`].
///
/// **Scope.** This policy produces *meta-equations* of the form
/// `⊢_Pure (HOL-bool-term-1) ≡ (HOL-bool-term-2)`. These are Pure
/// theorems with concl-type prop, useful when you want to rewrite
/// HOL terms at the meta level (e.g., normalisation by congruence).
///
/// The patterns recognised here are conservative:
///
/// - `Eq a a ≡ True` (HOL refl, lifted to Pure meta-eq, structural `a`).
/// - `Eq u v ≡ Eq v u` (HOL sym, lifted to Pure meta-eq).
///
/// Everything else returns `false`. Note that the more interesting
/// HOL theorems live in [`Thm::obs_true`] and [`Thm::obs_imp`] under
/// `Trueprop` — this policy is just for the meta-eq variant.
impl ObsEq for HolLight {
    fn obs_eq(
        &self,
        other: &Self,
        my_args: &[Term],
        other_args: &[Term],
        _hint: Option<&dyn covalence_pure::Hint>,
    ) -> bool {
        match (self, other) {
            // `Eq a a ≡ True`  (HOL refl lifted to meta-eq).
            (HolLight::Eq, HolLight::True) if my_args.len() == 2 && other_args.is_empty() => {
                my_args[0] == my_args[1]
            }
            (HolLight::True, HolLight::Eq) if my_args.is_empty() && other_args.len() == 2 => {
                other_args[0] == other_args[1]
            }
            // `Eq u v ≡ Eq v u`  (HOL sym lifted to meta-eq).
            (HolLight::Eq, HolLight::Eq) if my_args.len() == 2 && other_args.len() == 2 => {
                my_args[0] == other_args[1] && my_args[1] == other_args[0]
            }
            _ => false,
        }
    }
}

// ============================================================================
// ObsTrue policy — HOL theorems with no hypotheses
// ============================================================================

/// `obs_true` policy for [`HolLight`]. Mints `⊢_Pure Trueprop p` for
/// the HOL theorems that need no source-theorem assumptions.
///
/// **Recognised shapes:**
///
/// - **HOL refl**: `Trueprop (Eq a a)` for any term `a` (structural).
/// - **HOL beta**: `Trueprop (Eq ((λx. body) operand) (open body operand))`
///   where opening the lambda body with the operand gives the RHS.
///
/// Both are sound HOL theorems under the standard model with no
/// hypothesis-side-conditions and no need to transform any source
/// theorem's hypotheses.
impl ObsTrue for HolLight {
    fn obs_true(&self, args: &[Term], _hint: Option<&dyn covalence_pure::Hint>) -> bool {
        if !matches!(self, HolLight::Trueprop) || args.len() != 1 {
            return false;
        }
        let body = &args[0];
        check_refl_pattern(body) || check_beta_pattern(body)
    }
}

// ============================================================================
// ObsImp policy — HOL Light lazy-theorem rules
// ============================================================================

/// `obs_imp` policy for [`HolLight`]. Mints lazy theorems
///
/// ```text
/// ⊢_Pure hyps[0] ⟹ hyps[1] ⟹ … ⟹ hyps[n] ⟹ Trueprop p
/// ```
///
/// Callers chain `imp_elim` with concrete source theorems to discharge
/// the antecedents one by one.
///
/// **Recognised shapes** (in order of `hyps.len()`):
///
/// - 1 hyp:
///   - **HOL sym**: hyp = `Trueprop (Eq a b)`, concl = `Eq b a`.
///
/// - 2 hyps:
///   - **HOL trans**: hyps = `Trueprop (Eq a b)`, `Trueprop (Eq b c)`,
///     concl = `Eq a c`.
///   - **HOL MK_COMB**: hyps = `Trueprop (Eq f g)`, `Trueprop (Eq x y)`,
///     concl = `Eq (App f x) (App g y)`.
///   - **HOL EQ_MP** at bool: hyps = `Trueprop (Eq p q)`, `Trueprop p`,
///     concl = `q`. (Bool-level only — for general-type EQ, use sym +
///     trans + congruence chains.)
///
/// **Not recognised** (architectural — would be unsound here):
///
/// - HOL ABS — see module documentation. Lazy-theorem encoding fails
///   the soundness check when the binder variable appears free in the
///   source theorem's hypotheses.
/// - HOL INST — same issue: substitution must apply uniformly to
///   hyps and concl, but `obs_imp` only transforms the concl.
/// - HOL INST_TYPE, DEDUCT_ANTISYM — handled at the kernel-adapter
///   level.
impl ObsImp for HolLight {
    fn obs_imp(
        &self,
        args: &[Term],
        hyps: &[Term],
        _hint: Option<&dyn covalence_pure::Hint>,
    ) -> bool {
        if !matches!(self, HolLight::Trueprop) || args.len() != 1 {
            return false;
        }
        let concl_body = &args[0];
        match hyps.len() {
            1 => check_sym_pattern(&hyps[0], concl_body),
            2 => {
                check_trans_pattern(&hyps[0], &hyps[1], concl_body)
                    || check_mk_comb_pattern(&hyps[0], &hyps[1], concl_body)
                    || check_eq_mp_pattern(&hyps[0], &hyps[1], concl_body)
            }
            _ => false,
        }
    }
}

// ============================================================================
// Pattern checks for HOL Light rules
// ============================================================================
//
// Each `check_*_pattern` helper recognises one HOL Light derivation shape.
// They're all structural / decidable: given the inputs, the helper either
// returns true (rule applies) or false (rule doesn't). None of them
// allocate or mutate; they're pure functions of the input terms.

/// **HOL refl** at the Trueprop level: `Trueprop (Eq a a)` for any term `a`.
///
/// Match: `Eq` observer at the head, two structurally-equal args.
fn check_refl_pattern(concl_body: &Term) -> bool {
    decompose_hol_eq(concl_body)
        .map(|(a, b)| a == b)
        .unwrap_or(false)
}

/// **HOL beta** at the Trueprop level:
/// `Trueprop (Eq ((λ. body) operand) (open body operand))`.
///
/// Match: outer `Eq` over a β-redex on the LHS and the β-reduced
/// term on the RHS. Uses Pure's `subst::open` to compute the reduction.
fn check_beta_pattern(concl_body: &Term) -> bool {
    let Some((lhs, rhs)) = decompose_hol_eq(concl_body) else {
        return false;
    };
    let TermKind::App(f, operand) = lhs.kind() else {
        return false;
    };
    let TermKind::Abs(_h, _ty, body) = f.kind() else {
        return false;
    };
    covalence_pure::subst::open(body, operand) == rhs
}

/// **HOL sym**: lazy theorem
/// `⊢ Trueprop (Eq a b) ⟹ Trueprop (Eq b a)`.
///
/// Match: hyp is `Trueprop (Eq a b)`, concl is `Eq b a` (swap of args).
fn check_sym_pattern(hyp: &Term, concl_body: &Term) -> bool {
    let Some(hyp_body) = unwrap_trueprop(hyp) else {
        return false;
    };
    let (Some((a, b)), Some((b2, a2))) =
        (decompose_hol_eq(&hyp_body), decompose_hol_eq(concl_body))
    else {
        return false;
    };
    a == a2 && b == b2
}

/// **HOL trans**: lazy theorem
/// `⊢ Trueprop (Eq a b) ⟹ Trueprop (Eq b c) ⟹ Trueprop (Eq a c)`.
///
/// Match: matching middle term across the two hyps; concl shows
/// the outer-pair equation.
fn check_trans_pattern(hyp1: &Term, hyp2: &Term, concl_body: &Term) -> bool {
    let (Some(h1), Some(h2)) = (unwrap_trueprop(hyp1), unwrap_trueprop(hyp2)) else {
        return false;
    };
    let (Some((a, b1)), Some((b2, c)), Some((wa, wc))) = (
        decompose_hol_eq(&h1),
        decompose_hol_eq(&h2),
        decompose_hol_eq(concl_body),
    ) else {
        return false;
    };
    b1 == b2 && a == wa && c == wc
}

/// **HOL MK_COMB**: lazy theorem
/// `⊢ Trueprop (Eq f g) ⟹ Trueprop (Eq x y) ⟹ Trueprop (Eq (f x) (g y))`.
///
/// Match: hyps give two equations f=g and x=y; concl applies both
/// sides to give (f x) = (g y).
fn check_mk_comb_pattern(hyp1: &Term, hyp2: &Term, concl_body: &Term) -> bool {
    let (Some(h1), Some(h2)) = (unwrap_trueprop(hyp1), unwrap_trueprop(hyp2)) else {
        return false;
    };
    let (Some((f, g)), Some((x, y)), Some((lhs, rhs))) = (
        decompose_hol_eq(&h1),
        decompose_hol_eq(&h2),
        decompose_hol_eq(concl_body),
    ) else {
        return false;
    };
    let (TermKind::App(lf, lx), TermKind::App(rf, rx)) = (lhs.kind(), rhs.kind()) else {
        return false;
    };
    *lf == f && *lx == x && *rf == g && *rx == y
}

/// **HOL EQ_MP** at bool: lazy theorem
/// `⊢ Trueprop (Eq p q) ⟹ Trueprop p ⟹ Trueprop q`.
///
/// Match: first hyp is `Eq p q`, second is `p`, concl is `q`.
/// Specifically the bool-level EQ_MP (where `Eq` at bool×bool is
/// iff). For general-type EQ_MP, use the same shape with the
/// corresponding HOL `=` instances.
fn check_eq_mp_pattern(hyp1: &Term, hyp2: &Term, concl_body: &Term) -> bool {
    let (Some(h1), Some(h2_body)) = (unwrap_trueprop(hyp1), unwrap_trueprop(hyp2)) else {
        return false;
    };
    let Some((p, q)) = decompose_hol_eq(&h1) else {
        return false;
    };
    p == h2_body && q == *concl_body
}

// ============================================================================
// Decompose helpers (structural inspection of HOL primitives)
// ============================================================================

/// If `t` is `App(App(HolEq, a), b)` with the `HolLight::Eq` observer
/// at the head, return `(a, b)`. Otherwise `None`.
///
/// Used by every HOL rule pattern check. Verifies that the head obs
/// is specifically `HolLight::Eq` (not some other family or variant).
fn decompose_hol_eq(t: &Term) -> Option<(Term, Term)> {
    let TermKind::App(outer_fn, outer_arg) = t.kind() else {
        return None;
    };
    let TermKind::App(inner_fn, inner_arg) = outer_fn.kind() else {
        return None;
    };
    let TermKind::Obs(obs, _) = inner_fn.kind() else {
        return None;
    };
    obs.downcast::<HolLight>()
        .filter(|o| matches!(o, HolLight::Eq))?;
    Some((inner_arg.clone(), outer_arg.clone()))
}

/// If `t` is `App(Trueprop, body)` with the `HolLight::Trueprop`
/// observer at the head, return `body`. Otherwise `None`.
///
/// Used to recover the inner HOL bool term from a Pure prop-typed
/// hypothesis.
fn unwrap_trueprop(t: &Term) -> Option<Term> {
    let TermKind::App(f, body) = t.kind() else {
        return None;
    };
    let TermKind::Obs(obs, _) = f.kind() else {
        return None;
    };
    obs.downcast::<HolLight>()
        .filter(|o| matches!(o, HolLight::Trueprop))?;
    Some(body.clone())
}

// ============================================================================
// HolLightCtx — zero-sized handle on the process-global HOL primitives
// ============================================================================

/// Zero-sized handle on the process-global HOL Light primitives.
/// Constructing one is free — there are no fields. Methods delegate
/// to the module-level `LazyLock` statics. Two `HolLightCtx` values
/// are interchangeable.
#[derive(Clone, Copy, Default)]
pub struct HolLightCtx;

impl HolLightCtx {
    /// Construct a handle. Free; no allocation.
    pub fn new() -> Self {
        Self
    }

    // ---- HOL types ----

    /// HOL `bool` — `TyConObs(bool_obs, "bool", [])` over the global
    /// `BOOL_OBS`. Distinct from Pure `prop`.
    pub fn bool_type(&self) -> Type {
        Type::tycon_obs_from_dyn((*BOOL_OBS).clone(), "bool", vec![])
    }

    /// Pure function type α → β. HOL doesn't add a new function-type
    /// constructor; we re-use Pure's `Fun`.
    pub fn fun_type(&self, a: Type, b: Type) -> Type {
        Type::fun(a, b)
    }

    // ---- HOL constants (term-level Obs leaves at appropriate types) ----

    /// Construct a `Term::obs` at the given type over the given
    /// global observer. Used by every constant accessor below.
    fn obs_term(observer: &Object, ty: Type) -> Term {
        Term::obs_from_dyn(observer.clone(), ty)
    }

    /// HOL `=` instantiated at `α → α → bool`.
    pub fn eq_at(&self, alpha: Type) -> Term {
        let ty = Type::fun(alpha.clone(), Type::fun(alpha, self.bool_type()));
        Self::obs_term(&EQ_OBS, ty)
    }

    /// `t = u : bool`, given `t` and `u` of the same type α. Errors
    /// if `t` is ill-typed (its `type_of` fails).
    pub fn mk_eq(&self, lhs: Term, rhs: Term) -> Result<Term, covalence_pure::Error> {
        let alpha = lhs.type_of()?;
        let eq = self.eq_at(alpha);
        Ok(Term::app(Term::app(eq, lhs), rhs))
    }

    /// HOL `T : bool`.
    pub fn t(&self) -> Term {
        Self::obs_term(&TRUE_OBS, self.bool_type())
    }

    /// HOL `F : bool`.
    pub fn f(&self) -> Term {
        Self::obs_term(&FALSE_OBS, self.bool_type())
    }

    /// HOL `==>` at `bool → bool → bool`.
    pub fn imp_op(&self) -> Term {
        let b = self.bool_type();
        Self::obs_term(&IMP_OBS, Type::fun(b.clone(), Type::fun(b.clone(), b)))
    }
    /// HOL `p ==> q`.
    pub fn mk_imp(&self, p: Term, q: Term) -> Term {
        Term::app(Term::app(self.imp_op(), p), q)
    }

    /// HOL `~` at `bool → bool`.
    pub fn not_op(&self) -> Term {
        let b = self.bool_type();
        Self::obs_term(&NOT_OBS, Type::fun(b.clone(), b))
    }
    /// HOL `~ p`.
    pub fn mk_not(&self, p: Term) -> Term {
        Term::app(self.not_op(), p)
    }

    /// HOL `/\` at `bool → bool → bool`.
    pub fn and_op(&self) -> Term {
        let b = self.bool_type();
        Self::obs_term(&AND_OBS, Type::fun(b.clone(), Type::fun(b.clone(), b)))
    }
    /// HOL `p /\ q`.
    pub fn mk_and(&self, p: Term, q: Term) -> Term {
        Term::app(Term::app(self.and_op(), p), q)
    }

    /// HOL `\/` at `bool → bool → bool`.
    pub fn or_op(&self) -> Term {
        let b = self.bool_type();
        Self::obs_term(&OR_OBS, Type::fun(b.clone(), Type::fun(b.clone(), b)))
    }
    /// HOL `p \/ q`.
    pub fn mk_or(&self, p: Term, q: Term) -> Term {
        Term::app(Term::app(self.or_op(), p), q)
    }

    /// HOL `<=>` at `bool → bool → bool`.
    pub fn iff_op(&self) -> Term {
        let b = self.bool_type();
        Self::obs_term(&IFF_OBS, Type::fun(b.clone(), Type::fun(b.clone(), b)))
    }
    /// HOL `p <=> q`.
    pub fn mk_iff(&self, p: Term, q: Term) -> Term {
        Term::app(Term::app(self.iff_op(), p), q)
    }

    /// HOL `∀` at `(α → bool) → bool`.
    pub fn forall_at(&self, alpha: Type) -> Term {
        let pred = Type::fun(alpha, self.bool_type());
        Self::obs_term(&FORALL_OBS, Type::fun(pred, self.bool_type()))
    }
    /// HOL `∀x:α. body` — `Forall (λx:α. body)`.
    pub fn mk_forall(&self, hint: &str, alpha: Type, body: Term) -> Term {
        let lambda = Term::abs(hint, alpha.clone(), body);
        Term::app(self.forall_at(alpha), lambda)
    }

    /// HOL `∃` at `(α → bool) → bool`.
    pub fn exists_at(&self, alpha: Type) -> Term {
        let pred = Type::fun(alpha, self.bool_type());
        Self::obs_term(&EXISTS_OBS, Type::fun(pred, self.bool_type()))
    }
    /// HOL `∃x:α. body` — `Exists (λx:α. body)`.
    pub fn mk_exists(&self, hint: &str, alpha: Type, body: Term) -> Term {
        let lambda = Term::abs(hint, alpha.clone(), body);
        Term::app(self.exists_at(alpha), lambda)
    }

    /// HOL `ε` (Hilbert's choice) at `(α → bool) → α`.
    pub fn select_at(&self, alpha: Type) -> Term {
        let pred = Type::fun(alpha.clone(), self.bool_type());
        Self::obs_term(&SELECT_OBS, Type::fun(pred, alpha))
    }
    /// HOL `ε x:α. body` — `Select (λx:α. body)`.
    pub fn mk_select(&self, hint: &str, alpha: Type, body: Term) -> Term {
        let lambda = Term::abs(hint, alpha.clone(), body);
        Term::app(self.select_at(alpha), lambda)
    }

    // ---- Trueprop coercion ----

    /// HOL `Trueprop` at type `bool → prop` — the explicit coercion
    /// from HOL bool to Pure prop. A HOL theorem `⊢_HOL p` becomes
    /// the Pure theorem `⊢_Pure Trueprop p`.
    pub fn trueprop(&self) -> Term {
        Self::obs_term(&TRUEPROP_OBS, Type::fun(self.bool_type(), Type::prop()))
    }

    /// `Trueprop p` — wrap a HOL bool term as a Pure prop. Errors if
    /// `p` is not bool-typed.
    pub fn mk_trueprop(&self, p: Term) -> Result<Term, covalence_pure::Error> {
        let p_ty = p.type_of()?;
        if p_ty != self.bool_type() {
            return Err(covalence_pure::Error::TypeMismatch {
                expected: self.bool_type(),
                got: p_ty,
            });
        }
        Ok(Term::app(self.trueprop(), p))
    }

    // ---- Identity check helpers ----

    fn term_obs_ptr_id(t: &Term) -> Option<usize> {
        match t.kind() {
            TermKind::Obs(o, _) => Some(o.ptr_id()),
            _ => None,
        }
    }

    /// `true` iff `t` is the HOL `True` observer (Arc identity).
    pub fn is_true(&self, t: &Term) -> bool {
        Self::term_obs_ptr_id(t) == Some(TRUE_OBS.ptr_id())
    }

    /// `true` iff `t` is the HOL `False` observer.
    pub fn is_false(&self, t: &Term) -> bool {
        Self::term_obs_ptr_id(t) == Some(FALSE_OBS.ptr_id())
    }

    /// `true` iff `t` is the HOL `Trueprop` observer.
    pub fn is_trueprop(&self, t: &Term) -> bool {
        Self::term_obs_ptr_id(t) == Some(TRUEPROP_OBS.ptr_id())
    }

    /// Pointer-id of the `Eq` observer — useful for inspection or
    /// cross-process equality checks.
    pub fn eq_obs_ptr_id(&self) -> usize {
        EQ_OBS.ptr_id()
    }

    /// Pointer-id of the `Trueprop` observer.
    pub fn trueprop_obs_ptr_id(&self) -> usize {
        TRUEPROP_OBS.ptr_id()
    }
}

/// Marker trait certifying that an observer is in the [`HolLight`]
/// family. Useful as a generic bound when threading HOL-specific
/// reasoning through code that's parametric over observer types.
pub trait IsHolLight: Observer {}
impl IsHolLight for HolLight {}

// Allow `_hint: Option<&dyn Any>` to be passed through — Pure's Hint
// trait extends Any, so a generic `&dyn Any` could be wrapped, but
// for now the policies just ignore the hint. The hint trait is
// reserved for future adapter-layer rules that need source-theorem
// witnesses (e.g., observer-backed solvers).
#[allow(unused_imports)]
use Any as _;
