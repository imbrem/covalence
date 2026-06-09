//! HOL Light bootstrap on top of `covalence-pure`.
//!
//! ## What this module is
//!
//! A single Rust `enum` ([`HolLight`]) that carries every HOL Light
//! primitive — `bool`, `=`, `T`, `F`, `⟹`, `¬`, `∧`, `∨`, `↔`, `∀`,
//! `∃`, `ε`, plus `Trueprop` — as variants of one observer family.
//! Plus the polymorphic `eq_reflection` axiom that bridges HOL
//! bool-equality to Pure meta-equality. That's it.
//!
//! All observers and the `eq_reflection` axiom are process-global
//! lazy statics. [`HolLightCtx`] is a zero-sized handle over them —
//! constructing one is free.
//!
//! ## Mapping to Isabelle/HOL
//!
//! `covalence-pure` plays the role of Isabelle/Pure: the meta-logic
//! with `prop`, meta-`⋀`, meta-`⟹`, meta-`≡`, plus the standard
//! inference rules (`assume`, `imp_intro/elim`, `all_intro/elim`,
//! `refl`/`trans`/`sym`, `cong_app`/`cong_abs`, `beta_conv`,
//! `eta_conv`, `eq_mp`, `inst_tfree`).
//!
//! `covalence-hol` plays the role of Isabelle/HOL: HOL as a *theory*
//! built on top of the meta-logic. Standard Isabelle/HOL ships with:
//!
//! - `bool` as a separate type (we encode it as `TyConObs(Bool_obs, "bool", [])`).
//! - `Trueprop : bool ⇒ prop` as the explicit coercion (our [`HolLight::Trueprop`]).
//! - HOL `=` as a constant at `'a ⇒ 'a ⇒ bool` (our [`HolLight::Eq`]).
//! - One bridge axiom — `eq_reflection : (x = y) ⟹ (x ≡ y)` — that
//!   we mirror exactly in [`HolLightCtx::eq_reflection_axiom`].
//!
//! From the `eq_reflection` axiom plus Pure's primitives, every HOL
//! Light rule derives the way Isabelle does it. The audit-trail
//! discipline matches HOL Light's: any HOL theorem that relies on
//! `eq_reflection` carries it in the hypothesis set.
//!
//! ## Tarski-T encoding
//!
//! HOL judgements live in Pure as `⊢_Pure Trueprop p`. A HOL theorem
//! `Γ ⊢_HOL p` (with `p : bool` and each `h ∈ Γ : bool`) is the Pure
//! theorem
//!
//! ```text
//! {eq_reflection, ETA, SELECT, INFINITY, …} ∪ {Trueprop h | h ∈ Γ}
//!     ⊢_Pure Trueprop p
//! ```
//!
//! Pure's hypothesis set carries every axiom the conclusion depends
//! on (eq_reflection plus whichever standard HOL axioms apply) and
//! the HOL hypotheses lifted through Trueprop.
//!
//! ## The 10 HOL Light rules
//!
//! Status: all 10 derive via `eq_reflection` plus Pure's primitives.
//! The (forthcoming) `PureHol` kernel adapter wires each one up.
//!
//! | HOL Light rule    | Derived from                        |
//! |-------------------|-------------------------------------|
//! | REFL              | Pure `refl` + eq_reflection (bwd)   |
//! | TRANS             | eq_reflection (fwd) + Pure `trans` + eq_reflection (bwd) |
//! | MK_COMB           | eq_reflection (fwd) + Pure `cong_app` + eq_reflection (bwd) |
//! | ABS               | eq_reflection (fwd) + Pure `cong_abs` (checks "x not free in hyps") + eq_reflection (bwd) |
//! | BETA              | Pure `beta_conv` + eq_reflection (bwd) |
//! | ASSUME            | Pure `assume` on `Trueprop p` directly |
//! | EQ_MP at bool     | eq_reflection (fwd) + Pure `eq_mp` |
//! | DEDUCT_ANTISYM    | Pure `imp_intro` + iff_def (defined HOL constant) |
//! | INST              | Pure `all_intro` (checks "x not free in hyps") + `all_elim` |
//! | INST_TYPE         | Pure `inst_tfree` directly          |
//!
//! Pure's primitives already enforce the hypothesis-side-conditions
//! the conditioned HOL Light rules require (ABS, INST), and apply
//! substitutions uniformly across the hypothesis set (INST, INST_TYPE).
//! There's no soundness gap to engineer around.
//!
//! ## Why we don't use the "axiomless" approach
//!
//! An earlier version of this module attempted to avoid the
//! eq_reflection axiom by recognising HOL-Light-derivable shapes
//! directly in the [`covalence_core::ObsTrue`] and
//! [`covalence_core::ObsImp`] policies. The pattern looked appealing
//! — fewer hypotheses, no axiom to thread through — but the analysis
//! showed that ABS and INST cannot soundly fit. The pattern was
//! removed. See the project's `audit` commit for the analysis.

use std::sync::LazyLock;

use covalence_core::{HolOp, Term, TermKind, Thm, Type};

// ============================================================================
// HOL bridge axioms (still postulated)
// ============================================================================
//
// `Bool`, `Eq`, `True`, `False`, `Imp`, `Not`, `And`, `Or`, `Iff`,
// `Forall`, `Exists`, `Select`, `Trueprop` are no longer observer
// objects — they are first-class kernel atoms (`Type::bool()`,
// `Term::Bool(_)`, `Term::HolOp(_, _)`). The HOL bridge axioms
// below stay postulated as lazy theorems for now.

/// `⋀x y : 'a. Trueprop (Eq x y) ≡ (x ≡ y)` — the polymorphic
/// `eq_reflection` axiom. Built lazily once via `Thm::assume`, reused
/// process-wide. See [`HolLightCtx::eq_reflection_axiom`].
static EQ_REFLECTION_AXIOM: LazyLock<Thm> = LazyLock::new(build_eq_reflection_axiom);

/// `⋀P Q : bool. (Trueprop P ⟹ Trueprop Q) ⟹ (Trueprop Q ⟹ Trueprop P)
///   ⟹ Trueprop (Eq[bool] P Q)` — the iff-introduction axiom
/// (Isabelle's `iffI`). Built lazily once. See
/// [`HolLightCtx::iff_intro_axiom`].
static IFF_INTRO_AXIOM: LazyLock<Thm> = LazyLock::new(build_iff_intro_axiom);

/// `⋀P : 'a → bool. (⋀x:'a. Trueprop (P x)) ≡ Trueprop (Forall P)`
/// — bridges Pure's meta-`⋀` and HOL's object-level `∀`. The
/// counterpart of `eq_reflection` for universal quantification.
static FORALL_REFLECTION_AXIOM: LazyLock<Thm> = LazyLock::new(build_forall_reflection_axiom);

/// `⋀P Q : bool. (Trueprop P ⟹ Trueprop Q) ≡ Trueprop (P ⟹ Q)`
/// — bridges Pure's meta-`⟹` and HOL's object-level `⟹`. The
/// counterpart of `eq_reflection` for implication.
static IMP_REFLECTION_AXIOM: LazyLock<Thm> = LazyLock::new(build_imp_reflection_axiom);

// ============================================================================
// HolLightCtx — zero-sized handle on the process-global HOL primitives
// ============================================================================

/// Zero-sized handle on the process-global HOL Light primitives.
/// Constructing one is free — there are no fields. Methods delegate
/// to the module-level `LazyLock` statics. Two `HolLightCtx` values
/// are interchangeable.
#[derive(Clone, Copy, Debug, Default)]
pub struct HolLightCtx;

impl HolLightCtx {
    /// Construct a handle. Free; no allocation.
    pub fn new() -> Self {
        Self
    }

    // ---- HOL types ----

    /// HOL `bool` — the cached canonical `Type::bool()` instance.
    /// HOL is folded into the kernel, so `bool` is a regular kernel
    /// type, not a `TyConObs` over an observer identity.
    pub fn bool_type(&self) -> Type {
        Type::bool()
    }

    /// Pure function type α → β. HOL doesn't add a new function-type
    /// constructor; we re-use Pure's `Fun`.
    pub fn fun_type(&self, a: Type, b: Type) -> Type {
        Type::fun(a, b)
    }

    // ---- HOL constants — now folded into core via TermKind::HolOp ----

    /// HOL `=` instantiated at `α → α → bool`.
    pub fn eq_at(&self, alpha: Type) -> Term {
        let ty = Type::fun(alpha.clone(), Type::fun(alpha, self.bool_type()));
        Term::hol_op(HolOp::Eq, ty)
    }

    /// `t = u : bool`, given `t` and `u` of the same type α. Errors
    /// if `t` is ill-typed.
    pub fn mk_eq(&self, lhs: Term, rhs: Term) -> Result<Term, covalence_core::Error> {
        let alpha = lhs.type_of()?;
        let eq = self.eq_at(alpha);
        Ok(Term::app(Term::app(eq, lhs), rhs))
    }

    /// HOL `T : bool` — a kernel literal.
    pub fn t(&self) -> Term {
        Term::bool_lit(true)
    }

    /// HOL `F : bool` — a kernel literal.
    pub fn f(&self) -> Term {
        Term::bool_lit(false)
    }

    fn bool_binop_ty(&self) -> Type {
        let b = self.bool_type();
        Type::fun(b.clone(), Type::fun(b.clone(), b))
    }

    /// HOL `==>` at `bool → bool → bool`.
    pub fn imp_op(&self) -> Term {
        Term::hol_op(HolOp::Imp, self.bool_binop_ty())
    }
    /// HOL `p ==> q`.
    pub fn mk_imp(&self, p: Term, q: Term) -> Term {
        Term::app(Term::app(self.imp_op(), p), q)
    }

    /// HOL `~` at `bool → bool`.
    pub fn not_op(&self) -> Term {
        let b = self.bool_type();
        Term::hol_op(HolOp::Not, Type::fun(b.clone(), b))
    }
    /// HOL `~ p`.
    pub fn mk_not(&self, p: Term) -> Term {
        Term::app(self.not_op(), p)
    }

    /// HOL `/\` at `bool → bool → bool`.
    pub fn and_op(&self) -> Term {
        Term::hol_op(HolOp::And, self.bool_binop_ty())
    }
    /// HOL `p /\ q`.
    pub fn mk_and(&self, p: Term, q: Term) -> Term {
        Term::app(Term::app(self.and_op(), p), q)
    }

    /// HOL `\/` at `bool → bool → bool`.
    pub fn or_op(&self) -> Term {
        Term::hol_op(HolOp::Or, self.bool_binop_ty())
    }
    /// HOL `p \/ q`.
    pub fn mk_or(&self, p: Term, q: Term) -> Term {
        Term::app(Term::app(self.or_op(), p), q)
    }

    /// HOL `<=>` at `bool → bool → bool`.
    pub fn iff_op(&self) -> Term {
        Term::hol_op(HolOp::Iff, self.bool_binop_ty())
    }
    /// HOL `p <=> q`.
    pub fn mk_iff(&self, p: Term, q: Term) -> Term {
        Term::app(Term::app(self.iff_op(), p), q)
    }

    /// HOL `∀` at `(α → bool) → bool`.
    pub fn forall_at(&self, alpha: Type) -> Term {
        let pred = Type::fun(alpha, self.bool_type());
        Term::hol_op(HolOp::Forall, Type::fun(pred, self.bool_type()))
    }
    /// HOL `∀x:α. body` — `Forall (λx:α. body)`.
    pub fn mk_forall(&self, hint: &str, alpha: Type, body: Term) -> Term {
        let lambda = Term::abs(hint, alpha.clone(), body);
        Term::app(self.forall_at(alpha), lambda)
    }

    /// HOL `∃` at `(α → bool) → bool`.
    pub fn exists_at(&self, alpha: Type) -> Term {
        let pred = Type::fun(alpha, self.bool_type());
        Term::hol_op(HolOp::Exists, Type::fun(pred, self.bool_type()))
    }
    /// HOL `∃x:α. body` — `Exists (λx:α. body)`.
    pub fn mk_exists(&self, hint: &str, alpha: Type, body: Term) -> Term {
        let lambda = Term::abs(hint, alpha.clone(), body);
        Term::app(self.exists_at(alpha), lambda)
    }

    /// HOL `ε` (Hilbert's choice) at `(α → bool) → α`.
    pub fn select_at(&self, alpha: Type) -> Term {
        let pred = Type::fun(alpha.clone(), self.bool_type());
        Term::hol_op(HolOp::Select, Type::fun(pred, alpha))
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
        Term::hol_op(HolOp::Trueprop, Type::fun(self.bool_type(), Type::prop()))
    }

    /// `Trueprop p` — wrap a HOL bool term as a Pure prop. Errors if
    /// `p` is not bool-typed.
    pub fn mk_trueprop(&self, p: Term) -> Result<Term, covalence_core::Error> {
        let p_ty = p.type_of()?;
        if p_ty != self.bool_type() {
            return Err(covalence_core::Error::TypeMismatch {
                expected: self.bool_type(),
                got: p_ty,
            });
        }
        Ok(Term::app(self.trueprop(), p))
    }

    // ---- Identity check helpers ----

    /// `true` iff `t` is the HOL `T` literal.
    pub fn is_true(&self, t: &Term) -> bool {
        matches!(t.kind(), TermKind::Bool(true))
    }

    /// `true` iff `t` is the HOL `F` literal.
    pub fn is_false(&self, t: &Term) -> bool {
        matches!(t.kind(), TermKind::Bool(false))
    }

    /// `true` iff `t` is the HOL `Trueprop` constant (the bare
    /// `bool → prop` operator leaf).
    pub fn is_trueprop(&self, t: &Term) -> bool {
        matches!(t.kind(), TermKind::HolOp(HolOp::Trueprop, _))
    }

    // ========================================================================
    // The eq_reflection axiom (Isabelle/HOL bridge)
    // ========================================================================

    /// The polymorphic `eq_reflection` axiom — the bridge between HOL
    /// bool-equality (`Eq`) and Pure meta-equality (`≡`):
    ///
    /// ```text
    /// ⋀x y : 'a. Trueprop (Eq x y) ≡ (x ≡ y)
    /// ```
    ///
    /// Same axiom name and shape Isabelle/HOL ships. From this axiom
    /// plus Pure's existing primitives (`refl`, `trans`, `sym`,
    /// `cong_app`, `cong_abs`, `beta_conv`, `eq_mp`, `assume`,
    /// `imp_intro`, `imp_elim`, `all_intro`, `all_elim`, `inst_tfree`)
    /// you can derive every HOL Light rule.
    ///
    /// ## Use pattern
    ///
    /// This is a [`Thm::assume`] axiom — it has itself as a single
    /// hypothesis, and every theorem derived from it carries that
    /// hypothesis. Like ETA / SELECT / INFINITY in HOL Light, the
    /// axiom-as-hypothesis is the audit trail.
    ///
    /// To instantiate at a specific type α:
    ///
    /// ```ignore
    /// let axiom = ctx.eq_reflection_axiom();
    /// let axiom_at_bool = axiom.inst_tfree("a", ctx.bool_type())?;
    /// ```
    ///
    /// Forward direction (HOL `=` → Pure `≡`):
    ///
    /// ```text
    /// axiom_at_bool                                  // ⊢ ⋀x y. Trueprop (Eq x y) ≡ (x ≡ y)
    ///     .all_elim(a)?                              // ⊢ ⋀y. Trueprop (Eq a y) ≡ (a ≡ y)
    ///     .all_elim(b)?                              // ⊢ Trueprop (Eq a b) ≡ (a ≡ b)
    ///     .eq_mp(source_thm)?                        // ⊢ a ≡ b   (given source: ⊢ Trueprop (Eq a b))
    /// ```
    ///
    /// Backward direction (Pure `≡` → HOL `=`):
    ///
    /// ```text
    /// axiom_at_bool.all_elim(a)?.all_elim(b)?        // ⊢ Trueprop (Eq a b) ≡ (a ≡ b)
    ///     .sym()?                                    // ⊢ (a ≡ b) ≡ Trueprop (Eq a b)
    ///     .eq_mp(meta_eq_thm)?                       // ⊢ Trueprop (Eq a b)
    /// ```
    pub fn eq_reflection_axiom(&self) -> Thm {
        (*EQ_REFLECTION_AXIOM).clone()
    }

    /// The polymorphic-in-nothing `iff_intro` axiom (Isabelle's
    /// `iffI`):
    ///
    /// ```text
    /// ⋀P Q : bool.
    ///   (Trueprop P ⟹ Trueprop Q) ⟹
    ///   (Trueprop Q ⟹ Trueprop P) ⟹
    ///   Trueprop (Eq[bool] P Q)
    /// ```
    ///
    /// Drives `DEDUCT_ANTISYM_RULE`: from `A1 ⊢ Trueprop P` and
    /// `A2 ⊢ Trueprop Q`, `imp_intro` each direction to produce
    /// the two antecedents and then chain `all_elim` + `imp_elim`
    /// through this axiom to land at `Trueprop (P = Q)`.
    pub fn iff_intro_axiom(&self) -> Thm {
        (*IFF_INTRO_AXIOM).clone()
    }

    /// The polymorphic `forall_reflection` axiom — bridges Pure's
    /// meta-universal `⋀` and HOL's object-level `∀`:
    ///
    /// ```text
    /// ⋀P : 'a → bool. (⋀x:'a. Trueprop (P x)) ≡ Trueprop (Forall P)
    /// ```
    ///
    /// Used to convert between meta-level proofs (via Pure
    /// `all_intro`/`all_elim`) and object-level HOL `∀` reasoning.
    /// Forward direction (meta → object): `all_elim P`, then
    /// `eq_mp` with `⋀x. Trueprop (P x)` produces
    /// `Trueprop (Forall P)`. Backward direction symmetric via
    /// `sym`.
    pub fn forall_reflection_axiom(&self) -> Thm {
        (*FORALL_REFLECTION_AXIOM).clone()
    }

    /// The `imp_reflection` axiom — bridges Pure's meta-implication
    /// `⟹` and HOL's object-level `⟹`:
    ///
    /// ```text
    /// ⋀P Q : bool. (Trueprop P ⟹ Trueprop Q) ≡ Trueprop (P ⟹ Q)
    /// ```
    ///
    /// Used to convert between meta-level discharge (via Pure
    /// `imp_intro`/`imp_elim`) and object-level HOL implication
    /// reasoning. Forward: `eq_mp` with a meta-implication on the
    /// LHS gives a Trueprop-wrapped HOL implication. Backward
    /// symmetric.
    pub fn imp_reflection_axiom(&self) -> Thm {
        (*IMP_REFLECTION_AXIOM).clone()
    }
}

/// Build `eq_reflection` — called once, lazily, by the
/// `EQ_REFLECTION_AXIOM` static initialiser.
fn build_eq_reflection_axiom() -> Thm {
    let ctx = HolLightCtx;
    let alpha = Type::tfree("a");
    // Inside two ⋀-binders: x = Bound(1), y = Bound(0) (both : 'a).
    let x = Term::bound(1);
    let y = Term::bound(0);
    // HOL: x = y  (at 'a, returns bool)
    let eq_at_alpha = ctx.eq_at(alpha.clone());
    let hol_eq_x_y = Term::app(Term::app(eq_at_alpha, x.clone()), y.clone());
    // Trueprop (x = y)  (returns prop)
    let trueprop_hol_eq = Term::app(ctx.trueprop(), hol_eq_x_y);
    // Pure: x ≡ y  (at 'a, returns prop)
    let pure_eq_x_y = Term::eq(x, y);
    // Trueprop (Eq x y) ≡ (x ≡ y)  (meta-eq between two props, returns prop)
    let body = Term::eq(trueprop_hol_eq, pure_eq_x_y);
    // Wrap in two ⋀-binders.
    let inner = Term::all("y", alpha.clone(), body);
    let outer = Term::all("x", alpha, inner);
    Thm::assume(outer).expect("eq_reflection_axiom: well-typed by construction")
}

/// Build `iff_intro` — called once, lazily, by the
/// `IFF_INTRO_AXIOM` static initialiser.
fn build_iff_intro_axiom() -> Thm {
    let ctx = HolLightCtx;
    let bool_ty = ctx.bool_type();
    // Inside two ⋀-binders: P = Bound(1), Q = Bound(0) (both : bool).
    let p = Term::bound(1);
    let q = Term::bound(0);

    let trueprop = ctx.trueprop();
    let eq_at_bool = ctx.eq_at(bool_ty.clone());

    // Trueprop P, Trueprop Q.
    let tp_p = Term::app(trueprop.clone(), p.clone());
    let tp_q = Term::app(trueprop.clone(), q.clone());
    // HOL Eq[bool] P Q.
    let hol_eq_p_q = Term::app(Term::app(eq_at_bool, p), q);
    // Trueprop (Eq[bool] P Q).
    let tp_eq = Term::app(trueprop, hol_eq_p_q);

    // (Trueprop P ⟹ Trueprop Q) ⟹ (Trueprop Q ⟹ Trueprop P) ⟹ Trueprop (P = Q)
    let body = Term::imp(
        Term::imp(tp_p.clone(), tp_q.clone()),
        Term::imp(Term::imp(tp_q, tp_p), tp_eq),
    );
    let inner = Term::all("q", bool_ty.clone(), body);
    let outer = Term::all("p", bool_ty, inner);
    Thm::assume(outer).expect("iff_intro_axiom: well-typed by construction")
}

/// Build `forall_reflection` — called once, lazily.
///
/// Under outer ⋀P (where P : 'a → bool, Bound(0) at this level):
/// - Left side: `⋀x:'a. Trueprop (P x)` — inner Pure ⋀, body uses
///   Bound(0) for x, Bound(1) for P (one binder up from the inner ⋀).
/// - Right side: `Trueprop (Forall P)` — Bound(0) is P here.
fn build_forall_reflection_axiom() -> Thm {
    let ctx = HolLightCtx;
    let alpha = Type::tfree("a");
    let bool_ty = ctx.bool_type();
    let pred_ty = Type::fun(alpha.clone(), bool_ty);
    let trueprop = ctx.trueprop();

    // Inside inner ⋀x: P = Bound(1), x = Bound(0).
    let inner_body = Term::app(
        trueprop.clone(),
        Term::app(Term::bound(1), Term::bound(0)),
    );
    let inner_all = Term::all("x", alpha.clone(), inner_body);

    // Right: Trueprop (Forall P), with P = Bound(0).
    let forall_at = ctx.forall_at(alpha);
    let forall_p = Term::app(forall_at, Term::bound(0));
    let tp_forall_p = Term::app(trueprop, forall_p);

    // Pure meta-eq.
    let body = Term::eq(inner_all, tp_forall_p);
    let outer = Term::all("P", pred_ty, body);
    Thm::assume(outer).expect("forall_reflection_axiom: well-typed by construction")
}

/// Build `imp_reflection` — called once, lazily.
///
/// Under outer ⋀p ⋀q (p = Bound(1), q = Bound(0)):
/// - Left: `Trueprop p ⟹ Trueprop q` (Pure meta-imp).
/// - Right: `Trueprop (p ⟹ q)` (HOL imp wrapped in Trueprop).
fn build_imp_reflection_axiom() -> Thm {
    let ctx = HolLightCtx;
    let bool_ty = ctx.bool_type();
    let trueprop = ctx.trueprop();
    let imp_op = ctx.imp_op();

    let p = Term::bound(1);
    let q = Term::bound(0);

    let tp_p = Term::app(trueprop.clone(), p.clone());
    let tp_q = Term::app(trueprop.clone(), q.clone());
    let left = Term::imp(tp_p, tp_q);

    // HOL imp at bool: (imp p) q.
    let hol_imp_p_q = Term::app(Term::app(imp_op, p), q);
    let right = Term::app(trueprop, hol_imp_p_q);

    let body = Term::eq(left, right);
    let inner = Term::all("q", bool_ty.clone(), body);
    let outer = Term::all("p", bool_ty, inner);
    Thm::assume(outer).expect("imp_reflection_axiom: well-typed by construction")
}

// `HolLight` enum + `IsHolLight` marker trait removed:
// HOL primitives are now first-class kernel atoms (`Type::bool()`,
// `Term::Bool(_)`, `Term::HolOp(_, _)`), not an observer family.
