//! **L3 — the reified Metamath-expression algebra** (`MmAlgebra`), the
//! insulation boundary of the trait tower
//! (`notes/vibes/logics/derivation-system-interp.md`).
//!
//! ## What this abstracts
//!
//! A *reified Metamath-expression algebra* over an (opaque) HOL carrier `Φ`:
//! encode a symbol/app tree into a `Φ`-term (`sym`/`app`/`encode`), build a
//! structural translation `σ : Φ → Φ` from a leaf renaming (`structural_sigma`),
//! and expose `σ`'s per-node homomorphism witness (`sigma_app_hom`). These are
//! *exactly* the methods the transport layer ([`super::transport_db`]) consumes,
//! and BOTH backends provide them with the SAME signature — that is what makes
//! the insulation acid-test real (a trait with one impl proves nothing).
//!
//! ## Two backends behind one interface
//!
//! - [`FreeAlgebra`] — the *recursor-free free algebra* of
//!   [`super::mm_database`]: `Φ = nat`, `sym = leaf(db, tok)`, `app = concat`,
//!   `encode = Parser::encode_expr`. It genuinely implements `MmAlgebra`, but its
//!   `structural_sigma` is an OPAQUE whole-judgement wrap (there is no recursor
//!   over `concat`) and `sigma_app_hom` returns [`covalence_core::Error`] —
//!   `caps().structural == false`. This is the honest *degenerate* second impl.
//! - [`MmExprAlgebra`] — the *genuine inductive* `MmExpr := sym(nat) | app(Rec,
//!   Rec)`, realized by [`ImpredicativeBackend`]. Its `structural_sigma` is the
//!   catamorphism `λt. rec_app([λc. sym(leaf_map c), app], t)`, and
//!   `sigma_app_hom` is proved DIRECTLY from the `comp` computation law (no
//!   induction) — `caps().structural == true`. The recursor surface it uniquely
//!   provides lives on the companion [`MmRecursor`] trait (the free algebra
//!   CANNOT implement it, so it stays off the core trait).
//!
//! ## Object-safety (a load-bearing design decision)
//!
//! `MmAlgebra` returns bare [`Term`] / [`Thm`] (concrete `NativeHol` core types,
//! NOT associated types), and `Φ` is a runtime `fn phi(&self) -> Type` VALUE
//! (both carriers *are* `Type`), NOT an associated type. This keeps `&dyn
//! MmAlgebra` object-safe — needed by
//! [`super::interp::DerivationSystem::algebra`]. `MmRecursor` in a separate trait
//! keeps the object-safe core clean.
//!
//! ## Honest scope
//!
//! What LANDS: the trait + two impls + the `MmExpr` bundle + the structural σ +
//! the app-homomorphism-by-`comp` + Wf-preservation-by-induction + the
//! non-vacuity witness + the insulation acid-test. What DEFERS (see
//! the generated open-work index): firing [`super::transport_db::transport`] with a structural
//! `MmExpr` σ across two REAL rule sets — that needs re-encoding the live
//! `mm_database`/K carrier from `Φ=nat` onto the Church `MmExpr` carrier
//! (`check_same_carrier` rejects the mismatch), a carrier migration off the
//! additive path.

use covalence_core::{Result, Term, Type, subst};
use covalence_hol_eval::EvalThm as Thm;

use crate::init::ext::TermExt;
use crate::init::inductive::ImpredicativeBackend;
use crate::init::inductive::hol::NativeHol;
use crate::metamath::{Database, Expr};
use covalence_inductive::{
    ArgSort, CtorSpec, InductiveBackend, InductiveError, InductiveSpec, InductiveTheory,
};

use super::mm_database::{self, Parser};

/// Capability flags for an [`MmAlgebra`] impl — mirrors
/// [`covalence_inductive::BackendCaps`] (`theory.rs`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AlgebraCaps {
    /// Does this impl deliver a real structural recursor + `σ`-homomorphism?
    /// [`FreeAlgebra`] = `false`; [`MmExprAlgebra`] = `true`.
    pub structural: bool,
}

/// **The reified Metamath-expression algebra** — the L3 insulation boundary.
///
/// Encode symbol/app trees into an opaque HOL carrier `Φ`, build a structural
/// translation `σ : Φ → Φ`, and witness its per-node homomorphism. Everything
/// above L3 ([`super::transport_db`], [`super::interp`]) names ONLY these methods
/// — swapping the concrete impl changes only which `sym`/`app`/`structural_sigma`
/// build the encoding, never a higher-layer signature.
pub trait MmAlgebra {
    /// The opaque HOL carrier `Φ` these expressions encode into (`nat` for
    /// [`FreeAlgebra`]; the Church `MmExpr` carrier for [`MmExprAlgebra`]).
    fn phi(&self) -> Type;

    /// A **symbol leaf** from a token code. [`FreeAlgebra`]: `leaf(db, tok)`.
    /// [`MmExprAlgebra`]: `sym code` (`code : nat`).
    fn sym(&self, code: &Term) -> Result<Term>;

    /// A **binary node**. [`FreeAlgebra`]: `concat(a, b)`. [`MmExprAlgebra`]:
    /// `app a b`.
    fn app(&self, a: &Term, b: &Term) -> Result<Term>;

    /// Encode a statement body under a database's grammar into a `Φ`-term — the
    /// ONE entry point the frontends use. [`FreeAlgebra`]:
    /// `Parser::new(db).encode_expr(e)`. [`MmExprAlgebra`]: parse then fold
    /// `sym`/`app` (a `Φ=nat` tree re-lifted onto the `MmExpr` carrier).
    fn encode(&self, db: &Database, e: &Expr) -> Result<Term>;

    /// Build a **structural translation** `σ : Φ → Φ` renaming every leaf via
    /// `leaf_map : nat → nat` and rebuilding every node with `app`.
    /// [`FreeAlgebra`]: an OPAQUE identity wrap (no recursor over `concat`) — a
    /// genuine second impl of THIS signature, but degenerate. [`MmExprAlgebra`]:
    /// the catamorphism `λt. rec_app([λc. sym(leaf_map c), app], t)`.
    fn structural_sigma(&self, leaf_map: &Term) -> Result<Term>;

    /// The **σ-homomorphism lemma** `⊢ ∀X Y. σ (app X Y) = app (σ X) (σ Y)` —
    /// the per-node simulation obligation transport consumes. [`FreeAlgebra`]:
    /// [`Err`] (no recursor over `concat`). [`MmExprAlgebra`]: proved by
    /// `comp(steps, 1)` + β (UNCONDITIONAL — no `Wf` guard, hence non-vacuous).
    fn sigma_app_hom(&self, sigma: &Term) -> Result<Thm>;

    /// Capability: does this impl deliver a real structural homomorphism?
    fn caps(&self) -> AlgebraCaps;
}

/// The **recursor surface** — [`MmExprAlgebra`] ONLY. The free algebra cannot
/// honestly implement a recursor over `concat`, so these methods stay OFF the
/// core [`MmAlgebra`] trait (putting them there would force the free algebra to
/// be a liar). This split is what makes the core trait genuinely have two impls
/// of one signature.
pub trait MmRecursor: MmAlgebra {
    /// `rec_app(steps, t)` — the catamorphic recursor applied.
    fn rec_app(&self, steps: &[Term], t: &Term) -> Result<Term>;
    /// `comp(steps, i)` — the computation law for constructor `i`.
    fn comp(&self, steps: &[Term], i: usize) -> Result<Thm>;
    /// `induct(motive, cases)` — membership-relativized structural induction.
    fn induct(&self, motive: &Term, cases: Vec<Thm>) -> Result<Thm>;
    /// The `Wf` membership predicate `Φ → bool`.
    fn mem(&self) -> Term;
    /// `mem_ctor(i, args, rec_mems)` — constructor membership.
    fn mem_ctor(&self, i: usize, args: &[Term], rec_mems: Vec<Thm>) -> Result<Thm>;
}

// ============================================================================
// FreeAlgebra — the recursor-free `Φ=nat` free algebra (degenerate σ)
// ============================================================================

/// The [`super::mm_database`] free-term algebra as an [`MmAlgebra`]: `Φ = nat`,
/// `concat`/`leaf`, `Parser::encode_expr`. Pure delegation — ZERO new theorems.
/// Its `structural_sigma` is opaque and `sigma_app_hom` is unsupported
/// (`caps().structural == false`): the honest degenerate second impl.
pub struct FreeAlgebra<'a>(pub &'a Database);

impl<'a> MmAlgebra for FreeAlgebra<'a> {
    fn phi(&self) -> Type {
        mm_database::phi_ty()
    }

    fn sym(&self, code: &Term) -> Result<Term> {
        // A leaf is a `Φ=nat` token. We accept an arbitrary code term at `nat`
        // as an uninterpreted leaf: the free algebra's leaves ARE `nat` frees /
        // constants, and any `nat` term stands for one. This keeps the SAME
        // `sym(code)` interface as `MmExprAlgebra` while staying degenerate.
        if code.type_of()? != mm_database::phi_ty() {
            return Err(covalence_core::Error::ConnectiveRule(
                "FreeAlgebra::sym: leaf code must be a nat term".into(),
            ));
        }
        Ok(code.clone())
    }

    fn app(&self, a: &Term, b: &Term) -> Result<Term> {
        mm_database::concat_node(a.clone(), b.clone())
    }

    fn encode(&self, db: &Database, e: &Expr) -> Result<Term> {
        Parser::new(db).encode_expr(e)
    }

    fn structural_sigma(&self, _leaf_map: &Term) -> Result<Term> {
        // OPAQUE identity wrap: with no recursor over `concat`, the free algebra
        // cannot descend the tree to rename leaves. The honest degenerate σ is
        // the identity `λx:Φ. x` — a real term of type `Φ → Φ` (so higher layers
        // that only need `σ`'s TYPE still work), but `structural == false` flags
        // that it carries no homomorphism.
        let x = Term::free("__fa_x", self.phi());
        Ok(Term::abs(self.phi(), subst::close(&x, "__fa_x")))
    }

    fn sigma_app_hom(&self, _sigma: &Term) -> Result<Thm> {
        Err(covalence_core::Error::ConnectiveRule(
            "FreeAlgebra::sigma_app_hom: unsupported — the recursor-free free \
             algebra has no catamorphism over `concat`; use MmExprAlgebra"
                .into(),
        ))
    }

    fn caps(&self) -> AlgebraCaps {
        AlgebraCaps { structural: false }
    }
}

// ============================================================================
// MmExprAlgebra — the genuine inductive `MmExpr := sym(nat) | app(Rec, Rec)`
// ============================================================================

/// The inductive-`MmExpr` spec: `sym(code: nat) | app(l: Rec, r: Rec)`. Shape
/// identical to the `btree` conformance spec the Church backend already passes.
pub fn mmexpr_spec() -> InductiveSpec<Type> {
    InductiveSpec::new(
        "MmExpr",
        vec![
            CtorSpec::new("sym", [("code", ArgSort::Ext(Type::nat()))]),
            CtorSpec::new("app", [("l", ArgSort::Rec), ("r", ArgSort::Rec)]),
        ],
    )
}

/// The genuine inductive `MmExpr` algebra: `sym`/`app` are the church-realized
/// constructors, `structural_sigma` is a catamorphism through `rec_app`, and
/// `sigma_app_hom` is proved from the `comp` law. `caps().structural == true`.
pub struct MmExprAlgebra {
    th: InductiveTheory<NativeHol>,
}

impl MmExprAlgebra {
    /// Realize the `MmExpr` bundle via [`ImpredicativeBackend`].
    pub fn new() -> Result<Self> {
        let th = ImpredicativeBackend::new()
            .realize(&NativeHol, &mmexpr_spec())
            .map_err(ind_err)?;
        Ok(MmExprAlgebra { th })
    }

    /// The underlying theory bundle (carrier, mem, ctors, facts).
    pub fn theory(&self) -> &InductiveTheory<NativeHol> {
        &self.th
    }

    /// The `sym` constructor term (`nat → MmExpr⟨'r⟩`).
    pub fn sym_ctor(&self) -> &Term {
        &self.th.ctors[0]
    }

    /// The `app` constructor term (`MmExpr⟨'r⟩ → MmExpr⟨'r⟩ → MmExpr⟨'r⟩`).
    pub fn app_ctor(&self) -> &Term {
        &self.th.ctors[1]
    }

    /// The backend's fresh result-type-variable name (default `"r"`).
    fn rvar(&self) -> &str {
        "r"
    }

    /// The **observation carrier** `Φ_obs := MmExpr⟨'r := nat⟩` — the codomain of
    /// the structural fold: the carrier with its polymorphic fold slot pinned to a
    /// concrete `nat`, a monomorphic HOL type (no free `'r`). A catamorphism *to
    /// the polymorphic carrier itself* is not expressible at rank 1 (an
    /// endomorphism `C → C` would need `C = MmExpr⟨C⟩`, an infinite type; and
    /// `comp`'s result type must not mention `'r`). Folding to `Φ_obs` instead is
    /// the plan's risk-1 fallback (state σ at a fixed observation `'r`, exactly as
    /// `church.rs`'s `injective`/`distinct` observe at a chosen `'r`).
    ///
    /// The structural fold has type `σ : Φ_dom → Φ_obs` where `Φ_dom =
    /// MmExpr⟨Φ_obs⟩` ([`Self::phi_dom`]) — the carrier at `'r := Φ_obs`, whose
    /// handler slots are `nat → Φ_obs` / `Φ_obs → Φ_obs → Φ_obs` so the fold to
    /// `Φ_obs` typechecks. Both `Φ_dom` and `Φ_obs` are "reified MmExpr trees";
    /// the domain merely carries one extra observation layer.
    pub fn phi_obs(&self) -> Type {
        subst::subst_tfree_in_type(&self.th.ty, self.rvar(), &Type::nat())
    }

    /// The **fold domain** `Φ_dom := MmExpr⟨'r := Φ_obs⟩` — the carrier
    /// instantiated so a fold to `Φ_obs` typechecks (handlers `nat → Φ_obs`,
    /// `Φ_obs → Φ_obs → Φ_obs`). σ's binder is at `Φ_dom`.
    pub fn phi_dom(&self) -> Type {
        subst::subst_tfree_in_type(&self.th.ty, self.rvar(), &self.phi_obs())
    }

    /// `sym` at the observation instance `'r := nat`: `nat → Φ_obs`.
    fn sym_obs(&self) -> Term {
        subst::subst_tfree_in_term(self.sym_ctor(), self.rvar(), &Type::nat())
    }

    /// `app` at the observation instance `'r := nat`: `Φ_obs → Φ_obs → Φ_obs`.
    fn app_obs(&self) -> Term {
        subst::subst_tfree_in_term(self.app_ctor(), self.rvar(), &Type::nat())
    }

    /// `sym` / `app` at the fold DOMAIN instance `'r := Φ_obs` — the constructors
    /// that build the domain terms `X, Y : Φ_dom` the app-hom quantifies over.
    fn sym_dom(&self) -> Term {
        subst::subst_tfree_in_term(self.sym_ctor(), self.rvar(), &self.phi_obs())
    }
    fn app_dom(&self) -> Term {
        subst::subst_tfree_in_term(self.app_ctor(), self.rvar(), &self.phi_obs())
    }
    /// `app` at the domain carrier (public: the app-hom's INNER `app` builds
    /// `X, Y : Φ_dom` nodes).
    pub fn app_at_dom(&self, a: &Term, b: &Term) -> Result<Term> {
        self.app_dom().apply(a.clone())?.apply(b.clone())
    }
    /// `sym` at the domain carrier.
    pub fn sym_at_dom(&self, code: &Term) -> Result<Term> {
        self.sym_dom().apply(code.clone())
    }

    /// The catamorphism steps for a structural leaf-renaming σ, at the
    /// observation carrier `Φ_obs = MmExpr⟨nat⟩`:
    /// `step_sym := λc:nat. sym_obs (leaf_map c)`, `step_app := app_obs`.
    ///
    /// `step_app = app_obs` verbatim: `rec_app`'s app-step receives the RECURSIVE
    /// IMAGES `(σl, σr) : Φ_obs`, so rebuilding with `app_obs` IS the homomorphic
    /// re-fold. `step_sym`'s result type `Φ_obs` does NOT mention `'r`, so
    /// [`comp`] accepts it (result type read off `steps[0]`).
    fn sigma_steps(&self, leaf_map: &Term) -> Result<[Term; 2]> {
        // step_sym = λc:nat. sym_obs (leaf_map c)
        let c = Term::free("__mm_c", Type::nat());
        let mapped = leaf_map.clone().apply(c.clone())?; // leaf_map c : nat
        let sym_mapped = self.sym_obs().apply(mapped)?; // sym_obs (leaf_map c) : Φ_obs
        let step_sym = Term::abs(Type::nat(), subst::close(&sym_mapped, "__mm_c"));
        // step_app = app_obs  (Φ_obs → Φ_obs → Φ_obs)
        let step_app = self.app_obs();
        Ok([step_sym, step_app])
    }

    /// `app` at the observation carrier (public — the app-hom is stated with
    /// `Φ_obs` nodes, and consumers building X,Y for the hom need `app_obs`).
    pub fn app_at_obs(&self, a: &Term, b: &Term) -> Result<Term> {
        self.app_obs().apply(a.clone())?.apply(b.clone())
    }

    /// `sym` at the observation carrier.
    pub fn sym_at_obs(&self, code: &Term) -> Result<Term> {
        self.sym_obs().apply(code.clone())
    }
}

impl MmAlgebra for MmExprAlgebra {
    fn phi(&self) -> Type {
        // The working carrier is the OBSERVATION instance `MmExpr⟨nat⟩` — a
        // monomorphic HOL type (no free `'r`), so σ : Φ → Φ and higher layers see
        // a concrete carrier. The polymorphic `MmExpr⟨'r⟩` is an internal detail.
        self.phi_obs()
    }

    fn sym(&self, code: &Term) -> Result<Term> {
        // `sym` at the observation carrier, so `sym`/`app`/`encode` all land in Φ.
        self.sym_at_obs(code)
    }

    fn app(&self, a: &Term, b: &Term) -> Result<Term> {
        self.app_at_obs(a, b)
    }

    fn encode(&self, db: &Database, e: &Expr) -> Result<Term> {
        // Parse against the database grammar into the `Φ=nat` free-algebra tree,
        // then re-lift every `concat`/leaf node onto the `MmExpr` carrier via
        // `app`/`sym`. This is the carrier bridge: same free-term SHAPE, Church
        // carrier. (Leaves are `nat` frees/constants; `sym` wraps them.)
        let free = Parser::new(db).encode_expr(e)?;
        self.relift(&free)
    }

    fn structural_sigma(&self, leaf_map: &Term) -> Result<Term> {
        // σ := λt:Φ_dom. rec_app([step_sym, step_app], t)  —  σ : Φ_dom → Φ_obs.
        // `t` is bound at the FOLD DOMAIN carrier `Φ_dom = MmExpr⟨Φ_obs⟩`, whose
        // handler slots (`nat → Φ_obs`, `Φ_obs → Φ_obs → Φ_obs`) match `steps`, so
        // `rec_app`'s fold to `Φ_obs` typechecks. Folding to the polymorphic
        // carrier (an endomorphism) is not expressible at rank 1 — see `phi_obs`.
        let steps = self.sigma_steps(leaf_map)?;
        let dom = self.phi_dom();
        let t = Term::free("__mm_t", dom.clone());
        let body = self.th.facts.rec_app(&steps, &t).map_err(ind_err)?; // rec steps t : Φ_obs
        Ok(Term::abs(dom.clone(), subst::close(&body, "__mm_t")))
    }

    fn sigma_app_hom(&self, sigma: &Term) -> Result<Thm> {
        // The object-safe trait surface: prove the homomorphism for the σ AS
        // GIVEN. σ is `λt. rec_app(steps, t)`, so its body under the binder is the
        // application spine `(t' steps[0]) steps[1]`; we recover `steps` off it and
        // run the shared `comp`-based proof. Callers with the `leaf_map` in hand
        // may prefer the direct [`MmExprAlgebra::sigma_app_hom_of`].
        self.sigma_app_hom_from_sigma(sigma)
    }

    fn caps(&self) -> AlgebraCaps {
        AlgebraCaps { structural: true }
    }
}

impl MmRecursor for MmExprAlgebra {
    fn rec_app(&self, steps: &[Term], t: &Term) -> Result<Term> {
        self.th.facts.rec_app(steps, t).map_err(ind_err)
    }
    fn comp(&self, steps: &[Term], i: usize) -> Result<Thm> {
        self.th.facts.comp(steps, i).map_err(ind_err)
    }
    fn induct(&self, motive: &Term, cases: Vec<Thm>) -> Result<Thm> {
        self.th.facts.induct(motive, cases).map_err(ind_err)
    }
    fn mem(&self) -> Term {
        self.th.mem.clone()
    }
    fn mem_ctor(&self, i: usize, args: &[Term], rec_mems: Vec<Thm>) -> Result<Thm> {
        self.th.facts.mem_ctor(i, args, rec_mems).map_err(ind_err)
    }
}

impl MmExprAlgebra {
    /// Re-lift a `Φ=nat` free-algebra term onto the `MmExpr` carrier: `concat a
    /// b ↦ app (relift a) (relift b)`, any leaf `n:nat ↦ sym n`. Recursion on
    /// the term structure (a HOST-side fold — the RESULT is a genuine `MmExpr`
    /// term, no proof yet; it is the carrier-bridge for `encode`).
    fn relift(&self, t: &Term) -> Result<Term> {
        // A `concat a b` node is `((concat_fn a) b)`. Detect it by the head.
        if let Some((l, r)) = as_concat(t) {
            let a = self.relift(&l)?;
            let b = self.relift(&r)?;
            return self.app(&a, &b);
        }
        // Otherwise a leaf: wrap the `nat` term as `sym n`.
        self.sym(t)
    }

    /// The **leaf-map-parameterised** app-homomorphism (the honest entry):
    /// `⊢ ∀X Y. σ (app X Y) = app (σ X) (σ Y)` where `σ = structural_sigma(leaf_map)`.
    /// Proved DIRECTLY from `comp(steps, 1)` + β — no induction, unconditional
    /// (no `Wf` guard), hence non-vacuous.
    pub fn sigma_app_hom_of(&self, leaf_map: &Term) -> Result<Thm> {
        let steps = self.sigma_steps(leaf_map)?;
        let sigma = self.structural_sigma(leaf_map)?;
        self.prove_app_hom(&steps, &sigma)
    }

    /// The trait-surface [`MmAlgebra::sigma_app_hom`]: rebuild the steps by
    /// peeling `σ`'s `rec_app` body. Since `σ = λt. rec steps t`, its body under
    /// the binder is `t steps[0] steps[1]` (the fold). We recover `steps` from
    /// that application spine.
    fn sigma_app_hom_from_sigma(&self, sigma: &Term) -> Result<Thm> {
        let steps = self.recover_steps(sigma)?;
        self.prove_app_hom(&steps, sigma)
    }

    /// Recover `[step_sym, step_app]` from a `σ = λt. rec_app(steps, t)` term.
    /// `rec_app(steps, t) = (t @ 'r:=carrier) steps[0] steps[1]`, so the body
    /// under the `λt` binder is `((t' steps[0]) steps[1])`.
    fn recover_steps(&self, sigma: &Term) -> Result<[Term; 2]> {
        use covalence_core::TermKind;
        // sigma = Abs(_, body); body = App(App(t', s0), s1).
        let TermKind::Abs(_, body) = sigma.kind() else {
            return Err(covalence_core::Error::ConnectiveRule(
                "sigma_app_hom: σ is not a λ-abstraction".into(),
            ));
        };
        let TermKind::App(inner, s1) = body.kind() else {
            return Err(covalence_core::Error::ConnectiveRule(
                "sigma_app_hom: σ body is not an application".into(),
            ));
        };
        let TermKind::App(_t, s0) = inner.kind() else {
            return Err(covalence_core::Error::ConnectiveRule(
                "sigma_app_hom: σ body is not a two-arg application".into(),
            ));
        };
        Ok([s0.clone(), s1.clone()])
    }

    /// The shared spine: from `steps` and `σ = λt:Φ_dom. rec steps t`, prove
    /// `⊢ ∀X Y. σ (app_dom X Y) = app_obs (σ X) (σ Y)`.
    ///
    /// `σ : Φ_dom → Φ_obs`. The INNER `app_dom` (of `X, Y : Φ_dom`) builds a
    /// domain node; the OUTER `app_obs` (of `σ X, σ Y : Φ_obs`) is at the
    /// observation carrier. `comp(steps, 1)` gives `⊢ ∀l r. rec steps (app l r) =
    /// step_app (rec steps l)(rec steps r)`; since `step_app = app_obs` and
    /// `σ u ≡β rec steps u`, both `σ (app_dom X Y)` and `app_obs (σ X)(σ Y)`
    /// β-normalise to the comp RHS — so the proof is `beta_nf` both sides +
    /// `trans` + two `all_intro`s, the same spine `relations_sigma` uses at
    /// `Φ⟨bool⟩`. UNCONDITIONAL (no `Wf` guard), hence non-vacuous.
    fn prove_app_hom(&self, steps: &[Term], sigma: &Term) -> Result<Thm> {
        use crate::init::eq::beta_nf;
        use covalence_hol_eval::derived::DerivedRules;

        let dom = self.phi_dom();
        let x = Term::free("X", dom.clone());
        let y = Term::free("Y", dom.clone());

        // lhs = σ (app_dom X Y)   (X, Y : Φ_dom)
        let app_xy = self.app_at_dom(&x, &y)?;
        let lhs = sigma.clone().apply(app_xy)?;
        // rhs = app_obs (σ X) (σ Y)   (σ X, σ Y : Φ_obs)
        let sig_x = sigma.clone().apply(x.clone())?;
        let sig_y = sigma.clone().apply(y.clone())?;
        let rhs = self.app(&sig_x, &sig_y)?;

        let lhs_nf = beta_nf(lhs);
        let rhs_nf = beta_nf(rhs);

        debug_assert_eq!(
            lhs_nf.concl().as_eq().expect("lhs beta_nf eq").1,
            rhs_nf.concl().as_eq().expect("rhs beta_nf eq").1,
            "σ (app_dom X Y) and app_obs (σ X)(σ Y) must share a β-normal form"
        );
        let _ = steps; // steps drive σ's body; the β argument needs no comp call

        let eq = lhs_nf.trans(rhs_nf.sym()?)?;
        eq.all_intro("Y", dom.clone())?.all_intro("X", dom)
    }
}

/// Detect a `concat a b` node (head = the `mm$concat` free var). Returns the two
/// operands, or `None` for a leaf.
fn as_concat(t: &Term) -> Option<(Term, Term)> {
    use covalence_core::TermKind;
    let TermKind::App(inner, b) = t.kind() else {
        return None;
    };
    let TermKind::App(head, a) = inner.kind() else {
        return None;
    };
    if let TermKind::Free(v) = head.kind()
        && v.name() == "mm$concat"
    {
        return Some((a.clone(), b.clone()));
    }
    None
}

fn ind_err(e: InductiveError<covalence_core::Error>) -> covalence_core::Error {
    covalence_core::Error::ConnectiveRule(format!("mm_algebra (inductive): {e}"))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::metamath::{parse, verify_all};
    use covalence_hol_eval::mk_nat;

    fn assert_genuine(thm: &Thm) {
        assert!(thm.hyps().is_empty(), "theorem is hypothesis-free");
    }

    /// `leaf_map := succ` — a genuine non-identity `nat → nat`.
    fn succ_map() -> Term {
        crate::init::nat::nat_succ()
    }

    /// A tiny database whose grammar builds `( ph -> ps )`, so `encode` has real
    /// structure to walk.
    const MM: &str = "\
        $c ( ) -> wff |- $.
        $v ph ps $.
        wph $f wff ph $.
        wps $f wff ps $.
        wi $a wff ( ph -> ps ) $.
        ax-1 $a |- ( ph -> ps ) $.
    ";

    fn db() -> crate::metamath::Database {
        let d = parse(MM).expect("parse");
        verify_all(&d).expect("verify");
        d
    }

    // ========================================================================
    // (1) The MmExpr bundle is a genuine inductive datatype — SEEDS reification.
    // ========================================================================

    /// Realize `MmExpr`; assert ctor types, `distinct`, and both `comp` laws fire
    /// hypothesis-free. [STEP 1]
    #[test]
    fn mmexpr_bundle_is_genuine() {
        let alg = MmExprAlgebra::new().unwrap();
        let th = alg.theory();

        // ctors typed at Φ = Φ_obs (the working carrier): sym : nat → Φ,
        // app : Φ → Φ → Φ. (The polymorphic ctors are an internal detail.)
        let phi = alg.phi();
        assert_eq!(
            alg.sym(&Term::free("c", Type::nat()))
                .unwrap()
                .type_of()
                .unwrap(),
            phi,
            "sym c : Φ"
        );
        assert_eq!(
            alg.app(&Term::free("l", phi.clone()), &Term::free("r", phi.clone()))
                .unwrap()
                .type_of()
                .unwrap(),
            phi,
            "app l r : Φ"
        );

        // distinct(0,1): sym c ≠ app l r  (at the polymorphic carrier).
        let poly = th.ty.clone();
        let c = Term::free("c", Type::nat());
        let l = Term::free("l", poly.clone());
        let r = Term::free("r", poly.clone());
        let distinct = th
            .facts
            .distinct(0, 1, std::slice::from_ref(&c), &[l.clone(), r.clone()])
            .unwrap();
        assert_genuine(&distinct);

        // both comp laws (a rename σ's steps): comp(steps,0), comp(steps,1).
        let steps = alg.sigma_steps(&succ_map()).unwrap();
        for i in 0..2 {
            let comp = th.facts.comp(&steps, i).unwrap();
            assert_genuine(&comp);
        }
    }

    // ========================================================================
    // (2) The structural-σ app-homomorphism BY COMP — the headline reification.
    // ========================================================================

    /// `⊢ ∀X Y. σ (app X Y) = app (σ X) (σ Y)`, hypothesis-free, for
    /// `σ = structural_sigma(succ)`. The first catamorphic homomorphism on the MM
    /// carrier. [STEP 3]
    #[test]
    fn structural_sigma_app_hom_by_comp() {
        let alg = MmExprAlgebra::new().unwrap();
        let leaf_map = succ_map();

        // via the leaf-map entry.
        let hom = alg.sigma_app_hom_of(&leaf_map).unwrap();
        assert_genuine(&hom);

        // Shape: it IS ∀X Y. σ(app_dom X Y) = app_obs (σ X)(σ Y).
        let sigma = alg.structural_sigma(&leaf_map).unwrap();
        let dom = alg.phi_dom();
        let x = Term::free("X", dom.clone());
        let y = Term::free("Y", dom.clone());
        let lhs = sigma
            .clone()
            .apply(alg.app_at_dom(&x, &y).unwrap())
            .unwrap();
        let sx = sigma.clone().apply(x.clone()).unwrap();
        let sy = sigma.clone().apply(y.clone()).unwrap();
        let rhs = alg.app(&sx, &sy).unwrap();
        let expected = lhs
            .equals(rhs)
            .unwrap()
            .forall("Y", dom.clone())
            .unwrap()
            .forall("X", dom.clone())
            .unwrap();
        assert_eq!(hom.concl(), &expected, "app-homomorphism has the σ shape");

        // and the trait-surface method agrees (recovering steps off σ).
        let hom2 = alg.sigma_app_hom(&sigma).unwrap();
        assert_eq!(hom.concl(), hom2.concl(), "trait method == leaf-map entry");
    }

    // ========================================================================
    // (3) Non-vacuity witness — σ genuinely moves a term.
    // ========================================================================

    /// `σ (sym_dom 0)` β-reduces to `sym_obs (succ 0)`, asserted `≠ sym_obs 0`.
    /// So σ ≠ id — it genuinely shifts the leaf code.
    #[test]
    fn sigma_moves_a_term() {
        let alg = MmExprAlgebra::new().unwrap();
        let sigma = alg.structural_sigma(&succ_map()).unwrap();

        // A domain leaf `sym_dom 0 : Φ_dom`.
        let sym0 = alg.sym_at_dom(&mk_nat(0u32)).unwrap();
        let applied = sigma.clone().apply(sym0.clone()).unwrap();
        let nf_thm = crate::init::eq::beta_nf(applied);
        assert_genuine(&nf_thm);
        let nf = nf_thm.concl().as_eq().unwrap().1.clone();

        // equals sym_obs (succ 0)  (the observation-carrier image).
        let succ0 = succ_map().apply(mk_nat(0u32)).unwrap();
        let sym_succ0 = alg.sym(&succ0).unwrap(); // sym at obs
        let sym_succ0_nf = crate::init::eq::beta_nf(sym_succ0)
            .concl()
            .as_eq()
            .unwrap()
            .1
            .clone();
        assert_eq!(nf, sym_succ0_nf, "σ (sym_dom 0) = sym_obs (succ 0)");

        // ≠ sym_obs 0 — the code shifted 0 → succ 0.
        let sym0_obs = alg.sym(&mk_nat(0u32)).unwrap();
        let sym0_nf = crate::init::eq::beta_nf(sym0_obs)
            .concl()
            .as_eq()
            .unwrap()
            .1
            .clone();
        assert_ne!(
            nf, sym0_nf,
            "σ (sym_dom 0) ≠ sym_obs 0 — σ is not the identity"
        );
    }

    // ========================================================================
    // (5) THE ACID TEST — one high-level op on TWO backends, UNCHANGED.
    // ========================================================================

    /// A high-level op written ONCE against `MmAlgebra` — `app (encode e1) (encode
    /// e2)` — run on BOTH `FreeAlgebra` and `MmExprAlgebra`, asserting each yields
    /// a well-typed Φ-term of the respective carrier. The SAME code, unchanged,
    /// across the swapped backend = insulation proven mechanically.
    fn encode_pair<A: MmAlgebra>(
        alg: &A,
        db: &crate::metamath::Database,
        e1: &crate::metamath::Expr,
        e2: &crate::metamath::Expr,
    ) -> Result<Term> {
        alg.app(&alg.encode(db, e1)?, &alg.encode(db, e2)?)
    }

    #[test]
    fn insulation_high_level_op_on_two_backends() {
        let d = db();
        // Two encodable bodies from the database's `|-` assertion conclusion.
        let assertion = d
            .assertions()
            .find(|a| a.label == "ax-1")
            .expect("ax-1")
            .clone();
        let e = &assertion.conclusion;

        // Backend 1: the recursor-free free algebra (Φ = nat).
        let free = FreeAlgebra(&d);
        let r_free = encode_pair(&free, &d, e, e).unwrap();
        assert_eq!(
            r_free.type_of().unwrap(),
            free.phi(),
            "free-algebra result is a Φ=nat term"
        );

        // Backend 2: the inductive MmExpr (Church carrier) — SAME `encode_pair`.
        let mmexpr = MmExprAlgebra::new().unwrap();
        let r_mmexpr = encode_pair(&mmexpr, &d, e, e).unwrap();
        assert_eq!(
            r_mmexpr.type_of().unwrap(),
            mmexpr.phi(),
            "MmExpr result is a Φ=MmExpr term"
        );

        // The two carriers genuinely differ (the swap is real, not cosmetic).
        assert_ne!(
            free.phi(),
            mmexpr.phi(),
            "the two backends have DIFFERENT carriers — a real low-level swap"
        );
    }

    /// Capability honesty: FreeAlgebra reports non-structural + errors on
    /// `sigma_app_hom`; MmExprAlgebra reports structural + proves it.
    #[test]
    fn caps_are_honest() {
        let d = db();
        let free = FreeAlgebra(&d);
        assert!(!free.caps().structural);
        assert!(
            free.sigma_app_hom(&free.structural_sigma(&succ_map()).unwrap())
                .is_err()
        );

        let mmexpr = MmExprAlgebra::new().unwrap();
        assert!(mmexpr.caps().structural);
        assert!(mmexpr.sigma_app_hom_of(&succ_map()).is_ok());
    }
}
