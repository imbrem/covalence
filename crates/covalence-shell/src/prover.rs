//! High-level generic theorem-prover API.
//!
//! `Prover` is the **stable surface** that downstream prover frontends
//! (Alethe, OpenTheory, Metamath, Lean, …) target. Implementations lower it
//! to whatever underlying kernel is in flight — currently
//! [`covalence_kernel::Kernel`], later the framework / HOL-on-framework stack
//! from the [layered-framework
//! proposal](../../../docs/design/proposals/layered-framework/).
//!
//! Design notes:
//!
//! - **All methods return `Result`**, so an in-flight kernel rewrite can
//!   stub any individual operation with `ProverError::NotImplemented` and
//!   leave the trait + every frontend compiling.
//! - **Associated types** for `Type` / `Term` / `Prop` / `Thm` keep the
//!   trait kernel-agnostic. The only requirement is `Copy` or `Clone` plus
//!   `Debug`, which every reasonable backend satisfies.
//! - **No name interning at the trait level.** Methods take `&str`; the
//!   impl handles interning (`covalence-kernel` already does it natively).
//! - The surface is **kept small on purpose**. Today it covers what the
//!   Alethe bridge actually uses + the LIA term language. Future frontends
//!   will extend it; we'd rather grow the trait deliberately than ship
//!   speculative methods.

use std::fmt::Debug;

use covalence_kernel::primop::{PrimOp1, PrimOp2};
use covalence_types::Int;

/// Errors any `Prover` impl may return.
#[derive(Debug, thiserror::Error)]
pub enum ProverError {
    /// The operation is not yet wired up in this impl. The variant carries a
    /// short label so callers can route around (or surface) specific gaps
    /// without depending on the underlying kernel error taxonomy.
    #[error("prover operation not implemented: {0}")]
    NotImplemented(String),

    /// An underlying `covalence-kernel` proof rule failed. Carries the
    /// original `ProofError` for diagnostics; the variant is opaque to
    /// frontends that don't want to introspect.
    #[error("kernel proof error: {0:?}")]
    Proof(covalence_kernel::ProofError),

    /// A type-construction step failed at the arena level.
    #[error("subset/type-operator error: {0:?}")]
    SubsetError(covalence_kernel::SubsetError),

    /// A union-find merge failed.
    #[error("union error: {0:?}")]
    UnionError(covalence_kernel::UnionError),

    /// Catch-all for backend-specific failures the frontend doesn't need to
    /// distinguish (e.g., a foreign reference where a local was required).
    #[error("prover error: {0}")]
    Other(String),
}

impl From<covalence_kernel::ProofError> for ProverError {
    fn from(e: covalence_kernel::ProofError) -> Self {
        ProverError::Proof(e)
    }
}

impl From<covalence_kernel::SubsetError> for ProverError {
    fn from(e: covalence_kernel::SubsetError) -> Self {
        ProverError::SubsetError(e)
    }
}

impl From<covalence_kernel::UnionError> for ProverError {
    fn from(e: covalence_kernel::UnionError) -> Self {
        ProverError::UnionError(e)
    }
}

/// The high-level theorem-prover API.
///
/// Implementations wrap a concrete kernel. Frontends are generic over
/// `P: Prover`. Methods are grouped by category for readability; the trait
/// itself is flat.
pub trait Prover {
    /// Backend representation of types.
    type Type: Copy + Debug;
    /// Backend representation of terms. `Eq + Hash` is required so frontends
    /// can dedupe compound-term construction (the kernel doesn't hash-cons
    /// `alloc_term`, so re-translating the same SExpr yields a fresh
    /// `TermRef` — caches at the frontend layer fix that).
    type Term: Copy + Debug + Eq + std::hash::Hash;
    /// Backend representation of a (context, conclusion) pair before kernel
    /// validation — the "intent to prove" handle.
    type Prop: Clone + Debug;
    /// Backend representation of a proven theorem.
    type Thm: Clone + Debug;

    // -----------------------------------------------------------------
    // Types
    // -----------------------------------------------------------------

    fn bool_ty(&self) -> Result<Self::Type, ProverError>;
    fn int_ty(&self) -> Result<Self::Type, ProverError>;
    fn nat_ty(&self) -> Result<Self::Type, ProverError>;
    fn bytes_ty(&self) -> Result<Self::Type, ProverError>;
    fn fun_ty(&mut self, dom: Self::Type, cod: Self::Type) -> Result<Self::Type, ProverError>;

    /// User-declared type constructor applied to its arguments.
    /// Models `(declare-sort U n)` + use sites.
    fn tyapp(&mut self, name: &str, args: &[Self::Type]) -> Result<Self::Type, ProverError>;

    /// Polymorphic type variable.
    fn tyvar(&mut self, name: &str) -> Result<Self::Type, ProverError>;

    // -----------------------------------------------------------------
    // Terms — primitive constructors
    // -----------------------------------------------------------------

    fn truth(&mut self) -> Result<Self::Term, ProverError>;
    fn falsity(&mut self) -> Result<Self::Term, ProverError>;
    fn int_lit(&mut self, n: i64) -> Result<Self::Term, ProverError>;
    fn nat_lit(&mut self, n: u64) -> Result<Self::Term, ProverError>;

    /// Arbitrary-precision integer literal. cvc5 (and any real SMT solver)
    /// emits literals far outside `i64` range; the bridge translates them
    /// through this method.
    ///
    /// Default: `NotImplemented`. The kernel impl will lower it onto the
    /// arbitrary-precision int constructor once that lands; until then the
    /// `i64` fast path covers the test fixtures.
    fn int_lit_big(&mut self, _n: &Int) -> Result<Self::Term, ProverError> {
        Err(ProverError::NotImplemented("int_lit_big".into()))
    }

    /// `ite(c, a, b)` — if-then-else over any sort. cvc5's preprocessor lifts
    /// `ite` even in nominally QF_UFLIA problems, so the bridge needs a term
    /// constructor regardless of whether the kernel surfaces it as a primop
    /// or as a defined symbol.
    ///
    /// Default: `NotImplemented`. The redesigned kernel can either expose a
    /// dedicated `TermDef::Ite` variant or define `ite` via subset types; the
    /// trait stays agnostic.
    fn ite(
        &mut self,
        _c: Self::Term,
        _a: Self::Term,
        _b: Self::Term,
    ) -> Result<Self::Term, ProverError> {
        Err(ProverError::NotImplemented("ite".into()))
    }

    /// Free variable: a named, typed variable that occurs free in the term.
    fn free_var(&mut self, name: &str, ty: Self::Type) -> Result<Self::Term, ProverError>;

    /// Constant: a named, typed reference to a fixed denotation. The kernel
    /// does not require pre-registration; semantics come from later
    /// derivations or axioms.
    fn const_term(&mut self, name: &str, ty: Self::Type) -> Result<Self::Term, ProverError>;

    /// Application `(f x)`.
    fn comb(&mut self, f: Self::Term, x: Self::Term) -> Result<Self::Term, ProverError>;

    /// Equality `(a = b)`.
    fn eq(&mut self, a: Self::Term, b: Self::Term) -> Result<Self::Term, ProverError>;

    /// Lambda abstraction `(λ name:ty. body)`. The body should contain
    /// `Free(name, ty)` references; the impl handles closing over them.
    fn lam(
        &mut self,
        name: &str,
        ty: Self::Type,
        body: Self::Term,
    ) -> Result<Self::Term, ProverError>;

    // -----------------------------------------------------------------
    // Terms — primops (Boolean + integer)
    // -----------------------------------------------------------------
    //
    // These cover the propositional connectives + linear arithmetic
    // operators SMT-LIB problems use. The kernel exposes them as `Op1`/
    // `Op2`; the trait gives them named accessors so frontends don't have
    // to know the `PrimOp1`/`PrimOp2` enum.

    fn op1(&mut self, op: PrimOp1, x: Self::Term) -> Result<Self::Term, ProverError>;
    fn op2(
        &mut self,
        op: PrimOp2,
        a: Self::Term,
        b: Self::Term,
    ) -> Result<Self::Term, ProverError>;

    /// `¬p`.
    fn not_(&mut self, p: Self::Term) -> Result<Self::Term, ProverError> {
        self.op1(PrimOp1::LogicalNot, p)
    }

    /// `p ∧ q`.
    fn and_(&mut self, a: Self::Term, b: Self::Term) -> Result<Self::Term, ProverError> {
        self.op2(PrimOp2::LogicalAnd, a, b)
    }

    /// `p ∨ q`.
    fn or_(&mut self, a: Self::Term, b: Self::Term) -> Result<Self::Term, ProverError> {
        self.op2(PrimOp2::LogicalOr, a, b)
    }

    /// `p ⇒ q`.
    fn imp(&mut self, a: Self::Term, b: Self::Term) -> Result<Self::Term, ProverError> {
        self.op2(PrimOp2::LogicalImp, a, b)
    }

    /// `p ⊻ q`.
    fn xor_(&mut self, a: Self::Term, b: Self::Term) -> Result<Self::Term, ProverError> {
        self.op2(PrimOp2::LogicalXor, a, b)
    }

    // -----------------------------------------------------------------
    // Inspection
    // -----------------------------------------------------------------

    /// The conclusion of a Thm as a Term. Round-trips through the kernel's
    /// own representation; frontends use it to extract equalities or to
    /// re-check shapes for rules like `cong`.
    fn conclusion(&self, th: &Self::Thm) -> Result<Self::Term, ProverError>;

    /// Destructure `t` as an equality `(= a b)`, returning `Some((a, b))`
    /// if so. Used by rules that consume premise equalities (`cong`,
    /// `eq_mp`, …) and need access to the sides.
    fn dest_eq(&self, t: Self::Term) -> Option<(Self::Term, Self::Term)>;

    /// Destructure `t` as `ite(c, a, b)`, if so. Mirrors [`Self::ite`] on the
    /// inspection side.
    ///
    /// Default: `None`. Backends without an ITE constructor have nothing to
    /// destructure; the bridge falls through to other shapes.
    fn dest_ite(&self, _t: Self::Term) -> Option<(Self::Term, Self::Term, Self::Term)> {
        None
    }

    /// Destructure `t` as a propositional disjunction `(a ∨ b)`, returning
    /// `Some((a, b))` if so. Useful for resolution / clause-shape rules
    /// where the bridge needs to walk the left-folded `Or` tree to find a
    /// pivot literal.
    ///
    /// Default: `None`.
    fn dest_or(&self, _t: Self::Term) -> Option<(Self::Term, Self::Term)> {
        None
    }

    /// Destructure `t` as a propositional negation `¬a`. Symmetric to
    /// [`Self::dest_or`] / [`Self::dest_eq`].
    ///
    /// Default: `None`.
    fn dest_not(&self, _t: Self::Term) -> Option<Self::Term> {
        None
    }

    // -----------------------------------------------------------------
    // Context (assumption management)
    // -----------------------------------------------------------------

    /// Push `t` onto the current context as an assumption, returning the
    /// `Prop` handle that downstream rules (e.g. `assume`) reference.
    fn push_assumption(&mut self, t: Self::Term) -> Result<Self::Prop, ProverError>;

    // -----------------------------------------------------------------
    // Trust-injection (egraph union)
    // -----------------------------------------------------------------

    /// Record `a ≡ b` in the egraph's union-find **without proof**.
    ///
    /// This is the kernel's trust escape hatch: any subsequent `cong`-style
    /// derivation that closes over this union depends on the equality being
    /// semantically true. The framework redesign will replace this with an
    /// observation under a named authority; until then, callers should
    /// document at the call site *why* the equality is trusted (e.g.
    /// "Alethe TRUST_THEORY_REWRITE step" or "downstream of an
    /// already-verified Thm conclusion").
    fn union(&mut self, a: Self::Term, b: Self::Term) -> Result<(), ProverError>;

    // -----------------------------------------------------------------
    // Proof rules
    // -----------------------------------------------------------------

    /// `Γ ⊢ φ` from `φ ∈ Γ`.
    fn assume(&mut self, p: Self::Prop) -> Result<Self::Thm, ProverError>;

    /// `Γ ⊢ t = t`.
    fn refl(&mut self, t: Self::Term) -> Result<Self::Thm, ProverError>;

    /// `Γ ⊢ a = b` ↦ `Γ ⊢ b = a`.
    fn sym(&mut self, th: Self::Thm) -> Result<Self::Thm, ProverError>;

    /// `Γ ⊢ a = b`, `Γ ⊢ b = c` ↦ `Γ ⊢ a = c`.
    fn trans(&mut self, ab: Self::Thm, bc: Self::Thm) -> Result<Self::Thm, ProverError>;

    /// `Γ ⊢ p = q`, `Γ ⊢ p` ↦ `Γ ⊢ q`.
    fn eq_mp(&mut self, pq: Self::Thm, p_thm: Self::Thm) -> Result<Self::Thm, ProverError>;

    /// `Γ ⊢ p ⇒ q`, `Γ ⊢ p` ↦ `Γ ⊢ q`.
    fn mp(&mut self, imp: Self::Thm, ant: Self::Thm) -> Result<Self::Thm, ProverError>;

    /// Congruence: `Γ ⊢ a = b` where `a` and `b` are structurally congruent
    /// up to `depth` via the egraph's union-find. The depth parameter caps
    /// the recursion (`0` = exact match at level-0).
    fn cong(
        &mut self,
        a: Self::Term,
        b: Self::Term,
        depth: u32,
    ) -> Result<Self::Thm, ProverError>;

    /// β-reduction: `Γ ⊢ ((λx. body) arg) = body[arg/x]`.
    fn beta(&mut self, comb: Self::Term) -> Result<Self::Thm, ProverError>;

    /// `Γ ⊢ s = t` ↦ `Γ ⊢ (λname:ty. s) = (λname:ty. t)`.
    fn abs(
        &mut self,
        th: Self::Thm,
        name: &str,
        ty: Self::Type,
    ) -> Result<Self::Thm, ProverError>;

    /// Variable instantiation: substitute `replacement` for free occurrences
    /// of `Free(name, ty)` in the theorem.
    fn inst(
        &mut self,
        th: Self::Thm,
        name: &str,
        ty: Self::Type,
        replacement: Self::Term,
    ) -> Result<Self::Thm, ProverError>;

    /// Deductive antisymmetry:
    /// `Γ ⊢ p`, `Γ ⊢ q` ↦ `Γ ⊢ p = q` (with assumptions managed per the
    /// kernel's convention).
    fn deduct_antisym(
        &mut self,
        p_thm: Self::Thm,
        q_thm: Self::Thm,
    ) -> Result<Self::Thm, ProverError>;

    /// Apply the kernel's host-side reduction (literal evaluation, primop
    /// simplification) to produce `Γ ⊢ t = t↓`.
    fn reduce(&mut self, t: Self::Term) -> Result<Self::Thm, ProverError>;

    // -----------------------------------------------------------------
    // Boolean reasoning primitives
    // -----------------------------------------------------------------
    //
    // These are the two pieces missing from the existing rule set that block
    // propositional reasoning over free Bool variables. With them, all
    // propositional Alethe rules (equiv_pos2, resolution, false, …) become
    // derivable; without them, even `⊢ ¬False` is unreachable.

    /// `Γ ⊢ t` if `t` is a propositional tautology over its free Bool
    /// variables. Implemented by the kernel via brute-force 2^n truth-table
    /// check; supports `Bool` literals, `LogicalNot/And/Or/Imp/Xor/Nand/Nor`,
    /// and `Eq` over Booleans.
    ///
    /// The intent is that prover frontends building propositional rules
    /// (Alethe `equiv_pos2` / `resolution` / `false` / `or` / …) route through
    /// this single primitive rather than each rule deriving its own
    /// case-split.
    fn tautology_intro(&mut self, t: Self::Term) -> Result<Self::Thm, ProverError>;

    // -----------------------------------------------------------------
    // Subproof / Deduction Theorem
    // -----------------------------------------------------------------

    /// Deduction Theorem: `Γ, p ⊢ q` ↦ `Γ ⊢ p ⇒ q`.
    ///
    /// The dual of [`Self::mp`] / [`Self::push_assumption`]; needed for
    /// closing Alethe `anchor` scopes. The bridge tracks anchor frames
    /// locally and uses this to lift the inner conclusion into the outer
    /// context.
    ///
    /// Default: `NotImplemented`. The redesigned kernel is expected to ship
    /// this as a single rule (or to compose it from `add_assumption` +
    /// `mp` + a new `imp_intro`).
    fn discharge(
        &mut self,
        _thm: Self::Thm,
        _p: Self::Prop,
    ) -> Result<Self::Thm, ProverError> {
        Err(ProverError::NotImplemented("discharge".into()))
    }

    // -----------------------------------------------------------------
    // Clause-level resolution
    // -----------------------------------------------------------------

    /// Atomic propositional resolution.
    ///
    /// Given `Γ ⊢ C₁` and `Γ ⊢ C₂` with `C₁ = … ∨ pivot ∨ …` and
    /// `C₂ = … ∨ ¬pivot ∨ …` (left-folded disjunctions; either side may
    /// carry the negated literal), derive `Γ ⊢ C₁' ∨ C₂'` with the pivot
    /// pair removed.
    ///
    /// Today's `resolution` Alethe rule discharges via [`Self::tautology_intro`]
    /// (sound but 2ⁿ in the number of Bool atoms). This primitive is the
    /// linear-cost replacement cvc5 proofs need at scale; it'll desugar to
    /// `or_elim` + `mp` in the rewritten kernel.
    ///
    /// Default: `NotImplemented`.
    fn resolve(
        &mut self,
        _c1: Self::Thm,
        _c2: Self::Thm,
        _pivot: Self::Term,
    ) -> Result<Self::Thm, ProverError> {
        Err(ProverError::NotImplemented("resolve".into()))
    }

    // -----------------------------------------------------------------
    // Linear integer arithmetic
    // -----------------------------------------------------------------

    /// `Γ ⊢ t` if `t` is a linear-integer-arithmetic tautology.
    ///
    /// Decides QF_LIA Bool combinations of `IntLe`/`IntLt`/`IntEq` over
    /// `IntAdd`/`IntMul`-by-constant/`IntNeg`/`int_lit*` terms, with free
    /// `Int` variables existentially quantified at the top. Internally this
    /// is the LIA analog of [`Self::tautology_intro`]: brute-force isn't
    /// available, so the kernel-side implementation is expected to combine
    /// (a) the propositional truth-table check over the LIA literals'
    /// Bool structure, and (b) a Farkas/Fourier-Motzkin search for each
    /// satisfying literal assignment.
    ///
    /// The bridge falls through to this primitive when an Alethe step has
    /// no Farkas hints (rare — cvc5 emits hints for `la_generic` — but
    /// `lia_generic` and some `*_simplify` paths do).
    ///
    /// Default: `NotImplemented`. See also [`Self::farkas`] for the
    /// hint-driven faster path.
    fn lia_tautology(&mut self, _t: Self::Term) -> Result<Self::Thm, ProverError> {
        Err(ProverError::NotImplemented("lia_tautology".into()))
    }

    /// Farkas-certificate-checked refutation.
    ///
    /// Given premises `Γ ⊢ φᵢ` where each `φᵢ` is a linear-arith atom
    /// (`Σⱼ aᵢⱼ·xⱼ ⨂ᵢ bᵢ` with `⨂ᵢ ∈ {≤, <, =}`) and matching nonneg
    /// integer coefficients `λᵢ`, derive `Γ ⊢ False` by checking that
    /// `Σᵢ λᵢ · (LHSᵢ - RHSᵢ)` reduces to a positive constant under
    /// LIA normalization — i.e. the certificate witnesses unsatisfiability.
    ///
    /// This is the cvc5 `la_generic` shape: the `:args` carry the `λᵢ`,
    /// the negated clause literals are the premises (the bridge negates
    /// them up-front via `assume` + `discharge` once `discharge` lands).
    ///
    /// Returns `ProverError::Other` if the lengths mismatch; the
    /// soundness check itself fails closed with `NotATautology` once the
    /// kernel implementation lands.
    ///
    /// Default: `NotImplemented`. The intended desugaring is documented in
    /// the next paragraph and is expected to be a *derived* shell-level
    /// rule once the std-lib lemmas (sign-preserving multiplication,
    /// additivity, integer tightening) are in place.
    ///
    /// # Desugaring sketch
    ///
    /// For each premise `Γ ⊢ Lᵢ ≤ Rᵢ` (or `<`, or `=`):
    /// 1. Normalize to `Γ ⊢ (Lᵢ - Rᵢ) ≤ 0` via `int_le_sub_iff`.
    /// 2. Scale by `λᵢ` via `int_le_mul_nonneg` (needs `0 ≤ λᵢ`,
    ///    discharged by literal evaluation).
    /// 3. Equalities split into two scaled inequalities (signed coefficient
    ///    handled by the `λᵢ` being interpreted as `±|λᵢ|`).
    ///
    /// Then iteratively combine via `int_le_add_compat` to get
    /// `Γ ⊢ Σᵢ λᵢ(Lᵢ - Rᵢ) ≤ 0`, run [`Self::reduce`] on the LHS to fold
    /// to a constant `k`, and conclude `k ≤ 0` contradicts `0 < k` (a
    /// literal-evaluation step).
    fn farkas(
        &mut self,
        _premises: &[Self::Thm],
        _coeffs: &[Int],
    ) -> Result<Self::Thm, ProverError> {
        Err(ProverError::NotImplemented("farkas".into()))
    }
}
