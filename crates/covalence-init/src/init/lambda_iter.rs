//! # λ_iter, deeply embedded — a Tarski-style universe of codes over `nat`
//!
//! This module is the HOL-layer **deep embedding** of `λ_iter` (the first-order
//! expression language with branching and iteration from §2.1 of *Categorical
//! Imperative Programming*). Where the *shallow* embedding
//! (`crates/proof/metamath/tests/lambda_iter.rs`) makes each typing rule a
//! Metamath axiom — so a derivation *is* a proof and the metatheory is not
//! statable — the deep embedding **reifies syntax and derivations as data** so
//! that weakening, substitution, and the rest become ordinary theorems proved
//! by induction *inside* HOL.
//!
//! The kernel gives us exactly one structural-induction primitive,
//! [`Thm::nat_induct`](covalence_core::Thm::nat_induct) (over `0` / `succ`).
//! So the data we reify syntax into is the natural numbers, and every
//! "induction over the structure of a type / a derivation" is carried out as
//! **course-of-values induction on a `nat` code** — the lemma
//! [`strong_induct`] proved in `lambda_iter.cov`.
//!
//! ## Tarski-style universes (the encoding, conceptually)
//!
//! A **Tarski universe** is a pair `(U, El)`: a type `U` of *codes* together
//! with a *decoding* `El : U → Type` that sends a code to the thing it denotes.
//! Crucially the codes are plain data you can compute with and do induction
//! over — they are **not** the denoted objects themselves (that would be a
//! *Russell* universe). We mirror that here, three times over, with the
//! carrier `U` fixed to `nat`:
//!
//! ```text
//!     U_ty  ⊆ ℕ     El_ty  : U_ty  → (λ_iter types)        -- type codes
//!     U_ex  ⊆ ℕ     El_ex  : U_ex  → (λ_iter expressions)  -- expression codes
//!     U_ctx ⊆ ℕ     El_ctx : U_ctx → (λ_iter contexts)     -- context codes
//! ```
//!
//! Each universe `U_• ⊆ ℕ` is a **decidable predicate** `WfTyCode : nat → bool`
//! (resp. `WfExCode`, `WfCtxCode`) carving out the *well-formed* codes — the
//! image of the grammar. `El_•` is the partial decoding back to the object it
//! denotes; in a deep embedding we rarely run `El` (the code already *is* the
//! syntax), but naming it pins down what a code means and what `Wf` ranges over.
//! The reverse direction, the **encoding** `⌜·⌝ : syntax → ℕ`, is the
//! Gödel-numbering defined just below; `WfTyCode (⌜A⌝) = ⊤` and
//! `El_ty (⌜A⌝) = A` are its round-trip laws.
//!
//! ## The code/decode scheme (the encoding, concretely)
//!
//! Codes are built from two pieces of arithmetic:
//!
//! * a **tag** `nat` per constructor (a small constant — see [`tag`] below), and
//! * an injective **pairing** `⟨·,·⟩ : nat → nat → nat` with projections
//!   `π₁, π₂` and the strict-decrease laws `π₁⟨a,b⟩ < ⟨a,b⟩` and
//!   `π₂⟨a,b⟩ < ⟨a,b⟩` whenever the pair is non-trivial (Cantor pairing, or any
//!   monotone injective pairing, supplies these). The decrease laws are what
//!   make a child's code strictly smaller than its parent's — the bridge from
//!   *structural* recursion to course-of-values recursion on `<`.
//!
//! A node `c(x₁,…,xₖ)` with constructor tag `t` and child codes `n₁,…,nₖ` is
//! encoded as the spine `⟨t, ⟨n₁, ⟨…, ⟨nₖ, 0⟩…⟩⟩⟩`. Decoding reads the head
//! tag with `π₁` and walks the spine with `π₂`. Concretely, for **types**
//! (Fig 1: `A ::= X | A⊗B | 1 | A+B | 0`):
//!
//! ```text
//!     ⌜0⌝        = ⟨tag.empty,  0⟩              El_ty = 𝟎
//!     ⌜1⌝        = ⟨tag.unit,   0⟩              El_ty = 𝟏
//!     ⌜Xᵢ⌝       = ⟨tag.base,   ⟨i, 0⟩⟩          El_ty = the i-th base type
//!     ⌜A ⊗ B⌝    = ⟨tag.tensor, ⟨⌜A⌝, ⟨⌜B⌝,0⟩⟩⟩  El_ty = El A ⊗ El B
//!     ⌜A + B⌝    = ⟨tag.sum,    ⟨⌜A⌝, ⟨⌜B⌝,0⟩⟩⟩  El_ty = El A + El B
//! ```
//!
//! **Expressions** add the binders, and here the nat encoding pays off twice:
//! object variables become **de Bruijn indices** (themselves `nat`s), so the
//! grammar's `x ∉ Γ` freshness side-condition and α-equivalence evaporate — a
//! variable code is just `⟨tag.var, ⟨i, 0⟩⟩` for de Bruijn index `i`, and a
//! binder (`let`, `case`, `iter`) simply shifts indices in its body. (The
//! shallow embedding instead leaned on Metamath `$d` conditions; de Bruijn over
//! `nat` is the deep-embedding analogue.)
//!
//! **Contexts** are encoded as nat-coded lists of type codes (the spine trick
//! with `tag.cnil` / `tag.ccons`), so `El_ctx ⌜·⌝ = ·` and
//! `El_ctx ⌜Γ, x:A⌝ = El_ctx Γ, x : El_ty A`.
//!
//! ## Reifying the typing judgement and its derivations
//!
//! The typing relation `Γ ⊢ a : A` is reified as a predicate on the three codes,
//! `Typed : nat → nat → nat → bool` — defined as the least relation closed under
//! the (coded) Fig 2 rules. The metatheory (weakening 2.1.1.2.1, substitution
//! 2.1.1.2.2) ranges over *derivations*, so derivations too are reified: a
//! **derivation code** `d : nat` packages a rule tag with the codes of its
//! premises' derivations, and `Checks : nat → nat → nat → nat → bool`
//! ("`d` witnesses `Typed Γ a A`") is primitive-recursive on `d`. Then:
//!
//! > **induction over a derivation  ≡  course-of-values induction on `d`'s code**
//!
//! because each sub-derivation sits at a strictly smaller code (the pairing
//! decrease laws again). That equivalence — the whole reason this embedding
//! lives on `nat` — is discharged by [`strong_induct`].
//!
//! ## What is proved here vs. deferred
//!
//! `lambda_iter.cov` proves, end to end:
//!
//! * **Induction substrate** — [`strong_below`] / [`strong_induct`]
//!   (course-of-values induction on `nat`, from `Thm::nat_induct` + the
//!   `nat.cov` `<`/`≤` order theory). The core every code-level *induction*
//!   reduces to.
//! * **Course-of-values recursion** — the full theorem (the recursion dual of
//!   `strong_induct`):
//!   [`cv_unique`] (uniqueness/determinacy, proved directly by [`strong_induct`])
//!   plus [`cv_exists`](crate::init::cv_recursion::cv_exists) (existence:
//!   `⊢ Hext F ⟹ ∃f. ∀n. f n = F n f`, by bounded iteration in
//!   [`cv_recursion`](crate::init::cv_recursion)). Together they let a *function*
//!   be **defined** by course-of-values recursion on a `nat` code — `WfTyCode` /
//!   `Typed` / `El`, and the `nat` division floor witness.
//! * **Recursion infrastructure** — [`cvrec_rec_zero`] / [`cvrec_rec_succ`]
//!   (the `natRec` equations at result type `nat → 'a`, i.e. *function*-valued
//!   recursion — what the bounded approximation `B : nat → (nat → 'a)` runs on)
//!   and [`nat_zero_or_succ`].
//!
//! **Deferred** (see this crate's `SKELETONS.md`):
//!
//! * **Encoding + metatheorems** — pairing/tags, `WfTyCode`/`El`/`Typed` (now
//!   definable by the course-of-values recursion above), and subtyping
//!   reflexivity/transitivity → weakening → substitution, each by
//!   [`strong_induct`] on a code.

/// Function-valued `natRec` equations — the recursion theorem at result type
/// `nat → 'a` (so a recursion can produce a *function*, e.g. the bounded
/// approximation `B : nat → (nat → 'a)` the course-of-values construction
/// iterates). The `nat` env only exposes the monomorphic (`β = nat`) form; this
/// is the same fully-proved theorem ([`recursion::rec_holds_proof_at`]) at
/// `β = nat → 'a`, with `'a` schematic so `.cov` may use it at any result type.
pub(crate) fn natrec_fn_env() -> crate::script::Env {
    use covalence_core::Type;
    let mut e = crate::script::Env::empty();
    let beta = Type::fun(Type::nat(), Type::tfree("a"));
    e.define_lemma(
        "rec.holds.fn",
        crate::init::recursion::rec_holds_proof_at(&beta).expect("natRec equations at nat→'a"),
    );
    e
}

crate::cov_theory! {
    /// λ_iter deep-embedding induction substrate, over `core` + `logic` + the
    /// `nat` order theory. Exposes course-of-values induction on `nat`, the
    /// principle all code-level structural inductions reduce to.
    pub mod cov from "lambda_iter.cov" {
        import "core" = crate::script::Env::core();
        import "logic" = crate::init::logic::cov::env();
        import "nat" = crate::init::nat::cov::env();
        import "natrecfn" = crate::init::lambda_iter::natrec_fn_env();
        "strong.below"     => pub fn strong_below;
        "strong.induct"    => pub fn strong_induct;
        "cv.unique"        => pub fn cv_unique;
        "cvrec.rec_zero"   => pub fn cvrec_rec_zero;
        "cvrec.rec_succ"   => pub fn cvrec_rec_succ;
        "nat.zero_or_succ" => pub fn nat_zero_or_succ;
        "nat.lt_pred"        => pub fn nat_lt_pred;
        "nat.lt_succ_imp_le" => pub fn nat_lt_succ_imp_le;
        "nat.lt_le_trans"    => pub fn nat_lt_le_trans;
        "nat.lt_succ_self"   => pub fn nat_lt_succ_self;
    }
}

pub use cov::{
    cv_unique, cvrec_rec_succ, cvrec_rec_zero, nat_lt_le_trans, nat_lt_pred, nat_lt_succ_imp_le,
    nat_lt_succ_self, nat_zero_or_succ, strong_below, strong_induct,
};

#[cfg(test)]
mod tests {
    //! Forcing either accessor replays + resolves the whole `lambda_iter.cov`
    //! theory through the kernel, so these tests *are* the proof check.

    /// Course-of-values induction replays and lands a hypothesis-free theorem.
    #[test]
    fn strong_induct_proves() {
        let thm = super::strong_induct();
        assert!(
            thm.hyps().is_empty(),
            "strong.induct should be a closed theorem, got hyps: {:?}",
            thm.hyps()
        );
    }

    /// The accumulator lemma it rests on also replays cleanly.
    #[test]
    fn strong_below_proves() {
        let thm = super::strong_below();
        assert!(thm.hyps().is_empty(), "strong.below should be closed");
    }

    /// Course-of-values recursion uniqueness (determinacy) replays cleanly.
    #[test]
    fn cv_unique_proves() {
        let thm = super::cv_unique();
        assert!(thm.hyps().is_empty(), "cv.unique should be closed");
    }
}
