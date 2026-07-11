//! The **`list` inductive adapter** — `list α` as an [`Inductive`] for the
//! generic recursion engine ([`crate::init::inductive`]).
//!
//! `list α := stream (option α) where (finite ∧ contiguous)` is a derived
//! type, so its `Inductive` interface is supplied by *theorems*, not kernel
//! primitives:
//!
//! - **induction** — [`crate::init::list::list_induct`] (itself a genuine
//!   theorem, via a finiteness-bound `nat`-induction);
//! - **`cons` injectivity** — [`crate::init::list::cons_inj`];
//! - **`nil`/`cons` distinctness** — [`crate::init::list::nil_ne_cons`].
//!
//! This is the **lifting seam** the engine was designed for: where `nat`'s
//! adapter ([`crate::init::recursion`]) wraps kernel primitives
//! (`Thm::nat_induct` / `Thm::succ_inj`), `list`'s wraps *derived* theorems
//! — so the same `graph`/`existence`/`uniqueness`/`determinacy` machinery
//! runs unchanged, proving that genuine `list` structural recursion is
//! available.
//!
//! See `SKELETONS.md` for what rides on top (the `list_foldr` / `list_foldl`
//! catalogue equations — a *catamorphic* specialisation of the paramorphic
//! recursor the engine produces).

use covalence_core::{Error, Result, Term, Type};
use covalence_hol_eval::EvalThm as Thm;
use covalence_hol_eval::derived::DerivedRules;

use crate::init::ext::{TermExt, ThmExt};
use crate::init::inductive::{Arg, Constructor, Inductive, InductiveSig};
use crate::init::list::{cons_inj, list_induct, nil_ne_cons};

use covalence_hol_eval::defs::{cons, list, nil, option};

/// The element type `α` the adapter is specialised at.
fn elem() -> Type {
    Type::tfree("a")
}

/// `list α` at the adapter's element type.
fn list_ty() -> Type {
    list(elem())
}

/// The `list α` signature: `nil` (nullary) and `cons` (an element
/// parameter `x : α`, then one recursive argument `xs : list α` with image
/// `b`). Matches the `cons`-shaped constructor the engine's `graph` layer
/// already exercises (`Param` then `Rec`).
pub fn list_sig() -> &'static InductiveSig {
    static SIG: std::sync::LazyLock<InductiveSig> = std::sync::LazyLock::new(|| InductiveSig {
        ty: list(Type::tfree("a")),
        relation: "G",
        ctors: vec![
            Constructor::nullary(nil(Type::tfree("a"))),
            Constructor::new(
                cons(Type::tfree("a")),
                vec![
                    Arg::Param {
                        ty: Type::tfree("a"),
                        name: "x",
                    },
                    Arg::Rec {
                        name: "xs",
                        image: "b",
                    },
                ],
            ),
        ],
    });
    &SIG
}

/// `list`'s [`Inductive`] adapter, sourcing induction + freeness from the
/// derived theorems in [`mod@crate::init::list`].
pub struct ListTheory;

impl Inductive for ListTheory {
    fn sig(&self) -> &InductiveSig {
        list_sig()
    }

    fn induct(&self, motive: &Term, cases: Vec<Thm>) -> Result<Thm> {
        // cases = [⊢ P nil, ⊢ P xs ⟹ P (cons x xs)] (applied form, the
        // step over fresh `x : α`, `xs : list α`). `list_induct` wants the
        // step ∀-closed.
        let [base, step]: [Thm; 2] = cases
            .try_into()
            .map_err(|_| Error::ConnectiveRule("list induct: expected 2 cases".into()))?;
        let cons_case = step.all_intro("xs", list_ty())?.all_intro("x", elem())?; // ⊢ ∀x xs. P xs ⟹ P (cons x xs)
        list_induct(&elem(), motive, base, cons_case)
    }

    fn injective(&self, i: usize, xs: &[Term], ys: &[Term]) -> Result<Thm> {
        // Only `cons` (constructor 1) is injective-relevant.
        match (i, xs, ys) {
            (1, [x, xtl], [y, ytl]) => cons_inj(&elem(), x, xtl, y, ytl),
            _ => Err(Error::ConnectiveRule(format!(
                "list injective: no injectivity for constructor {i}"
            ))),
        }
    }

    fn distinct(&self, i: usize, j: usize, xs: &[Term], ys: &[Term]) -> Result<Thm> {
        // `nil_ne_cons x xs : ⊢ ¬(nil = cons x xs)`; bridge to `(Cᵢ = Cⱼ) ⟹ F`.
        match (i, j, xs, ys) {
            (0, 1, [], [y, ytl]) => {
                let eq = nil(elem()).equals(cons_app(y, ytl)?)?;
                nil_ne_cons(&elem(), y, ytl)?
                    .not_elim(Thm::assume(eq.clone())?)?
                    .imp_intro(&eq)
            }
            (1, 0, [x, xtl], []) => {
                let eq = cons_app(x, xtl)?.equals(nil(elem()))?;
                nil_ne_cons(&elem(), x, xtl)?
                    .not_elim(Thm::assume(eq.clone())?.sym()?)?
                    .imp_intro(&eq)
            }
            _ => Err(Error::ConnectiveRule(format!(
                "list distinct: no rule for constructors {i}, {j}"
            ))),
        }
    }
}

/// `cons x xs`.
fn cons_app(x: &Term, xs: &Term) -> Result<Term> {
    cons(elem()).apply(x.clone())?.apply(xs.clone())
}

// ============================================================================
// `list_foldr` — the catamorphic recursor, discharged from the engine's
// paramorphic recursion theorem.
// ============================================================================

use crate::init::eq::{beta_expand, beta_nf, beta_reduce};
use crate::init::logic::{exists_elim, exists_intro};
use covalence_core::subst;
use covalence_hol_eval::defs;

/// `β` — the fold's result type (the catalogue's generic `b`).
fn fold_beta() -> Type {
    Type::tfree("b")
}

/// `α → β → β` — the fold's step function type.
fn fold_f_ty() -> Type {
    Type::fun(elem(), Type::fun(fold_beta(), fold_beta()))
}

/// `β → (α → list α → β → β) → list α → β` — the **paramorphic** recursor
/// type the engine produces.
fn para_rec_ty() -> Type {
    Type::fun(
        fold_beta(),
        Type::fun(
            Type::fun(
                elem(),
                Type::fun(list_ty(), Type::fun(fold_beta(), fold_beta())),
            ),
            Type::fun(list_ty(), fold_beta()),
        ),
    )
}

/// The paramorphic recursor predicate `P_rec` at `β := b`:
/// `λr. ∀z f'. (r z f' nil = z) ∧ (∀x xs. r z f' (cons x xs) = f' x xs (r z f' xs))`.
fn para_pred() -> Term {
    let z = Term::free("z", fold_beta());
    let f = Term::free(
        "f",
        Type::fun(
            elem(),
            Type::fun(list_ty(), Type::fun(fold_beta(), fold_beta())),
        ),
    );
    let r = Term::free("r", para_rec_ty());
    let rzf = |t: Term| Term::app(Term::app(Term::app(r.clone(), z.clone()), f.clone()), t);
    let base = mk_eq(rzf(nil(elem())), z.clone());
    let x = Term::free("x", elem());
    let xs = Term::free("xs", list_ty());
    let lhs = rzf(cons(elem())
        .apply(x.clone())
        .unwrap()
        .apply(xs.clone())
        .unwrap());
    let rhs = Term::app(
        Term::app(Term::app(f.clone(), x.clone()), xs.clone()),
        rzf(xs.clone()),
    );
    let step = forall("x", elem(), forall("xs", list_ty(), mk_eq(lhs, rhs)));
    let body = forall(
        "z",
        fold_beta(),
        forall("f", f.type_of().unwrap(), and(base, step)),
    );
    abs("r", para_rec_ty(), body)
}

/// `⊢ ∃r. P_rec r` — the paramorphic list recursion theorem at `α,β` (the
/// catalogue's generic types).
fn para_recursion_theorem() -> Result<Thm> {
    let z = Term::free("z", fold_beta());
    let f = Term::free(
        "f",
        Type::fun(
            elem(),
            Type::fun(list_ty(), Type::fun(fold_beta(), fold_beta())),
        ),
    );
    crate::init::inductive::recursor::recursion_theorem(
        &ListTheory,
        &[z, f],
        &fold_beta(),
        &para_pred(),
    )
}

/// `⊢ list_foldr_predicate list_foldr` — **the `list_foldr` recursion
/// equations**, fully proved (no hypotheses). Discharges the catalogue's
/// Hilbert-ε `list_foldr`: the engine's paramorphic recursion theorem
/// yields a recursor `r`; the catamorphic fold `λf z. r z (λx xs acc. f x
/// acc)` satisfies `list_foldr_predicate`, and `spec_ax(list_foldr, ·)`
/// transfers the equations to `list_foldr` itself.
/// `⊢ list_foldr_predicate (foldr witness)`, polymorphic in `a, b`. **Cached**:
/// it calls the inductive engine's recursion theorem, so it is expensive and
/// input-independent — built once and shared. `foldr_holds_at` just
/// `inst_tfree`s it, so every list recursion lemma (`foldr_*`, `length_*`,
/// `cat_*`) reuses one build instead of rebuilding the recursor ~6× (the bulk
/// of `list_env` / `list.cov` evaluation time).
pub fn foldr_holds() -> Result<Thm> {
    static CACHE: std::sync::LazyLock<Thm> =
        std::sync::LazyLock::new(|| foldr_holds_uncached().expect("foldr_holds derivation"));
    Ok(CACHE.clone())
}

fn foldr_holds_uncached() -> Result<Thm> {
    // Under `P_rec r`, build the catamorphic witness and prove `pred witness`.
    let r = Term::free("r", para_rec_ty());
    let p_rec_r = beta_reduce(Thm::assume(Term::app(para_pred(), r.clone()))?)?; // {P_rec r} ⊢ ∀z f'. …

    // The fold predicate (catalogue), instantiated at α,β.
    let foldr_pred = defs::list_foldr_spec()
        .tm()
        .expect("list_foldr carries a selector predicate")
        .clone();

    // witness = λf z l. r z (λx xs acc. f x acc) l   :  (α→β→β)→β→list α→β.
    let witness = foldr_witness(&r);

    // ⊢ list_foldr_predicate witness  (under {P_rec r}).
    let pred_witness = prove_foldr_pred(&r, &witness, &foldr_pred, &p_rec_r)?;

    // ∃fr. list_foldr_predicate fr, discharging `P_rec r` via the engine's ∃.
    let ex_fr = exists_intro(foldr_pred.clone(), witness, pred_witness)?; // {P_rec r} ⊢ ∃fr. pred fr
    let step = ex_fr
        .imp_intro(&Term::app(para_pred(), r.clone()))?
        .all_intro("r", para_rec_ty())?; // ⊢ ∀r. P_rec r ⟹ ∃fr. pred fr
    let goal_ex = {
        // ∃fr. list_foldr_predicate fr (the bool target for exists_elim).
        let fr_ty = foldr_fr_ty();
        Term::app(defs::exists(fr_ty), foldr_pred.clone())
    };
    let some_fr = exists_elim(para_recursion_theorem()?, goal_ex, step)?; // ⊢ ∃fr. pred fr

    // spec_ax(list_foldr, w) : ⊢ pred w ⟹ pred list_foldr; exists_elim it.
    let foldr = defs::list_foldr(elem(), fold_beta());
    let w = Term::free("w", foldr_fr_ty());
    let transfer = Thm::spec_ax(foldr.clone(), w.clone())?.all_intro("w", foldr_fr_ty())?; // ⊢ ∀w. pred w ⟹ pred list_foldr
    let p_foldr = exists_elim(some_fr, Term::app(foldr_pred, foldr), transfer)?;
    beta_reduce(p_foldr)
}

/// `(α→β→β) → β → list α → β` — the `list_foldr` carrier type.
fn foldr_fr_ty() -> Type {
    Type::fun(
        fold_f_ty(),
        Type::fun(fold_beta(), Type::fun(list_ty(), fold_beta())),
    )
}

/// `λf z l. r z (λx xs acc. f x acc) l` — the catamorphic fold built from
/// the paramorphic recursor `r` (the `cons` step ignores the sub-list `xs`).
fn foldr_witness(r: &Term) -> Term {
    let f = Term::free("f", fold_f_ty());
    let z = Term::free("z", fold_beta());
    let l = Term::free("l", list_ty());
    // step' = λx xs acc. f x acc.
    let x = Term::free("x", elem());
    let acc = Term::free("acc", fold_beta());
    let f_x_acc = Term::app(Term::app(f.clone(), x.clone()), acc.clone());
    let step = abs(
        "x",
        elem(),
        abs("xs", list_ty(), abs("acc", fold_beta(), f_x_acc)),
    );
    let body = Term::app(Term::app(Term::app(r.clone(), z.clone()), step), l.clone());
    abs(
        "f",
        fold_f_ty(),
        abs("z", fold_beta(), abs("l", list_ty(), body)),
    )
}

/// `⊢ list_foldr_predicate witness`, under `{P_rec r}` — the catamorphic
/// fold built from the paramorphic recursor satisfies the fold equations.
fn prove_foldr_pred(r: &Term, witness: &Term, foldr_pred: &Term, p_rec_r: &Thm) -> Result<Thm> {
    // For fixed f, z: the paramorphic step `f' = λx xs acc. f x acc`.
    let f = Term::free("f", fold_f_ty());
    let z = Term::free("z", fold_beta());
    let x = Term::free("x", elem());
    let acc = Term::free("acc", fold_beta());
    let f_x_acc = Term::app(Term::app(f.clone(), x.clone()), acc.clone());
    let step_f = abs(
        "x",
        elem(),
        abs("xs", list_ty(), abs("acc", fold_beta(), f_x_acc)),
    );

    // P_rec r at z, step_f: (r z step_f nil = z) ∧ (∀x xs. r z step_f (cons x xs) = step_f x xs (r z step_f xs)).
    let pr = p_rec_r
        .clone()
        .all_elim(z.clone())?
        .all_elim(step_f.clone())?;
    let base_para = pr.clone().and_elim_l()?; // r z step_f nil = z
    let step_para = pr.and_elim_r()?; // ∀x xs. r z step_f (cons x xs) = step_f x xs (r z step_f xs)

    // witness f z l β-reduces to `r z step_f l`.
    let wfz = |t: Term| {
        Term::app(
            Term::app(Term::app(witness.clone(), f.clone()), z.clone()),
            t,
        )
    };
    let wfz_eq = |t: Term| -> Result<Thm> {
        // ⊢ witness f z t = r z step_f t  (β-normalise the witness application).
        beta_nf(wfz(t.clone())).trans(
            beta_nf(Term::app(
                Term::app(Term::app(r.clone(), z.clone()), step_f.clone()),
                t,
            ))
            .sym()?,
        )
    };

    // base: witness f z nil = r z step_f nil = z.
    let base = wfz_eq(nil(elem()))?.trans(base_para)?; // witness f z nil = z

    // step: ∀x xs. witness f z (cons x xs) = f x (witness f z xs).
    let xs = Term::free("xs", list_ty());
    let consed = cons(elem()).apply(x.clone())?.apply(xs.clone())?;
    let step_at_para = step_para.all_elim(x.clone())?.all_elim(xs.clone())?; // r z step_f (cons x xs) = step_f x xs (r z step_f xs)
    // step_f x xs (r z step_f xs) β-reduces to f x (r z step_f xs).
    let collapse = beta_nf(rhs_of(&step_at_para)?); // step_f x xs (...) = f x (r z step_f xs)
    let step_collapsed = step_at_para.trans(collapse)?; // r z step_f (cons x xs) = f x (r z step_f xs)
    // Bridge both sides to `witness`.
    let lhs_bridge = wfz_eq(consed.clone())?; // witness f z (cons x xs) = r z step_f (cons x xs)
    let rhs_bridge = wfz_eq(xs.clone())?.sym()?; // r z step_f xs = witness f z xs
    let rhs_cong = rhs_bridge.cong_arg(Term::app(f.clone(), x.clone()))?; // f x (r z step_f xs) = f x (witness f z xs)
    let step_eq = lhs_bridge.trans(step_collapsed)?.trans(rhs_cong)?; // witness f z (cons x xs) = f x (witness f z xs)
    let step = step_eq.all_intro("xs", list_ty())?.all_intro("x", elem())?;

    // base ∧ step, ∀-closed over f, z; then β-fold into `pred witness`.
    let body = base.and_intro(step)?; // (witness f z nil = z) ∧ (∀x xs. …)
    let closed = body
        .all_intro("z", fold_beta())?
        .all_intro("f", fold_f_ty())?; // ∀f z. …
    let _ = consed;
    beta_expand(foldr_pred, witness.clone(), closed)
}

// ============================================================================
// The `list_foldr` defining equations — the recursion clauses, at *arbitrary*
// element/result types `α, β` and arbitrary `f, z`. Projected out of
// `foldr_holds` (`⊢ list_foldr_predicate list_foldr`, β-reduced to the
// `∀f z` conjunction of nil/cons clauses) and re-typed at `α, β`. These are
// the seam givens `list.cov` (and the `length`/`cat`/`map` derivations below)
// build on.
// ============================================================================

/// `foldr_holds` at a chosen element type `α` and result type `β` — the
/// generic `a, b` are instantiated to `alpha, beta` so the clauses come out
/// at the caller's types. Returns `⊢ ∀f z. (foldr f z nil = z) ∧
/// (∀x xs. foldr f z (cons x xs) = f x (foldr f z xs))`.
fn foldr_holds_at(alpha: &Type, beta: &Type) -> Result<Thm> {
    foldr_holds()?
        .inst_tfree("a", alpha.clone())?
        .inst_tfree("b", beta.clone())
}

/// `⊢ list_foldr f z nil = z` — the right-fold base clause, at the given
/// `f : α → β → β` and `z : β`. Genuine (hypothesis- and oracle-free).
pub fn foldr_nil(alpha: &Type, beta: &Type, f: &Term, z: &Term) -> Result<Thm> {
    foldr_holds_at(alpha, beta)?
        .all_elim(f.clone())?
        .all_elim(z.clone())?
        .and_elim_l()
}

/// `⊢ list_foldr f z (cons x xs) = f x (list_foldr f z xs)` — the right-fold
/// step clause, at the given `f, z` and `x : α`, `xs : list α`. Genuine.
pub fn foldr_cons(
    alpha: &Type,
    beta: &Type,
    f: &Term,
    z: &Term,
    x: &Term,
    xs: &Term,
) -> Result<Thm> {
    foldr_holds_at(alpha, beta)?
        .all_elim(f.clone())?
        .all_elim(z.clone())?
        .and_elim_r()?
        .all_elim(x.clone())?
        .all_elim(xs.clone())
}

// ============================================================================
// `length` / `cat` (append) — the `foldr`-factored structural ops. Their
// nil/cons recursion clauses follow by δ-unfolding the op to its `foldr`
// body, β-reducing, applying the matching `foldr` clause, and folding the
// inner `foldr` application back to a recursive call.
// ============================================================================

/// `nat` (the result type of `length`).
fn nat_ty() -> Type {
    Type::nat()
}

/// `0 : nat`.
fn nat_zero() -> Term {
    covalence_hol_eval::mk_nat(0u32)
}

/// `succ n`.
fn succ(n: &Term) -> Term {
    Term::app(defs::nat_succ(), n.clone())
}

/// `list_length[α] xs` applied.
fn length_app(alpha: &Type, xs: &Term) -> Term {
    Term::app(defs::list_length(alpha.clone()), xs.clone())
}

/// The `length` fold step `λ_:α. λacc:nat. succ acc`, and its zero seed.
fn length_step(alpha: &Type) -> Term {
    let acc = Term::free("acc", nat_ty());
    abs("_", alpha.clone(), abs("acc", nat_ty(), succ(&acc)))
}

/// `⊢ list_length t = foldr step 0 t` — δ-unfold `length` to its `foldr`
/// body (`delta_all` walks the spine, then β collapses the applied λ).
fn length_unfold(alpha: &Type, t: &Term) -> Result<Thm> {
    length_app(alpha, t)
        .delta_all(defs::list_length_spec().symbol())?
        .rhs_conv(|u| u.reduce())
}

/// `⊢ list_length nil = 0` — the empty list has length zero. Genuine.
pub fn length_nil(alpha: &Type) -> Result<Thm> {
    let step = length_step(alpha);
    let unfold = length_unfold(alpha, &nil(alpha.clone()))?; // length nil = foldr step 0 nil
    let base = foldr_nil(alpha, &nat_ty(), &step, &nat_zero())?; // foldr step 0 nil = 0
    unfold.trans(base)
}

/// `⊢ list_length (cons x xs) = succ (list_length xs)` — length recurses
/// over `cons`. Genuine (hypothesis- and oracle-free).
pub fn length_cons(alpha: &Type, x: &Term, xs: &Term) -> Result<Thm> {
    let consed = cons(alpha.clone()).apply(x.clone())?.apply(xs.clone())?;
    let step = length_step(alpha);

    // length (cons x xs) = foldr step 0 (cons x xs)  (δ + β).
    let unfold = length_unfold(alpha, &consed)?;
    // foldr step 0 (cons x xs) = step x (foldr step 0 xs).
    let fc = foldr_cons(alpha, &nat_ty(), &step, &nat_zero(), x, xs)?;
    // β: step x (foldr step 0 xs) = succ (foldr step 0 xs).
    let collapse = rhs_of(&fc)?.reduce()?;
    // foldr step 0 xs = length xs  (reverse δ + β).
    let fold_back = length_unfold(alpha, xs)?.sym()?;
    let cong = fold_back.cong_arg(defs::nat_succ())?; // succ (foldr…) = succ (length xs)

    crate::init::eq::trans_chain([unfold, fc, collapse, cong])
}

/// `list_cat[α] xs ys` applied.
fn cat_app(alpha: &Type, xs: &Term, ys: &Term) -> Term {
    Term::app(
        Term::app(defs::list_cat(alpha.clone()), xs.clone()),
        ys.clone(),
    )
}

/// `⊢ list_cat t ys = foldr cons ys t` — δ-unfold `cat` to its `foldr`
/// body (`delta_all` spine walk + β).
fn cat_unfold(alpha: &Type, t: &Term, ys: &Term) -> Result<Thm> {
    cat_app(alpha, t, ys)
        .delta_all(defs::list_cat_spec().symbol())?
        .rhs_conv(|u| u.reduce())
}

/// `⊢ list_cat nil ys = ys` — appending onto `nil` is the identity (left
/// unit). Genuine (hypothesis- and oracle-free).
pub fn cat_nil(alpha: &Type, ys: &Term) -> Result<Thm> {
    let la = list(alpha.clone());
    let unfold = cat_unfold(alpha, &nil(alpha.clone()), ys)?; // cat nil ys = foldr cons ys nil
    let base = foldr_nil(alpha, &la, &cons(alpha.clone()), ys)?; // foldr cons ys nil = ys
    unfold.trans(base)
}

/// `⊢ list_cat (cons x xs) ys = cons x (list_cat xs ys)` — append recurses
/// over the left list's `cons`. Genuine (hypothesis- and oracle-free).
pub fn cat_cons(alpha: &Type, x: &Term, xs: &Term, ys: &Term) -> Result<Thm> {
    let la = list(alpha.clone());
    let consed = cons(alpha.clone()).apply(x.clone())?.apply(xs.clone())?;

    // cat (cons x xs) ys = foldr cons ys (cons x xs)  (δ + β).
    let unfold = cat_unfold(alpha, &consed, ys)?;
    // foldr cons ys (cons x xs) = cons x (foldr cons ys xs).
    let fc = foldr_cons(alpha, &la, &cons(alpha.clone()), ys, x, xs)?;
    // foldr cons ys xs = cat xs ys  (reverse δ + β).
    let fold_back = cat_unfold(alpha, xs, ys)?.sym()?;
    let cong = fold_back.cong_arg(Term::app(cons(alpha.clone()), x.clone()))?; // cons x (foldr…) = cons x (cat xs ys)

    crate::init::eq::trans_chain([unfold, fc, cong])
}

// --- small term helpers (kept local to keep the proof readable) ---

fn mk_eq(a: Term, b: Term) -> Term {
    crate::HolLightCtx::new()
        .mk_eq(a, b)
        .expect("mk_eq: well-typed")
}
fn and(a: Term, b: Term) -> Term {
    crate::HolLightCtx::new().mk_and(a, b)
}
fn forall(name: &str, ty: Type, body: Term) -> Term {
    crate::HolLightCtx::new().mk_forall(name, ty, body)
}
fn abs(name: &str, ty: Type, body: Term) -> Term {
    Term::abs(ty, subst::close(&body, name))
}
fn rhs_of(thm: &Thm) -> Result<Term> {
    Ok(thm.concl().as_eq().ok_or(Error::NotAnEquation)?.1.clone())
}

/// `option α` at the adapter's element type (unused export guard).
#[allow(dead_code)]
fn opt() -> Type {
    option(elem())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::init::eq::beta_reduce;
    use crate::init::inductive::{existence, recursor, uniqueness};
    use covalence_core::subst;

    /// The recursor result type `β` for the validation tests.
    fn beta() -> Type {
        Type::nat()
    }

    /// Step terms `[z, f]`: `z : β` (the `nil` image) and
    /// `f : α → list α → β → β` (the `cons` step).
    fn steps() -> [Term; 2] {
        let z = Term::free("z", beta());
        let f = Term::free(
            "f",
            Type::fun(elem(), Type::fun(list_ty(), Type::fun(beta(), beta()))),
        );
        [z, f]
    }

    #[test]
    fn graph_total_runs_through_list_induct() {
        // The existence layer (`∀l. ∃a. Graph l a`) consumes `ListTheory`'s
        // `induct` (= the derived `list_induct`). If it goes through, the
        // engine accepts `list`.
        let thm = existence::graph_total(&ListTheory, &steps(), &beta()).unwrap();
        assert!(thm.hyps().is_empty(), "graph_total must be axiom-free");
    }

    #[test]
    fn graph_base_inversion_is_axiom_free() {
        // `nil` inversion from the freeness feeders (`distinct`).
        let thm = uniqueness::graph_inv(&ListTheory, &steps(), &beta(), 0).unwrap();
        assert!(thm.hyps().is_empty());
    }

    #[test]
    fn graph_det_runs_through_list_induct() {
        let thm =
            crate::init::inductive::determinacy::graph_det(&ListTheory, &steps(), &beta()).unwrap();
        assert!(thm.hyps().is_empty(), "determinacy must be axiom-free");
    }

    #[test]
    fn foldr_holds_is_fully_proved() {
        // ⊢ list_foldr_predicate list_foldr — the catalogue fold's defining
        // equations, fully proved (no hypotheses).
        let thm = super::foldr_holds().unwrap();
        assert!(thm.hyps().is_empty(), "foldr_holds must be axiom-free");
        // It is `list_foldr_predicate list_foldr` (β-reduced to the
        // ∀f z conjunction of the nil/cons fold equations).
        assert!(thm.concl().type_of().unwrap().is_bool());
    }

    #[test]
    fn foldr_nil_and_cons_equations() {
        // Project the proved fold predicate into the two defining equations
        // at concrete f, z and check their shapes.
        let thm = super::foldr_holds().unwrap();
        let f = Term::free("f", super::fold_f_ty());
        let z = Term::free("z", super::fold_beta());
        let conj = thm
            .all_elim(f.clone())
            .unwrap()
            .all_elim(z.clone())
            .unwrap();
        let base = conj.clone().and_elim_l().unwrap(); // foldr f z nil = z
        assert!(base.hyps().is_empty());
        let (lhs, rhs) = base.concl().as_eq().unwrap();
        let foldr = covalence_hol_eval::defs::list_foldr(elem(), super::fold_beta());
        let foldr_f_z_nil = Term::app(
            Term::app(Term::app(foldr.clone(), f.clone()), z.clone()),
            nil(elem()),
        );
        assert_eq!(lhs, &foldr_f_z_nil);
        assert_eq!(rhs, &z);
        // step exists.
        let _step = conj.and_elim_r().unwrap();
    }

    #[test]
    fn recursion_theorem_for_list_is_axiom_free() {
        // The paramorphic recursor predicate: `λr. (r z f nil = z) ∧
        // (∀x xs. r z f (cons x xs) = f x xs (r z f xs))`. Build it and run
        // the engine's `recursion_theorem`; a successful, hypothesis-free
        // `∃r. P_rec r` is genuine `list` structural recursion.
        let [z, f] = steps();
        let pred = paramorphic_pred(&z, &f);
        let rt = recursor::recursion_theorem(&ListTheory, &[z, f], &beta(), &pred).unwrap();
        assert!(rt.hyps().is_empty(), "∃r. P_rec r must be axiom-free");
        assert!(rt.concl().type_of().unwrap().is_bool());
    }

    /// `λr. ∀z f. (r z f nil = z) ∧ (∀x xs. r z f (cons x xs) = f x xs (r z
    /// f xs))` — the paramorphic recursor predicate the engine ∃-introduces
    /// over. The engine abstracts the step variables `z, f`, so the
    /// predicate must ∀-quantify them (the inner `recursor` applications
    /// stay un-reduced, matching the engine's per-constructor equations).
    fn paramorphic_pred(z: &Term, f: &Term) -> Term {
        let f_ty = f.type_of().unwrap();
        let rec_ty = Type::fun(
            beta(),
            Type::fun(f_ty.clone(), Type::fun(list_ty(), beta())),
        );
        let r = Term::free("r", rec_ty.clone());
        let rzf = |t: Term| -> Term {
            Term::app(Term::app(Term::app(r.clone(), z.clone()), f.clone()), t)
        };
        // base: r z f nil = z.
        let base = rzf(nil(elem())).equals(z.clone()).unwrap();
        // step: ∀x xs. r z f (cons x xs) = f x xs (r z f xs).
        let x = Term::free("x", elem());
        let xs = Term::free("xs", list_ty());
        let consed = cons(elem())
            .apply(x.clone())
            .unwrap()
            .apply(xs.clone())
            .unwrap();
        let lhs = rzf(consed);
        let rhs = Term::app(
            Term::app(Term::app(f.clone(), x.clone()), xs.clone()),
            rzf(xs.clone()),
        );
        let step = lhs
            .equals(rhs)
            .unwrap()
            .forall("xs", list_ty())
            .unwrap()
            .forall("x", elem())
            .unwrap();
        // ∀z f. base ∧ step.
        let body = base
            .and(step)
            .unwrap()
            .forall("f", f_ty)
            .unwrap()
            .forall("z", beta())
            .unwrap();
        let _ = beta_reduce; // (kept for parity with the nat module's helpers)
        Term::abs(rec_ty, subst::close(&body, "r"))
    }

    // -- the foldr / length / cat equations --------------------------------

    #[test]
    fn foldr_clauses_are_genuine() {
        let f = Term::free("f", super::fold_f_ty());
        let z = Term::free("z", super::fold_beta());
        let x = Term::free("x", elem());
        let xs = Term::free("xs", list_ty());
        let nil_eq = super::foldr_nil(&elem(), &super::fold_beta(), &f, &z).unwrap();
        assert!(nil_eq.hyps().is_empty());
        let (l, r) = nil_eq.concl().as_eq().unwrap();
        let foldr = covalence_hol_eval::defs::list_foldr(elem(), super::fold_beta());
        assert_eq!(
            l,
            &Term::app(
                Term::app(Term::app(foldr.clone(), f.clone()), z.clone()),
                nil(elem())
            )
        );
        assert_eq!(r, &z);
        let cons_eq = super::foldr_cons(&elem(), &super::fold_beta(), &f, &z, &x, &xs).unwrap();
        assert!(cons_eq.hyps().is_empty());
    }

    #[test]
    fn length_clauses_are_genuine() {
        let x = Term::free("x", elem());
        let xs = Term::free("xs", list_ty());
        let ln = super::length_nil(&elem()).unwrap();
        assert!(ln.hyps().is_empty());
        let (l, r) = ln.concl().as_eq().unwrap();
        assert_eq!(
            l,
            &Term::app(covalence_hol_eval::defs::list_length(elem()), nil(elem()))
        );
        assert_eq!(r, &covalence_hol_eval::mk_nat(0u32));

        let lc = super::length_cons(&elem(), &x, &xs).unwrap();
        assert!(lc.hyps().is_empty());
        let (l, r) = lc.concl().as_eq().unwrap();
        let consed = cons(elem())
            .apply(x.clone())
            .unwrap()
            .apply(xs.clone())
            .unwrap();
        assert_eq!(
            l,
            &Term::app(covalence_hol_eval::defs::list_length(elem()), consed)
        );
        let expected_r = Term::app(
            covalence_hol_eval::defs::nat_succ(),
            Term::app(covalence_hol_eval::defs::list_length(elem()), xs.clone()),
        );
        assert_eq!(r, &expected_r);
    }

    #[test]
    fn cat_clauses_are_genuine() {
        let x = Term::free("x", elem());
        let xs = Term::free("xs", list_ty());
        let ys = Term::free("ys", list_ty());
        let cn = super::cat_nil(&elem(), &ys).unwrap();
        assert!(cn.hyps().is_empty());
        let (l, r) = cn.concl().as_eq().unwrap();
        let cat = covalence_hol_eval::defs::list_cat(elem());
        assert_eq!(
            l,
            &Term::app(Term::app(cat.clone(), nil(elem())), ys.clone())
        );
        assert_eq!(r, &ys);

        let cc = super::cat_cons(&elem(), &x, &xs, &ys).unwrap();
        assert!(cc.hyps().is_empty());
        let (l, r) = cc.concl().as_eq().unwrap();
        let consed = cons(elem())
            .apply(x.clone())
            .unwrap()
            .apply(xs.clone())
            .unwrap();
        assert_eq!(l, &Term::app(Term::app(cat.clone(), consed), ys.clone()));
        let cat_xs_ys = Term::app(Term::app(cat.clone(), xs.clone()), ys.clone());
        let expected_r = Term::app(Term::app(cons(elem()), x.clone()), cat_xs_ys);
        assert_eq!(r, &expected_r);
    }
}
