//! Phase-0 de-risking tests for the relation calculus + `TyRep`-in-base
//! (`notes/vibes/base-relcalc-holomega-design.md` §6). Exercised through the
//! public API (`execute`/`transpose`/`canon`/the equality calculus).
//!
//! These machine-check the load-bearing claims: `execute` is positive-only and
//! sound even under **nondeterminism/partiality** (the property that justifies
//! its existence), it is **zero-copy** over large I/O, the canon/execute duality
//! holds, transpose works ungated, and a `TyRep` equation transports through the
//! existing calculus.

use std::any::TypeId;
use std::cell::Cell;
use std::rc::Rc;
use std::sync::Arc;

use crate::*;

// ============================ demo language ============================

/// A demo relation language admitting exactly the four relations below (+ the
/// `HashOp` canonical-eval op for the duality test). Directly extends `()`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct RelCalc;

impl Language for RelCalc {
    fn admits(&self, r: TypeId) -> bool {
        r == TypeId::of::<Rel<HashFn>>()
            || r == TypeId::of::<Rel<AddModFn>>()
            || r == TypeId::of::<Rel<CoinFn>>()
            || r == TypeId::of::<Rel<PartialFn>>()
            || r == TypeId::of::<Rel<IncFn>>()
            || r == TypeId::of::<Rel<DblFn>>()
            || r == TypeId::of::<Rel<SubTwoFn>>()
            || r == TypeId::of::<HashOp>()
    }
    fn extends(&self, p: TypeId) -> bool {
        p == TypeId::of::<()>()
    }
    fn union(self, _: Self) -> Option<Self> {
        Some(RelCalc)
    }
    const MANIFEST: Option<&'static Manifest> = None;
}

// ============================ demo functions ============================

/// A deterministic, non-cryptographic 32-byte digest — a hermetic stand-in for a
/// real content hash (Phase 0 de-risks the *kernel seam*, not the hash). Real
/// `covalence-hash::Blake3`/`O256` wiring is a follow-up integration step.
fn digest(bytes: &[u8]) -> [u8; 32] {
    let mut out = [0u8; 32];
    let mut h: u64 = 0xcbf29ce484222325; // FNV-1a offset basis
    for (i, &b) in bytes.iter().enumerate() {
        h ^= b as u64;
        h = h.wrapping_mul(0x100000001b3);
        out[i % 32] ^= (h >> ((i % 8) * 8)) as u8;
    }
    out
}

/// `Bytes → O256`-shaped content hash, as an **untrusted relation** (the store /
/// content-addressing north star).
#[derive(Clone, Copy, Debug)]
struct HashFn;
impl UntrustedFn for HashFn {
    type In = Vec<u8>;
    type Out = [u8; 32];
    fn run(&self, a: &Vec<u8>) -> Result<[u8; 32], RelErr> {
        Ok(digest(a))
    }
}

/// The *same* hash as a pure [`CanonRule`] op (the duality: functional equation
/// vs. effectful membership).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct HashOp;
impl Op for HashOp {
    type In = Vec<u8>;
    type Out = [u8; 32];
}
impl CanonRule for HashOp {
    fn eval(&self, a: &Vec<u8>) -> Option<[u8; 32]> {
        Some(digest(a))
    }
}

/// `(u64, u64) → u64` add-mod — a deterministic-total stand-in for a WASM run.
#[derive(Clone, Copy, Debug)]
struct AddModFn;
impl UntrustedFn for AddModFn {
    type In = (u64, u64);
    type Out = u64;
    fn run(&self, a: &(u64, u64)) -> Result<u64, RelErr> {
        Ok((a.0.wrapping_add(a.1)) % 1_000_000_007)
    }
}

/// A **nondeterministic** `() → u64`: successive runs return *different* values
/// (a shared counter). Models a genuinely non-functional relation.
#[derive(Clone, Debug)]
struct CoinFn {
    ctr: Rc<Cell<u64>>,
}
impl UntrustedFn for CoinFn {
    type In = ();
    type Out = u64;
    fn run(&self, _: &()) -> Result<u64, RelErr> {
        let v = self.ctr.get();
        self.ctr.set(v + 1);
        Ok(v * 100 + 7) // 7, 107, 207, … — distinct across calls
    }
}

/// A **partial** `u64 → u64`: refuses (mints nothing) on odd inputs.
#[derive(Clone, Copy, Debug)]
struct PartialFn;
impl UntrustedFn for PartialFn {
    type In = u64;
    type Out = u64;
    fn run(&self, a: &u64) -> Result<u64, RelErr> {
        if a.is_multiple_of(2) {
            Ok(a / 2)
        } else {
            Err(RelErr::Refused)
        }
    }
}

/// `u64 → u64`, `n ↦ n+1` — a total relation for composition tests.
#[derive(Clone, Copy, Debug)]
struct IncFn;
impl UntrustedFn for IncFn {
    type In = u64;
    type Out = u64;
    fn run(&self, a: &u64) -> Result<u64, RelErr> {
        Ok(a + 1)
    }
}

/// `u64 → u64`, `n ↦ 2n`.
#[derive(Clone, Copy, Debug)]
struct DblFn;
impl UntrustedFn for DblFn {
    type In = u64;
    type Out = u64;
    fn run(&self, a: &u64) -> Result<u64, RelErr> {
        Ok(a * 2)
    }
}

/// `u64 → u64`, `n ↦ n-2` — agrees with `PartialFn` (`n/2`) at `n = 4` (both
/// give `2`), for the intersection test.
#[derive(Clone, Copy, Debug)]
struct SubTwoFn;
impl UntrustedFn for SubTwoFn {
    type In = u64;
    type Out = u64;
    fn run(&self, a: &u64) -> Result<u64, RelErr> {
        Ok(a - 2)
    }
}

// ============================ the tests ============================

/// **The test that justifies `execute`** (F6): membership is sound even for a
/// nondeterministic or partial `f`, exactly where `canon`'s functional equation
/// would be unsound.
#[test]
fn execute_nondeterministic_or_partial() {
    // --- nondeterminism: both observed outputs mint TRUE membership ---
    let coin = Rel(CoinFn {
        ctr: Rc::new(Cell::new(0)),
    });
    let t0 = execute(coin.clone(), (), RelCalc).expect("admitted + Ok");
    let t1 = execute(coin, (), RelCalc).expect("admitted + Ok");

    // Distinct outputs across the two runs (`b₀ = 7`, `b₁ = 107`) — both are in
    // the graph, so both `⊢ () Rel(Coin) bᵢ` hold. Neither is a functional
    // equation, and there is NO rule (here or anywhere in the base) that mints
    // `b₀ = b₁` or any negation — so `canon` would be unsound here while
    // `execute` membership is sound.
    let b0 = *t0.prop().1.1.0; // Ref(Arc<u64>).0 = Arc<u64>, deref → u64
    let b1 = *t1.prop().1.1.0;
    assert_eq!(b0, 7);
    assert_eq!(b1, 107);
    assert_ne!(b0, b1, "nondeterministic: the two observed outputs differ");
    // Both are genuine positive theorems in RelCalc.
    assert_eq!(*t0.lang(), RelCalc);
    assert_eq!(*t1.lang(), RelCalc);

    // --- partiality: a refused call mints NOTHING ---
    let ok = execute(Rel(PartialFn), 8u64, RelCalc).expect("even ⇒ Ok");
    assert_eq!(*ok.prop().1.1.0, 4u64); // 8 ↦ 4, observed membership
    let refused = execute(Rel(PartialFn), 7u64, RelCalc);
    assert!(
        matches!(refused, Err(Error::RuleFailed(_))),
        "odd ⇒ refused ⇒ no theorem minted (partial f proves no absence)"
    );
}

/// A WASM-shaped run mints membership; the never-false asymmetry holds (no
/// `execute` path or falsity rule yields a wrong output).
#[test]
fn execute_witnesses_wasm_shaped() {
    let thm = execute(Rel(AddModFn), (2u64, 3u64), RelCalc).expect("admitted");
    // `⊢ (2, 3) Rel(AddMod) 5`.
    assert_eq!(*thm.prop().1.0.0, (2u64, 3u64)); // Ref(Arc<(u64,u64)>).0 → deref
    assert_eq!(*thm.prop().1.1.0, 5u64); // Ref(Arc<u64>).0 → deref
    // The *wrong* output `6` is unobtainable: `execute` only ever mints what
    // `run` actually returned, and the base has no rule that mints `¬(a R b)` or
    // any competing membership without a corresponding run.
    assert_ne!(*thm.prop().1.1.0, 6u64);
}

/// Content-addressing over a ≥1 MB blob: O(1) materialized structure AND O(1)
/// copies — the payload lives behind an `Arc`, transport bumps a refcount.
#[test]
fn execute_content_address_o1_copies() {
    let blob = vec![0xABu8; 1 << 20]; // 1 MiB
    let expected = digest(&blob);
    let thm = execute(Rel(HashFn), blob, RelCalc).expect("admitted");

    // O(1) materialized nodes: the prop's in-memory size is a small constant
    // (two `Arc` pointers + a ZST op), INDEPENDENT of the megabyte payload.
    assert!(
        std::mem::size_of_val(thm.prop()) < 64,
        "prop structure is O(1), not O(blob)"
    );
    assert_eq!(*thm.prop().1.1.0, expected); // the hash came out right

    // Zero-copy transport: grab the blob's Arc, then clone the whole theorem and
    // observe a refcount bump on the SAME allocation (no megabyte copy).
    let arc_before = &thm.prop().1.0.0; // &Arc<Vec<u8>>
    assert_eq!(Arc::strong_count(arc_before), 1);
    let ptr_before = Arc::as_ptr(arc_before);

    let thm2 = thm.clone(); // transport — bumps refcount, does NOT copy the blob
    let arc_after = &thm2.prop().1.0.0;
    assert_eq!(
        Arc::strong_count(arc_after),
        2,
        "refcount bumped, not copied"
    );
    assert_eq!(
        Arc::as_ptr(arc_after),
        ptr_before,
        "same allocation — the 1 MiB blob was never duplicated"
    );
}

/// The canon/execute duality: the *same* hash as a `CanonRule` mints the
/// **functional** equation `⊢ hash(blob) = h` (and copies its `Val<Bytes>`),
/// contrasted with `execute`'s zero-copy **membership** form.
#[test]
fn canon_vs_execute_duality() {
    let blob = vec![1u8, 2, 3, 4];
    let h = digest(&blob);

    // canon: functional equation `⊢ App<HashOp, Val(blob)> = Val(h)`.
    let eq: Thm<RelCalc, Eqn<App<HashOp, Val<Vec<u8>>>, Val<[u8; 32]>>> =
        canon(HashOp, blob.clone(), RelCalc).expect("HashOp admitted");
    assert_eq!(eq.lhs(), &App(HashOp, Val(blob.clone())));
    assert_eq!(eq.rhs(), &Val(h));
    // NB `canon` OWNS a `Val<Vec<u8>>` — the blob is copied into the equation
    // (MF2: only the `execute` membership form is zero-copy).

    // execute: membership `⊢ blob Rel(Hash) h`, over a zero-copy `Ref<Arc<_>>`.
    let mem = execute(Rel(HashFn), blob, RelCalc).expect("Rel<HashFn> admitted");
    assert_eq!(*mem.prop().1.1.0, h); // same underlying computation, different seam
}

/// Transpose is an ungated-but-trusted method: `⊢ a R b` ⟹ `⊢ b R° a`.
#[test]
fn transpose_positive() {
    let thm = execute(Rel(AddModFn), (2u64, 3u64), RelCalc).expect("admitted");
    let t = thm.transpose();
    // `⊢ 5 Rel(AddMod)° (2, 3)` — pair swapped, op wrapped in `Transpose`.
    assert_eq!(*t.prop().1.0.0, 5u64); // first component now the output
    assert_eq!(*t.prop().1.1.0, (2u64, 3u64)); // second now the input pair
}

/// The rest of the positive calculus: **compose** (`R;S`), **join** (`R∪S`),
/// **meet** (`R∩S`) — all ungated-but-trusted, recombining positive facts.
#[test]
fn positive_calculus_compose_join_meet() {
    // compose: `⊢ 5 Inc 6` ∧ `⊢ 6 Dbl 12` ⟹ `⊢ 5 (Inc;Dbl) 12`. The middle `6`
    // is matched across the two theorems (fresh Arcs, but `Ref<Arc<u64>>: Eq`
    // compares the shared pointees, i.e. the values).
    let inc = execute(Rel(IncFn), 5u64, RelCalc).expect("Inc admitted"); // 5 ↦ 6
    let dbl = execute(Rel(DblFn), 6u64, RelCalc).expect("Dbl admitted"); // 6 ↦ 12
    let comp = inc.compose(dbl).expect("middle 6 matches");
    // `⊢ 5 (Inc;Dbl) 12` — endpoints preserved, op is `Compose(Inc, Dbl)`.
    assert_eq!(*comp.prop().1.0.0, 5u64);
    assert_eq!(*comp.prop().1.1.0, 12u64);

    // compose rejects a mismatched middle (5 Inc 6, but 7 Dbl 14 — 6 ≠ 7).
    let inc2 = execute(Rel(IncFn), 5u64, RelCalc).unwrap();
    let dbl2 = execute(Rel(DblFn), 7u64, RelCalc).unwrap();
    assert_eq!(inc2.compose(dbl2).unwrap_err(), Error::TransMismatch);

    // join: `⊢ 5 Inc 6` ⟹ `⊢ 5 (Inc∪Dbl) 6` (left injection, any other op).
    let inc3 = execute(Rel(IncFn), 5u64, RelCalc).unwrap();
    let j = inc3.join_l(Rel(DblFn));
    assert_eq!(*j.prop().1.0.0, 5u64);
    assert_eq!(*j.prop().1.1.0, 6u64);

    // meet: `⊢ 4 Partial 2` ∧ `⊢ 4 SubTwo 2` ⟹ `⊢ 4 (Partial∩SubTwo) 2` (both
    // operands matched). Rejects mismatched operands.
    let p = execute(Rel(PartialFn), 4u64, RelCalc).unwrap(); // 4 ↦ 2 (n/2)
    let s = execute(Rel(SubTwoFn), 4u64, RelCalc).unwrap(); // 4 ↦ 2 (n-2)
    let m = p.meet(s).expect("both endpoints (4, 2) match");
    assert_eq!(*m.prop().1.0.0, 4u64);
    assert_eq!(*m.prop().1.1.0, 2u64);

    // meet rejects when the pairs differ (4 Partial 2 vs 6 SubTwo 4).
    let p2 = execute(Rel(PartialFn), 4u64, RelCalc).unwrap();
    let s2 = execute(Rel(SubTwoFn), 6u64, RelCalc).unwrap(); // 6 ↦ 4
    assert_eq!(p2.meet(s2).unwrap_err(), Error::TransMismatch);
}

// ---- TyRep-in-base ----

/// An in-base demo type rep (the `C` Phase 0 commits to; MF1). Distinct values
/// are distinguishable via `Eq`, so `⊢ a = a'` is meaningful.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct TyRepDemo(u32);

/// A `TyRep` equation transports through the *existing* `cong_pair` + `cong_app`
/// calculus — no new rule — and is *meaningful* (distinct reps are not provably
/// equal).
#[test]
fn tyrep_in_base_transports() {
    let a = TyRepDemo(1);
    let b = TyRepDemo(9);

    // A proven leaf equation between reps (equal values ⇒ `of_eq` fires).
    let ea: Thm<(), Eqn<Val<TyRepDemo>, Val<TyRepDemo>>> = of_eq(a, a).expect("a == a");
    let eb: Thm<(), Eqn<Val<TyRepDemo>, Val<TyRepDemo>>> = of_eq(b, b).expect("b == b");

    // Combine into a pair equation, then push through the `TyFn` constructor.
    let pair_eq = ea.cong_pair(eb).expect("union of () contexts");
    let ty_eq = pair_eq.cong_app(ty_fn::<TyRepDemo>());
    // `⊢ TyFn(a, b) = TyFn(a, b)` as an `App`-spine over `Val` leaves — the
    // `TyRep`-in-base foothold, built with NO new rule.
    assert_eq!(ty_eq.lhs(), &App(ty_fn::<TyRepDemo>(), (Val(a), Val(b))));

    // Meaningfulness (F7): distinct reps are NOT provably equal — `of_eq` only
    // fires when the two `TyRepDemo` values are `Eq`-equal.
    assert!(
        of_eq::<TyRepDemo, ()>(TyRepDemo(1), TyRepDemo(2)).is_none(),
        "distinct type reps must not be provably equal"
    );
}

// ---- HOL-ω Kind sort in the base (B-K1) ----

/// A demo kind-rep sort (the `K` the base is generic over; picked by a consumer).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct Kdemo;

/// Reflected kinds (`⋆`, `⋆ ⇒ ⋆`) are well-formed base terms of the kind-rep sort,
/// and their equality/congruence come FREE from `refl`/`cong_pair`/`cong_app` — no
/// new rule, no `Thm::new` site. The `KStar`/`KArrow` ops are inert (uninterpreted).
#[test]
fn kind_sort_in_base_transports() {
    // `⋆` and `⋆ ⇒ ⋆` as base terms of sort `Kdemo`.
    let s = star::<Kdemo>(); // ⋆  = App(KStar, Val(()))
    let arrow = App(k_arrow::<Kdemo>(), (star::<Kdemo>(), star::<Kdemo>())); // ⋆ ⇒ ⋆
    fn is_kind<E: Expr<Ty = Kdemo>>(_: &E) {}
    is_kind(&s);
    is_kind(&arrow);

    // Congruence is free: from `⊢ ⋆ = ⋆` build `⊢ (⋆ ⇒ ⋆) = (⋆ ⇒ ⋆)` via
    // `cong_pair` + `cong_app(KArrow)` — the machinery applies to kind terms with
    // NO new rule (the point of B-K1).
    let refl_star: Thm<(), Eqn<_, _>> = Thm::refl(star::<Kdemo>(), ());
    let pair = refl_star
        .clone()
        .cong_pair(refl_star)
        .expect("union of () contexts");
    let arrow_eq = pair.cong_app(k_arrow::<Kdemo>());
    assert_eq!(
        arrow_eq.lhs(),
        &App(k_arrow::<Kdemo>(), (star::<Kdemo>(), star::<Kdemo>()))
    );
    // Both sides equal (well-formed reflexive kind equation).
    assert_eq!(arrow_eq.lhs(), arrow_eq.rhs());
}

/// Higher-rank HOL-ω binder syntax (B-K2): `TyAll`/`TyAbs`/`TyBound` build
/// well-formed base terms; de-Bruijn structural equality **is** α-equivalence;
/// and the existing `cong_pair`/`cong_app` calculus transports through the
/// binders — all with inert (uninterpreted) ops, no new rule.
#[test]
fn tyrep_binders_are_debruijn_and_transport() {
    // `∀(α : ⋆ : 0). α` as a base term of sort `TyRepDemo` — (kind, rank, body).
    // Every leaf is `Copy`, so the reflected term is `Copy` too.
    let arg = (
        star::<Kdemo>(),                         // κ = ⋆
        Val(0u32),                               // rank r = 0
        App(ty_bound::<TyRepDemo>(), Val(0u32)), // body = tyvar #0
    );
    let all1 = App(ty_all::<TyRepDemo, Kdemo>(), arg);
    let all2 = App(ty_all::<TyRepDemo, Kdemo>(), arg);
    fn is_ty<E: Expr<Ty = TyRepDemo>>(_: &E) {}
    is_ty(&all1);
    // De-Bruijn ⇒ one canonical form ⇒ structural equality is α-equivalence: two
    // independently-built `∀α.α` terms are equal with no α-renaming machinery.
    assert_eq!(all1, all2);

    // The calculus applies to binder terms (refl over the 3-tuple arg, then
    // `cong_app(TyAll)`) — no new rule.
    let r_arg: Thm<(), Eqn<_, _>> = Thm::refl(arg, ());
    let all_eq = r_arg.cong_app(ty_all::<TyRepDemo, Kdemo>());
    assert_eq!(all_eq.lhs(), &all1);

    // `λ(α : ⋆). α` (TyAbs, a 2-tuple arg) — congruence via `cong_pair` +
    // `cong_app`, showing sub-term equations transport into a binder equation.
    let kappa = star::<Kdemo>();
    let body = App(ty_bound::<TyRepDemo>(), Val(0u32));
    let rk: Thm<(), Eqn<_, _>> = Thm::refl(kappa, ());
    let rb: Thm<(), Eqn<_, _>> = Thm::refl(body, ());
    let pair = rk.cong_pair(rb).expect("union of () contexts");
    let abs_eq = pair.cong_app(ty_abs::<TyRepDemo, Kdemo>());
    assert_eq!(
        abs_eq.lhs(),
        &App(ty_abs::<TyRepDemo, Kdemo>(), (kappa, body))
    );
}
