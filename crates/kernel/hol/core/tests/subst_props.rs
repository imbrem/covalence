//! Property tests for the substitution / de Bruijn machinery in
//! `covalence_core::subst` — the largest TCB surface previously tested
//! by example only.
//!
//! Strategy: every optimized kernel operation (`close`, `close_var`,
//! `open`, `shift_by`, `subst_free` — with their Bloom-filter skips,
//! `bvi` skips, `Arc`-reuse short-circuits, and the type-stamping
//! `inst_typed` fast path) is checked against a **naive reference
//! implementation** written here with no caches and no sharing, on
//! randomized terms over the real kernel vocabulary (literals, `=`/`ε`,
//! `succ`, `defs/` catalogue leaves, `Def`s, spec coercions). On top of
//! the reference agreement we check the classical substitution lemmas a
//! paper proof would need (open/close round trips, shift inverses and
//! composition, the substitution commutation lemma, type preservation,
//! α-stability of renaming) and pin the sharing/caching contracts
//! (`Arc`-identity on no-op substitution, cached `bvi`/`ty` honesty
//! under rebuild).
//!
//! Case count: the committed default is modest for CI cost; run
//! `PROPTEST_CASES=2048 cargo test -p covalence-core --test subst_props`
//! for a generous local sweep. Every config below routes its count
//! through [`covalence_proptest::cases`] — an explicit `cases:` field
//! would otherwise *override* the env-derived default and silently
//! defeat the sweep.
//!
//! ## Bugs found by these properties (fixed in `src/subst.rs`)
//!
//! The `open_with` fast path (`inst_typed`) *trusted* the body's
//! well-typedness instead of verifying it. Reachable from the safe pub
//! API (`subst::open`) with an ill-typed body:
//!
//! 1. **panic** — an ill-typed *unchanged* subterm hit the
//!    `type_in_ctx` `.expect()` (e.g. `open(#0 (1 2), 0)`), and
//! 2. **false cached type** (soundness-class) — an ill-typed *changed*
//!    `App` took the trusting `_ => f_ty.clone()` codomain fallback, and
//!    the enclosing `Abs` stamped a wrong `TermInfo::Wf` type via
//!    `abs_with_ty`: `open(λ:nat. (#1 #0), 5u8)` returned `λ:nat. (5u8 #0)`
//!    with cached type `Ok(nat → u8)` even though the term is ill-typed
//!    — breaking the cached-type invariant every kernel rule trusts.
//!
//! Fix: `inst_typed` now *verifies* typing inline (mirroring
//! `type_of_in`'s `App` check) and aborts the fast path (`None`) on any
//! failure, falling back to the type-agnostic `inst_opt`. The
//! regression tests at the bottom pin both cases.

use std::collections::BTreeSet;
use std::sync::LazyLock;

use covalence_core::subst::{
    self, close, close_var, has_free_var, has_free_var_typed, is_closed, open, shift_by,
    subst_free, uses_bound_outer,
};
use covalence_core::{Term, TermKind, Thm, Type, TypeKind, Var, defs};
use covalence_proptest::cases;
use covalence_proptest::proptest::prelude::*;
use covalence_proptest::proptest::sample::{Index, select};
use covalence_proptest::proptest::strategy::Union;

// ===========================================================================
// Reference implementations — naive structural recursion, no bloom, no bvi
// skip, no Arc reuse, no type stamping. The specification the optimized
// kernel code must agree with.
// ===========================================================================

/// Reference [`close`]: name-only abstraction of a free variable.
fn ref_close(t: &Term, name: &str, depth: u32) -> Term {
    match t.kind() {
        TermKind::Free(v) if v.name() == name => Term::bound(depth),
        TermKind::App(f, x) => Term::app(ref_close(f, name, depth), ref_close(x, name, depth)),
        TermKind::Abs(ty, b) => Term::abs(ty.clone(), ref_close(b, name, depth + 1)),
        _ => t.clone(),
    }
}

/// Reference [`close_var`]: (name, type)-precise abstraction.
fn ref_close_var(t: &Term, var: &Var, depth: u32) -> Term {
    match t.kind() {
        TermKind::Free(v) if v == var => Term::bound(depth),
        TermKind::App(f, x) => {
            Term::app(ref_close_var(f, var, depth), ref_close_var(x, var, depth))
        }
        TermKind::Abs(ty, b) => Term::abs(ty.clone(), ref_close_var(b, var, depth + 1)),
        _ => t.clone(),
    }
}

/// Reference [`shift_by`]. Only called with shifts that cannot underflow.
fn ref_shift(t: &Term, delta: i64, cutoff: u32) -> Term {
    match t.kind() {
        TermKind::Bound(i) => {
            if *i < cutoff {
                t.clone()
            } else {
                let new = *i as i64 + delta;
                assert!(
                    (0..=u32::MAX as i64).contains(&new),
                    "ref_shift out of range"
                );
                Term::bound(new as u32)
            }
        }
        TermKind::App(f, x) => Term::app(ref_shift(f, delta, cutoff), ref_shift(x, delta, cutoff)),
        TermKind::Abs(ty, b) => Term::abs(ty.clone(), ref_shift(b, delta, cutoff + 1)),
        _ => t.clone(),
    }
}

/// Reference [`open`]: instantiate `Bound(depth) := u`, decrementing deeper
/// indices and shifting `u` by the binder depth.
fn ref_open(t: &Term, u: &Term, depth: u32) -> Term {
    match t.kind() {
        TermKind::Bound(i) => match i.cmp(&depth) {
            std::cmp::Ordering::Less => t.clone(),
            std::cmp::Ordering::Equal => ref_shift(u, depth as i64, 0),
            std::cmp::Ordering::Greater => Term::bound(i - 1),
        },
        TermKind::App(f, x) => Term::app(ref_open(f, u, depth), ref_open(x, u, depth)),
        TermKind::Abs(ty, b) => Term::abs(ty.clone(), ref_open(b, u, depth + 1)),
        _ => t.clone(),
    }
}

/// Reference [`subst_free`]: capture-avoiding free-variable substitution.
fn ref_subst_free(t: &Term, var: &Var, r: &Term, depth: u32) -> Term {
    match t.kind() {
        TermKind::Free(v) if v == var => ref_shift(r, depth as i64, 0),
        TermKind::App(f, x) => Term::app(
            ref_subst_free(f, var, r, depth),
            ref_subst_free(x, var, r, depth),
        ),
        TermKind::Abs(ty, b) => Term::abs(ty.clone(), ref_subst_free(b, var, r, depth + 1)),
        _ => t.clone(),
    }
}

/// Reference free-variable collection ((name, type)-precise).
fn ref_free_vars(t: &Term, out: &mut BTreeSet<Var>) {
    match t.kind() {
        TermKind::Free(v) => {
            out.insert(v.clone());
        }
        TermKind::App(f, x) => {
            ref_free_vars(f, out);
            ref_free_vars(x, out);
        }
        TermKind::Abs(_, b) => ref_free_vars(b, out),
        _ => {}
    }
}

/// Reference maximum free de Bruijn index (`-1` = closed) — the spec of
/// the cached [`Term::bvi`].
fn ref_bvi(t: &Term) -> i64 {
    match t.kind() {
        TermKind::Bound(i) => *i as i64,
        TermKind::App(f, x) => ref_bvi(f).max(ref_bvi(x)),
        TermKind::Abs(_, b) => (ref_bvi(b) - 1).max(-1),
        _ => -1,
    }
}

/// Reference [`uses_bound_outer`].
fn ref_uses_bound(t: &Term, target: u32, depth: u32) -> bool {
    match t.kind() {
        TermKind::Bound(i) => *i == target + depth,
        TermKind::App(f, x) => ref_uses_bound(f, target, depth) || ref_uses_bound(x, target, depth),
        TermKind::Abs(_, b) => ref_uses_bound(b, target, depth + 1),
        _ => false,
    }
}

/// Reference [`subst::find_free_type`]: first-in-traversal-order type of a
/// free variable named `name`.
fn ref_find_free_type(t: &Term, name: &str) -> Option<Type> {
    match t.kind() {
        TermKind::Free(v) if v.name() == name => Some(v.ty().clone()),
        TermKind::App(f, x) => ref_find_free_type(f, name).or_else(|| ref_find_free_type(x, name)),
        TermKind::Abs(_, b) => ref_find_free_type(b, name),
        _ => None,
    }
}

/// Structurally rebuild `t` through the plain smart constructors, forcing a
/// fresh `TermInfo` (bvi / bloom / cached-type) computation at every interior
/// node. Comparing the rebuilt term's cached summaries to the original's
/// checks that incremental construction (including `abs_with_ty` stamping)
/// never caches something the from-scratch type-checker wouldn't.
fn rebuild(t: &Term) -> Term {
    match t.kind() {
        TermKind::App(f, x) => Term::app(rebuild(f), rebuild(x)),
        TermKind::Abs(ty, b) => Term::abs(ty.clone(), rebuild(b)),
        _ => t.clone(),
    }
}

/// Assert the cached summaries of `t` agree with a from-scratch rebuild:
/// same structure, same `bvi`, same cached-type verdict and value.
fn assert_cached_info_honest(t: &Term) -> Result<(), TestCaseError> {
    let r = rebuild(t);
    prop_assert_eq!(t, &r, "rebuild must be structurally identical");
    prop_assert_eq!(t.bvi(), r.bvi(), "cached bvi disagrees with rebuild");
    prop_assert_eq!(t.bvi(), ref_bvi(t), "cached bvi disagrees with reference");
    match (t.ty(), r.ty()) {
        (Ok(a), Ok(b)) => prop_assert_eq!(a, b, "cached type disagrees with rebuild"),
        (Err(a), Err(b)) => prop_assert_eq!(a, b),
        (a, b) => prop_assert!(false, "cached ty verdict mismatch: {:?} vs {:?}", a, b),
    }
    Ok(())
}

/// Replace every occurrence of `var` with an opaque closed constant of the
/// same type. Used to establish `var ∉ fv(result)` side conditions.
fn purge_var(t: &Term, var: &Var) -> Term {
    ref_subst_free(t, var, &Term::const_("purged", var.ty().clone()), 0)
}

/// Wrap `t` in enough `λ:nat` binders to make it locally closed.
fn close_up(mut t: Term) -> Term {
    while t.bvi() >= 0 {
        t = Term::abs(Type::nat(), t);
    }
    t
}

// ===========================================================================
// Generators
// ===========================================================================

/// A `Def` leaf minted once through the real kernel rule (`Thm::define`).
fn def_leaf() -> Term {
    static DEF: LazyLock<Term> = LazyLock::new(|| {
        let thm: Thm = Thm::define("subst_props_c", Term::u8_lit(42)).expect("define");
        let (lhs, _) = thm.concl().as_eq().expect("define concl is an equation");
        lhs.clone()
    });
    DEF.clone()
}

/// Random types over the kernel vocabulary: base types, tvars, arrows, and
/// `defs/` catalogue specs (`option`/`stream`/`coprod`) — plus `u8` (a
/// nested subtype spec).
fn arb_ty() -> impl Strategy<Value = Type> {
    let leaf = prop_oneof![
        Just(Type::nat()),
        Just(Type::bool()),
        Just(Type::tfree("a")),
        Just(Type::tfree("b")),
        Just(defs::u8_ty()),
    ];
    leaf.prop_recursive(3, 8, 2, |inner| {
        prop_oneof![
            (inner.clone(), inner.clone()).prop_map(|(a, b)| Type::fun(a, b)),
            inner.clone().prop_map(defs::option),
            inner.clone().prop_map(defs::stream),
            (inner.clone(), inner).prop_map(|(a, b)| defs::coprod(a, b)),
        ]
    })
}

/// Raw random terms: possibly open (dangling `Bound`s), possibly ill-typed —
/// the full domain of the syntactic operations. Leaves cover every
/// substitution-relevant `TermKind` constructible outside the kernel:
/// literals, `=`/`ε`, `succ`, catalogue `Spec`s (`cond`/`fail`),
/// `SpecAbs`/`SpecRep` coercions, and a real `Def`.
fn arb_term() -> impl Strategy<Value = Term> {
    let leaf = prop_oneof![
        (0u32..5).prop_map(Term::bound),
        (prop_oneof![Just("x"), Just("y"), Just("z")], arb_ty())
            .prop_map(|(n, ty)| Term::free(n, ty)),
        arb_ty().prop_map(|ty| Term::const_("c", ty)),
        // Literal leaves: the fixed-width `SmallInt` family only — the
        // `nat_lit`/`int_lit`/`blob` constructors are under the toHOL-purge
        // ratchet (docs/deps/purge-ratchet.json), and all literal kinds are
        // uniform opaque leaves to the substitution machinery anyway.
        any::<u8>().prop_map(Term::u8_lit),
        any::<i16>().prop_map(Term::s16_lit),
        any::<u64>().prop_map(Term::u64_lit),
        any::<bool>().prop_map(Term::bool_lit),
        arb_ty().prop_map(Term::eq_op),
        arb_ty().prop_map(Term::select_op),
        Just(Term::succ()),
        arb_ty().prop_map(defs::cond),
        arb_ty().prop_map(defs::fail),
        Just(Term::spec_abs(defs::s8_spec(), Vec::<Type>::new())),
        Just(Term::spec_rep(defs::s8_spec(), Vec::<Type>::new())),
        Just(def_leaf()),
    ];
    leaf.prop_recursive(4, 24, 2, |inner| {
        prop_oneof![
            3 => (inner.clone(), inner.clone()).prop_map(|(f, x)| Term::app(f, x)),
            2 => (arb_ty(), inner).prop_map(|(ty, b)| Term::abs(ty, b)),
        ]
    })
}

/// The canonical free variable of a type: name derived from the type, so a
/// term built exclusively from `var_for` leaves never reuses one name at two
/// types (which `type_of` rejects).
fn var_for(ty: &Type) -> Var {
    Var::new(format!("v_{ty}"), ty.clone())
}

/// Well-typed term of type `ty` in binder context `ctx` (innermost binder
/// last, matching `TypeEnv`). Compositional: variables (`var_for`),
/// `Bound(i)` at matching binder types, literals, `fail : 'a`, plus — under
/// the depth budget — abstractions, applications, equations, and `cond`.
fn typed_term(ctx: Vec<Type>, ty: Type, depth: u32) -> BoxedStrategy<Term> {
    let mut opts: Vec<BoxedStrategy<Term>> = vec![
        Just(Term::free_var(var_for(&ty))).boxed(),
        Just(defs::fail(ty.clone())).boxed(),
    ];
    if ty == Type::bool() {
        opts.push(any::<bool>().prop_map(Term::bool_lit).boxed());
    }
    for (i, bty) in ctx.iter().rev().enumerate() {
        if *bty == ty {
            opts.push(Just(Term::bound(i as u32)).boxed());
        }
    }
    if depth > 0 {
        // λ-abstraction when the target is an arrow.
        if let TypeKind::Fun(dom, cod) = ty.kind() {
            let (dom, cod) = (dom.clone(), cod.clone());
            let mut ctx2 = ctx.clone();
            ctx2.push(dom.clone());
            opts.push(
                typed_term(ctx2, cod, depth - 1)
                    .prop_map(move |b| Term::abs(dom.clone(), b))
                    .boxed(),
            );
        }
        // Application at a small pool of argument types.
        for aty in [Type::nat(), Type::bool(), Type::tfree("a")] {
            let f = typed_term(ctx.clone(), Type::fun(aty.clone(), ty.clone()), depth - 1);
            let x = typed_term(ctx.clone(), aty, depth - 1);
            opts.push((f, x).prop_map(|(f, x)| Term::app(f, x)).boxed());
        }
        // Equations land at bool.
        if ty == Type::bool() {
            for ety in [Type::nat(), Type::tfree("a")] {
                let l = typed_term(ctx.clone(), ety.clone(), depth - 1);
                let r = typed_term(ctx.clone(), ety.clone(), depth - 1);
                opts.push(
                    (l, r)
                        .prop_map(move |(l, r)| {
                            Term::app(Term::app(Term::eq_op(ety.clone()), l), r)
                        })
                        .boxed(),
                );
            }
        }
        // `cond b x y : ty`.
        let c = typed_term(ctx.clone(), Type::bool(), depth - 1);
        let a = typed_term(ctx.clone(), ty.clone(), depth - 1);
        let b = typed_term(ctx, ty.clone(), depth - 1);
        let ty2 = ty;
        opts.push(
            (c, a, b)
                .prop_map(move |(c, a, b)| {
                    Term::app(Term::app(Term::app(defs::cond(ty2.clone()), c), a), b)
                })
                .boxed(),
        );
    }
    Union::new(opts).boxed()
}

/// Small pool of closed-form target types for the typed generator.
fn arb_target_ty() -> impl Strategy<Value = Type> {
    prop_oneof![
        Just(Type::nat()),
        Just(Type::bool()),
        Just(Type::tfree("a")),
        Just(Type::fun(Type::nat(), Type::nat())),
        Just(Type::fun(Type::nat(), Type::bool())),
        Just(Type::fun(
            Type::fun(Type::nat(), Type::bool()),
            Type::bool()
        )),
    ]
}

/// `(t, v, r)`: a closed well-typed `t`, a free variable `v` occurring in
/// `t` (or a definitely-absent one when `t` has no frees), and a closed
/// well-typed replacement `r : v.ty()`.
fn subst_type_case() -> BoxedStrategy<(Term, Var, Term)> {
    arb_target_ty()
        .prop_flat_map(|ty| typed_term(vec![], ty, 3))
        .prop_flat_map(|t| {
            let mut set = BTreeSet::new();
            ref_free_vars(&t, &mut set);
            let vars: Vec<Var> = set.into_iter().collect();
            if vars.is_empty() {
                let v = Var::new("v_absent", Type::nat());
                (Just(t), Just(v), typed_term(vec![], Type::nat(), 2)).boxed()
            } else {
                select(vars)
                    .prop_flat_map(move |v| {
                        let r = typed_term(vec![], v.ty().clone(), 2);
                        (Just(t.clone()), Just(v), r)
                    })
                    .boxed()
            }
        })
        .boxed()
}

/// Pick a free variable of `t` by index, or `None` if `t` has no frees.
fn pick_var(t: &Term, idx: &Index) -> Option<Var> {
    let mut set = BTreeSet::new();
    ref_free_vars(t, &mut set);
    let vars: Vec<Var> = set.into_iter().collect();
    if vars.is_empty() {
        None
    } else {
        Some(idx.get(&vars).clone())
    }
}

// ===========================================================================
// Reference agreement + cached-summary honesty (cheap, syntactic)
// ===========================================================================

proptest! {
    #![proptest_config(ProptestConfig {
        cases: cases(256),
        ..ProptestConfig::default()
    })]

    /// `close` agrees with the naive reference on arbitrary terms.
    #[test]
    fn prop_close_matches_reference(t in arb_term(), name in prop_oneof![Just("x"), Just("y"), Just("q")]) {
        prop_assert_eq!(close(&t, name), ref_close(&t, name, 0));
    }

    /// `close_var` agrees with the reference — (name, type)-precise, so a
    /// same-named variable at another type stays free.
    #[test]
    fn prop_close_var_matches_reference(t in arb_term(), ty in arb_ty(), name in prop_oneof![Just("x"), Just("y")]) {
        let v = Var::new(name, ty);
        prop_assert_eq!(close_var(&t, &v), ref_close_var(&t, &v, 0));
    }

    /// `subst_free` agrees with the reference (replacement may be open, so
    /// the depth-shift of the replacement is exercised).
    #[test]
    fn prop_subst_free_matches_reference(t in arb_term(), ty in arb_ty(), r in arb_term()) {
        let v = Var::new("x", ty);
        prop_assert_eq!(subst_free(&t, &v, &r), ref_subst_free(&t, &v, &r, 0));
    }

    /// `shift_by` agrees with the reference for non-negative deltas at
    /// arbitrary cutoffs (negative deltas are caller-checked; the safe
    /// round trip is covered separately).
    #[test]
    fn prop_shift_matches_reference(t in arb_term(), delta in 0i64..4, cutoff in 0u32..3) {
        prop_assert_eq!(shift_by(&t, delta, cutoff), ref_shift(&t, delta, cutoff));
    }

    /// `open` agrees with the reference on arbitrary bodies and
    /// replacements — this crosses both the `inst_typed` fast path
    /// (closed well-typed `u`, `bvi(body) <= 0`) and the general
    /// `inst_opt` path (open or ill-typed inputs), including the
    /// ill-typed-body fallback.
    #[test]
    fn prop_open_matches_reference(body in arb_term(), u in arb_term()) {
        prop_assert_eq!(open(&body, &u), ref_open(&body, &u, 0));
    }

    /// Cached `bvi` and `is_closed` agree with the reference definition.
    #[test]
    fn prop_bvi_matches_reference(t in arb_term()) {
        prop_assert_eq!(t.bvi(), ref_bvi(&t));
        prop_assert_eq!(t.is_closed(), ref_bvi(&t) < 0);
        prop_assert_eq!(is_closed(&t), ref_bvi(&t) < 0);
    }

    /// The free-variable queries agree with the reference — in particular
    /// the Bloom filter can never produce a false negative: a name that IS
    /// free must always be reported.
    #[test]
    fn prop_free_var_queries_match_reference(t in arb_term(), ty in arb_ty()) {
        for name in ["x", "y", "z", "nope"] {
            prop_assert_eq!(has_free_var(&t, name), ref_find_free_type(&t, name).is_some());
            prop_assert_eq!(subst::find_free_type(&t, name), ref_find_free_type(&t, name));
            let v = Var::new(name, ty.clone());
            let mut set = BTreeSet::new();
            ref_free_vars(&t, &mut set);
            prop_assert_eq!(has_free_var_typed(&t, &v), set.contains(&v));
        }
    }

    /// `uses_bound_outer` agrees with the reference.
    #[test]
    fn prop_uses_bound_outer_matches_reference(t in arb_term(), target in 0u32..4) {
        prop_assert_eq!(uses_bound_outer(&t, target), ref_uses_bound(&t, target, 0));
    }

    /// Cached summaries (bvi + type) are honest under a from-scratch
    /// rebuild, for raw generated terms.
    #[test]
    fn prop_cached_info_honest(t in arb_term()) {
        assert_cached_info_honest(&t)?;
    }

    /// Results of the de Bruijn operations also carry honest caches (this
    /// pins the `abs_with_ty` stamping and every incremental `TermInfo`).
    #[test]
    fn prop_op_results_have_honest_caches(t in arb_term(), u in arb_term(), ty in arb_ty()) {
        let v = Var::new("x", ty);
        assert_cached_info_honest(&open(&t, &u))?;
        assert_cached_info_honest(&close_var(&t, &v))?;
        assert_cached_info_honest(&subst_free(&t, &v, &u))?;
        assert_cached_info_honest(&shift_by(&t, 2, 1))?;
    }
}

// ===========================================================================
// Classical substitution lemmas + sharing contracts
// ===========================================================================

proptest! {
    #![proptest_config(ProptestConfig {
        cases: cases(256),
        ..ProptestConfig::default()
    })]

    /// Open-after-close round trip: for locally closed `t`,
    /// `open(close_var(t, v), v) == t`.
    #[test]
    fn prop_open_after_close_roundtrip(t0 in arb_term(), idx in any::<Index>()) {
        let t = close_up(t0);
        let v = pick_var(&t, &idx).unwrap_or_else(|| Var::new("v_absent", Type::nat()));
        let body = close_var(&t, &v);
        let reopened = open(&body, &Term::free_var(v));
        prop_assert_eq!(reopened, t);
    }

    /// Close-after-open round trip: for a binder body (`bvi <= 0`) and a
    /// variable `v` not free in it, `close_var(open(body, v), v) == body`.
    #[test]
    fn prop_close_after_open_roundtrip(t0 in arb_term(), idx in any::<Index>()) {
        let t = close_up(t0);
        let v = pick_var(&t, &idx).unwrap_or_else(|| Var::new("v_absent", Type::nat()));
        let body = close_var(&t, &v); // bvi <= 0 by construction
        prop_assert!(body.bvi() <= 0);
        let fresh = Var::new("ξfresh", Type::nat()); // generator never mints ξ names
        let opened = open(&body, &Term::free_var(fresh.clone()));
        prop_assert_eq!(close_var(&opened, &fresh), body);
    }

    /// Shift round trip and composition: up-then-down is the identity, and
    /// consecutive up-shifts add.
    #[test]
    fn prop_shift_roundtrip_and_composition(t in arb_term(), a in 0i64..4, b in 0i64..4, cutoff in 0u32..3) {
        let up = shift_by(&t, a, cutoff);
        prop_assert_eq!(shift_by(&up, -a, cutoff), t.clone(), "shift up then down");
        prop_assert_eq!(
            shift_by(&shift_by(&t, a, cutoff), b, cutoff),
            shift_by(&t, a + b, cutoff),
            "shift composition"
        );
    }

    /// The substitution commutation lemma: for `x ≠ y` with `x ∉ fv(v)`
    /// and closed `u`, `v`:
    /// `t[u/x][v/y] == t[v/y][ u[v/y] / x ]`.
    #[test]
    fn prop_subst_commutation(t in arb_term(), u0 in arb_term(), v0 in arb_term(), idx in any::<Index>(), idy in any::<Index>()) {
        let x = pick_var(&t, &idx).unwrap_or_else(|| Var::new("x", Type::nat()));
        let y = pick_var(&t, &idy).unwrap_or_else(|| Var::new("y", Type::bool()));
        prop_assume!(x != y);
        let u = close_up(u0);
        let v = purge_var(&close_up(v0), &x); // x ∉ fv(v)
        let lhs = subst_free(&subst_free(&t, &x, &u), &y, &v);
        let rhs = subst_free(&subst_free(&t, &y, &v), &x, &subst_free(&u, &y, &v));
        prop_assert_eq!(lhs, rhs);
    }

    /// α-stability of the de Bruijn operations: renaming a free variable to
    /// a fresh name commutes with closing —
    /// `close_var(t[y/x], y) == close_var(t, x)`.
    #[test]
    fn prop_rename_then_close_is_close(t in arb_term(), idx in any::<Index>()) {
        let x = pick_var(&t, &idx).unwrap_or_else(|| Var::new("x", Type::nat()));
        let y = Var::new("ξren", x.ty().clone()); // fresh by name discipline
        let renamed = subst_free(&t, &x, &Term::free_var(y.clone()));
        prop_assert_eq!(close_var(&renamed, &y), close_var(&t, &x));
    }

    /// No-op substitution returns the *same `Arc`* (the sharing-preserving
    /// `_opt` cores): substituting or closing a definitely-absent variable
    /// allocates nothing.
    #[test]
    fn prop_noop_subst_is_arc_identical(t in arb_term(), r in arb_term(), ty in arb_ty()) {
        let absent = Var::new("ξabsent", ty); // generator never mints ξ names
        let s = subst_free(&t, &absent, &r);
        prop_assert_eq!(s.ptr_id(), t.ptr_id(), "subst_free of absent var must reuse the Arc");
        let c = close_var(&t, &absent);
        prop_assert_eq!(c.ptr_id(), t.ptr_id(), "close_var of absent var must reuse the Arc");
        // Name-only close is bloom-gated (rebuilds on filter collision), so
        // only structural identity is guaranteed there.
        prop_assert_eq!(close(&t, "ξabsent"), t);
    }

    /// Shift no-ops are `Arc`-identical: `delta == 0` always, and any shift
    /// of a closed term (the `bvi` skip). Opening a closed body is likewise
    /// `Arc`-identical.
    #[test]
    fn prop_noop_shift_and_open_are_arc_identical(t in arb_term(), u in arb_term(), delta in -3i64..4, cutoff in 0u32..3) {
        prop_assert_eq!(shift_by(&t, 0, cutoff).ptr_id(), t.ptr_id());
        if t.is_closed() {
            prop_assert_eq!(shift_by(&t, delta, cutoff).ptr_id(), t.ptr_id());
            prop_assert_eq!(open(&t, &u).ptr_id(), t.ptr_id(), "open of a closed body is a no-op");
        }
    }
}

// ===========================================================================
// Typing properties (heavier generator — modest committed case count)
// ===========================================================================

proptest! {
    #![proptest_config(ProptestConfig {
        cases: cases(64),
        ..ProptestConfig::default()
    })]

    /// Generator sanity: `typed_term` really produces closed terms of the
    /// requested type.
    #[test]
    fn prop_typed_generator_sound((ty, t) in arb_target_ty().prop_flat_map(|ty| {
        let ty2 = ty.clone();
        typed_term(vec![], ty, 3).prop_map(move |t| (ty2.clone(), t))
    })) {
        prop_assert!(t.is_closed());
        prop_assert_eq!(t.type_of().expect("typed_term output must type-check"), ty);
    }

    /// The substitution lemma for typing: substituting a well-typed closed
    /// replacement of the variable's type preserves the term's type.
    #[test]
    fn prop_subst_free_preserves_type((t, v, r) in subst_type_case()) {
        let before = t.type_of().expect("generator output well-typed");
        prop_assert_eq!(r.type_of().expect("replacement well-typed"), v.ty().clone());
        let after = subst_free(&t, &v, &r);
        prop_assert_eq!(after.type_of().expect("substitution must preserve typing"), before);
        assert_cached_info_honest(&after)?;
    }

    /// β-instantiation preserves typing, and the `inst_typed` fast path's
    /// stamped types are honest: opening `body : cod` (under a binder of
    /// type `dom`) with `u : dom` yields a term of type `cod` whose cached
    /// summaries survive a from-scratch rebuild.
    #[test]
    fn prop_open_preserves_type_and_stamps_honestly((dom, cod, body, u) in
        (arb_target_ty(), arb_target_ty()).prop_flat_map(|(dom, cod)| {
            let body = typed_term(vec![dom.clone()], cod.clone(), 3);
            let u = typed_term(vec![], dom.clone(), 2);
            (Just(dom), Just(cod), body, u)
        })
    ) {
        // Sanity: λ:dom. body is well-typed at dom → cod.
        let lam = Term::abs(dom.clone(), body.clone());
        prop_assert_eq!(lam.type_of().expect("abs well-typed"), Type::fun(dom, cod.clone()));
        let opened = open(&body, &u);
        prop_assert_eq!(opened.type_of().expect("open must preserve typing"), cod);
        assert_cached_info_honest(&opened)?;
    }

    /// Type-variable instantiation commutes with typing (the `INST_TYPE`
    /// property): `type_of(t[σ/'a]) == type_of(t)[σ/'a]`.
    #[test]
    fn prop_subst_tfree_preserves_typing((t, sigma) in
        arb_target_ty()
            .prop_flat_map(|ty| typed_term(vec![], ty, 3))
            .prop_flat_map(|t| {
                let sigma = prop_oneof![
                    Just(Type::nat()),
                    Just(Type::bool()),
                    Just(Type::fun(Type::nat(), Type::bool())),
                ];
                (Just(t), sigma)
            })
    ) {
        let before = t.type_of().expect("generator output well-typed");
        let t2 = subst::subst_tfree_in_term(&t, "a", &sigma);
        prop_assert_eq!(
            t2.type_of().expect("tvar instantiation must preserve typing"),
            subst::subst_tfree_in_type(&before, "a", &sigma)
        );
        assert_cached_info_honest(&t2)?;
    }
}

// ===========================================================================
// Type-level substitution and matching
// ===========================================================================

proptest! {
    #![proptest_config(ProptestConfig {
        cases: cases(256),
        ..ProptestConfig::default()
    })]

    /// `match_types` recovers a substitution: for any pattern `p` and
    /// substitution `σ`, matching `p` against `p[σ]` succeeds and the
    /// recovered substitution reproduces `p[σ]` exactly (the property
    /// `Def::body` depends on).
    #[test]
    fn prop_match_types_recovers_substitution(p in arb_ty(), ra in arb_ty(), rb in arb_ty()) {
        let mut sub = std::collections::BTreeMap::new();
        sub.insert("a".into(), ra);
        sub.insert("b".into(), rb);
        let target = subst::subst_tfrees_in_type(&p, &sub);
        let mut recovered = std::collections::BTreeMap::new();
        prop_assert!(
            subst::match_types(&p, &target, &mut recovered).is_ok(),
            "matching a pattern against its own instance must succeed"
        );
        prop_assert_eq!(subst::subst_tfrees_in_type(&p, &recovered), target);
    }

    /// A singleton simultaneous substitution equals the single-variable
    /// one, at both the type and the term level.
    #[test]
    fn prop_subst_tfrees_singleton_equals_single(ty in arb_ty(), t in arb_term(), r in arb_ty()) {
        let mut sub = std::collections::BTreeMap::new();
        sub.insert("a".into(), r.clone());
        prop_assert_eq!(
            subst::subst_tfrees_in_type(&ty, &sub),
            subst::subst_tfree_in_type(&ty, "a", &r)
        );
        prop_assert_eq!(
            subst::subst_tfrees_in_term(&t, &sub),
            subst::subst_tfree_in_term(&t, "a", &r)
        );
    }

    /// The empty simultaneous substitution is an `Arc`-identical no-op.
    #[test]
    fn prop_subst_tfrees_empty_is_identity(ty in arb_ty(), t in arb_term()) {
        let sub = std::collections::BTreeMap::new();
        prop_assert_eq!(subst::subst_tfrees_in_type(&ty, &sub), ty);
        prop_assert_eq!(subst::subst_tfrees_in_term(&t, &sub).ptr_id(), t.ptr_id());
    }

    /// Sequential-vs-simultaneous decomposition: applying `'a := ra` then
    /// `'b := rb` equals the *simultaneous* `{a := ra[b := rb], b := rb}` —
    /// the algebraic law relating the two APIs (and exactly the law a
    /// cascading-fold implementation would violate on swaps).
    #[test]
    fn prop_type_subst_sequential_decomposition(ty in arb_ty(), ra in arb_ty(), rb in arb_ty()) {
        let seq = subst::subst_tfree_in_type(&subst::subst_tfree_in_type(&ty, "a", &ra), "b", &rb);
        let mut sub = std::collections::BTreeMap::new();
        sub.insert("a".into(), subst::subst_tfree_in_type(&ra, "b", &rb));
        sub.insert("b".into(), rb);
        prop_assert_eq!(seq, subst::subst_tfrees_in_type(&ty, &sub));
    }
}

// ===========================================================================
// Regressions pinned from property-test findings (see module docs)
// ===========================================================================

/// Finding 1: `open` used to panic (`type_in_ctx` `.expect()`) when the
/// body contained a closed ill-typed subterm alongside the substituted
/// index. It must fall back to the type-agnostic path instead.
#[test]
fn open_ill_typed_unchanged_subterm_falls_back_no_panic() {
    let ill = Term::app(Term::u8_lit(1), Term::u8_lit(2));
    let body = Term::app(Term::bound(0), ill.clone());
    let u = Term::u8_lit(0);
    let opened = open(&body, &u);
    assert_eq!(opened, Term::app(u, ill));
}

/// Finding 2 (soundness-class): `open` used to stamp a **false cached
/// type** on an ill-typed result — `open(λ:nat. (#1 #0), 5u8)` returned
/// `λ:nat. (5u8 #0)` with cached type `Ok(nat → u8)`. The cached type must
/// agree with a from-scratch type-check.
#[test]
fn open_ill_typed_app_does_not_stamp_false_type() {
    let body = Term::abs(Type::nat(), Term::app(Term::bound(1), Term::bound(0)));
    let u = Term::u8_lit(5);
    let opened = open(&body, &u);
    assert_eq!(
        opened,
        Term::abs(Type::nat(), Term::app(Term::u8_lit(5), Term::bound(0)))
    );
    // λ:nat. (5u8 #0) applies a u8 literal — ill-typed; the cache must say so.
    let rebuilt = rebuild(&opened);
    assert_eq!(
        opened.ty().is_ok(),
        rebuilt.ty().is_ok(),
        "cached type must not lie"
    );
    assert!(opened.ty().is_err(), "λ:nat. (5u8 #0) is ill-typed");
    assert!(opened.type_of().is_err());
}
