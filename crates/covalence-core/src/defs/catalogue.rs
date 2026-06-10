//! The kernel's lazy-static derived-type catalogue.
//!
//! Each entry is built once into a [`TypeSpecHandle`] via a
//! `LazyLock`. Public accessors return cheap handle clones; users
//! never see the underlying `Arc`. Two handles minted from the
//! same lazy static pointer-equal via [`TypeSpecHandle::ptr_eq`],
//! so `TypeKind::Spec(h, args)` leaves built through the
//! convenience constructors below pointer-equal at the spec
//! component without an interning step.
//!
//! Adding a new derived type is two changes:
//!
//! 1. Build the `TypeSpec`'s `ty` (the carrier) and `tm` (the
//!    selector predicate, often `λ_. T` for the unconditional
//!    `def name args := ty` shape) using kernel atoms.
//! 2. Park it behind a `LazyLock<TypeSpecHandle>` and write a
//!    `defs::*` accessor.
//!
//! Type-variable convention: factories use `TFree('a)`, `TFree('b)`,
//! … with letters in canonical (alphabetical) order. The
//! positional arg list at the `TypeKind::Spec` leaf matches
//! `spec.ty.free_tvars()` order.

use std::sync::LazyLock;

use crate::term::{Term, Type};

use super::canonical::Canonical;
use super::spec::{TermSpec, TermSpecHandle, TypeSpec, TypeSpecHandle};

/// The "any" predicate `λ_:τ. T` for the carrier type τ. Used by
/// every `def name args := ty` (no `where pred`) catalogue entry.
fn any(carrier: &Type) -> Term {
    Term::abs("_", carrier.clone(), Term::bool_lit(true))
}

// ============================================================================
// set 'a := 'a → bool
// ============================================================================

static SET_LAZY: LazyLock<TypeSpecHandle> = LazyLock::new(|| {
    let alpha = Type::tfree("a");
    let carrier = Type::fun(alpha, Type::bool());
    TypeSpecHandle::new(TypeSpec {
        symbol: Canonical::Set,
        ty: Some(carrier.clone()),
        tm: Some(any(&carrier)),
    })
});

/// `set 'a := 'a → bool` — the predicate-style encoding of sets
/// over a carrier type. Returns a cheap, process-shared handle.
pub fn set_spec() -> TypeSpecHandle {
    SET_LAZY.clone()
}

/// `set α` — the set type at carrier α.
pub fn set(alpha: Type) -> Type {
    Type::spec(set_spec(), vec![alpha])
}

// ============================================================================
// rel 'a 'b := 'a → 'b → bool
// ============================================================================

static REL_LAZY: LazyLock<TypeSpecHandle> = LazyLock::new(|| {
    let alpha = Type::tfree("a");
    let beta = Type::tfree("b");
    let carrier = Type::fun(alpha, Type::fun(beta, Type::bool()));
    TypeSpecHandle::new(TypeSpec {
        symbol: Canonical::Rel,
        ty: Some(carrier.clone()),
        tm: Some(any(&carrier)),
    })
});

/// `rel 'a 'b := 'a → 'b → bool` — heterogeneous relations.
/// Returns a cheap, process-shared handle.
pub fn rel_spec() -> TypeSpecHandle {
    REL_LAZY.clone()
}

/// `rel α β` — the relation type at carriers (α, β).
pub fn rel(alpha: Type, beta: Type) -> Type {
    Type::spec(rel_spec(), vec![alpha, beta])
}

// ============================================================================
// stream 'a := nat → 'a
// ============================================================================

static STREAM_LAZY: LazyLock<TypeSpecHandle> = LazyLock::new(|| {
    let alpha = Type::tfree("a");
    let carrier = Type::fun(Type::nat(), alpha);
    TypeSpecHandle::new(TypeSpec {
        symbol: Canonical::Stream,
        ty: Some(carrier.clone()),
        tm: Some(any(&carrier)),
    })
});

/// `stream 'a := nat → 'a` — infinite sequences indexed by nat.
/// Returns a cheap, process-shared handle.
pub fn stream_spec() -> TypeSpecHandle {
    STREAM_LAZY.clone()
}

/// `stream α` — the stream type at carrier α.
pub fn stream(alpha: Type) -> Type {
    Type::spec(stream_spec(), vec![alpha])
}

// ============================================================================
// coprod 'a 'b — disjoint union encoded as a relation
//
// def coprod 'a 'b := rel 'a 'b where
//   (λR. (∃a:'a. R = λx y. x = a) ∨ (∃b:'b. R = λx y. y = b))
//
// Carrier is the underlying function type `'a → 'b → bool` (= rel 'a 'b
// once we add alias-unfolding). Predicate selects relations that
// "encode" exactly one value of either α or β.
// ============================================================================

/// Build the coprod predicate at concrete carriers `α` and `β`:
/// `λR:α→β→bool. (∃a:α. R = λx y. x = a) ∨ (∃b:β. R = λx y. y = b)`.
fn coprod_predicate_at(alpha: Type, beta: Type) -> Term {
    use crate::hol;
    let rel_ty = Type::fun(alpha.clone(), Type::fun(beta.clone(), Type::bool()));

    let r = Term::free("R", rel_ty.clone());

    let p1 = {
        let a_free = Term::free("a", alpha.clone());
        let x_free = Term::free("x", alpha.clone());
        let inner = hol::hol_eq(x_free, a_free);
        let lam_y = hol::pub_abs("y", beta.clone(), inner);
        let lam_xy = hol::pub_abs("x", alpha.clone(), lam_y);
        let r_eq = hol::hol_eq(r.clone(), lam_xy);
        hol::hol_exists("a", alpha.clone(), r_eq)
    };
    let p2 = {
        let b_free = Term::free("b", beta.clone());
        let y_free = Term::free("y", beta.clone());
        let inner = hol::hol_eq(y_free, b_free);
        let lam_y = hol::pub_abs("y", beta.clone(), inner);
        let lam_xy = hol::pub_abs("x", alpha.clone(), lam_y);
        let r_eq = hol::hol_eq(r.clone(), lam_xy);
        hol::hol_exists("b", beta.clone(), r_eq)
    };

    let body = hol::hol_or(p1, p2);
    hol::pub_abs("R", rel_ty, body)
}

/// The polymorphic coprod predicate at `('a, 'b)` — what
/// `coprod_spec`'s `tm` field holds.
fn coprod_predicate() -> Term {
    coprod_predicate_at(Type::tfree("a"), Type::tfree("b"))
}

static COPROD_LAZY: LazyLock<TypeSpecHandle> = LazyLock::new(|| {
    let alpha = Type::tfree("a");
    let beta = Type::tfree("b");
    let carrier = Type::fun(alpha, Type::fun(beta, Type::bool()));
    TypeSpecHandle::new(TypeSpec {
        symbol: Canonical::Coprod,
        ty: Some(carrier),
        tm: Some(coprod_predicate()),
    })
});

/// `coprod 'a 'b := rel 'a 'b where (...)` — disjoint union.
/// Returns a cheap, process-shared handle.
pub fn coprod_spec() -> TypeSpecHandle {
    COPROD_LAZY.clone()
}

/// `coprod α β` — the disjoint union type at carriers (α, β).
pub fn coprod(alpha: Type, beta: Type) -> Type {
    Type::spec(coprod_spec(), vec![alpha, beta])
}

// ============================================================================
// prod 'a 'b — cartesian product encoded as a relation
//
// def prod 'a 'b := rel 'a 'b where
//   (λR. ∃a b. R = λx y. x = a ∧ y = b)
//
// Selects relations that "encode" exactly one pair (a, b).
// ============================================================================

fn prod_predicate() -> Term {
    use crate::hol;
    let alpha = Type::tfree("a");
    let beta = Type::tfree("b");
    let rel_ty = Type::fun(alpha.clone(), Type::fun(beta.clone(), Type::bool()));

    let r = Term::free("R", rel_ty.clone());

    // body: ∃a:α. ∃b:β. R = (λx:α. λy:β. x = a ∧ y = b)
    let body = {
        let a_free = Term::free("a", alpha.clone());
        let b_free = Term::free("b", beta.clone());
        let x_free = Term::free("x", alpha.clone());
        let y_free = Term::free("y", beta.clone());
        let eq_x_a = hol::hol_eq(x_free, a_free);
        let eq_y_b = hol::hol_eq(y_free, b_free);
        let conj = crate::hol::hol_and(eq_x_a, eq_y_b);
        let lam_y = hol::pub_abs("y", beta.clone(), conj);
        let lam_xy = hol::pub_abs("x", alpha.clone(), lam_y);
        let r_eq = hol::hol_eq(r.clone(), lam_xy);
        let inner_exists = hol::hol_exists("b", beta.clone(), r_eq);
        hol::hol_exists("a", alpha.clone(), inner_exists)
    };

    hol::pub_abs("R", rel_ty, body)
}


static PROD_LAZY: LazyLock<TypeSpecHandle> = LazyLock::new(|| {
    let alpha = Type::tfree("a");
    let beta = Type::tfree("b");
    let carrier = Type::fun(alpha, Type::fun(beta, Type::bool()));
    TypeSpecHandle::new(TypeSpec {
        symbol: Canonical::Prod,
        ty: Some(carrier),
        tm: Some(prod_predicate()),
    })
});

/// `prod 'a 'b := rel 'a 'b where (...)` — cartesian product.
/// Returns a cheap, process-shared handle.
pub fn prod_spec() -> TypeSpecHandle {
    PROD_LAZY.clone()
}

/// `prod α β` — the product type at carriers (α, β).
pub fn prod(alpha: Type, beta: Type) -> Type {
    Type::spec(prod_spec(), vec![alpha, beta])
}

// ============================================================================
// option 'a := coprod 'a unit
// ============================================================================

static OPTION_LAZY: LazyLock<TypeSpecHandle> = LazyLock::new(|| {
    // The carrier is `'a → unit → bool` (the underlying function
    // shape of `coprod 'a unit`). The predicate is *the same*
    // disjunction the coprod predicate computes at α and unit; we
    // delegate by reusing it.
    let alpha = Type::tfree("a");
    let carrier = Type::fun(alpha.clone(), Type::fun(Type::unit(), Type::bool()));

    // `tm = coprod_predicate` instantiated at β := unit, then η-equivalent
    // for option's carrier. For the MVP we just stash `coprod`'s
    // predicate term (it mentions `'b` which the catalogue user is
    // expected to instantiate consistently). A later refinement
    // would freshen β := unit here at static-init time.
    TypeSpecHandle::new(TypeSpec {
        symbol: Canonical::Option,
        ty: Some(carrier),
        tm: Some(coprod_predicate()),
    })
});

/// `option 'a := coprod 'a unit`.
pub fn option_spec() -> TypeSpecHandle {
    OPTION_LAZY.clone()
}

/// `option α` — option type at carrier α.
pub fn option(alpha: Type) -> Type {
    Type::spec(option_spec(), vec![alpha])
}

// ============================================================================
// Fixed-width unsigned integers — coprod chain doubling at each step
//
// u1 (bit) := coprod unit unit
// u2       := coprod bit bit
// u4       := coprod u2  u2
// u8       := coprod u4  u4
// u16      := coprod u8  u8
// u32      := coprod u16 u16
// u64      := coprod u32 u32
// u128     := coprod u64 u64
// u256     := coprod u128 u128
// u512     := coprod u256 u256
//
// Each is a 0-ary `TypeSpec`. The carrier is the underlying function
// type `prev → prev → bool` (the unfolded coprod-rel shape).
// ============================================================================

/// Build a fixed-width unsigned TypeSpec whose carrier is the
/// `coprod prev prev` underlying shape, with predicate
/// `coprod_predicate_at(prev, prev)`.
fn fixed_width_spec(symbol: Canonical, prev: Type) -> TypeSpecHandle {
    let carrier = Type::fun(prev.clone(), Type::fun(prev.clone(), Type::bool()));
    TypeSpecHandle::new(TypeSpec {
        symbol,
        ty: Some(carrier),
        tm: Some(coprod_predicate_at(prev.clone(), prev)),
    })
}

// Naming: 0-ary types use `*_ty()` for the Type accessor (avoiding
// clashes with Rust's primitive `u8` / `u16` / `u32` / ... names)
// and `*_spec()` for the underlying `TypeSpecHandle`.

static BIT_LAZY: LazyLock<TypeSpecHandle> =
    LazyLock::new(|| fixed_width_spec(Canonical::Bit, Type::unit()));

/// `u1 (bit) := coprod unit unit`.
pub fn bit_spec() -> TypeSpecHandle {
    BIT_LAZY.clone()
}
/// `bit` as a 0-ary `Type`.
pub fn bit_ty() -> Type {
    Type::spec(bit_spec(), vec![])
}

// The remaining widths chain via the previous width.
macro_rules! width {
    ($lazy:ident, $spec_fn:ident, $type_fn:ident, $canon:expr, $prev_fn:ident) => {
        static $lazy: LazyLock<TypeSpecHandle> =
            LazyLock::new(|| fixed_width_spec($canon, $prev_fn()));

        pub fn $spec_fn() -> TypeSpecHandle {
            $lazy.clone()
        }
        pub fn $type_fn() -> Type {
            Type::spec($spec_fn(), vec![])
        }
    };
}

width!(U2_LAZY, u2_spec, u2_ty, Canonical::U2, bit_ty);
width!(U4_LAZY, u4_spec, u4_ty, Canonical::U4, u2_ty);
width!(U8_LAZY, u8_spec, u8_ty, Canonical::U8, u4_ty);
width!(U16_LAZY, u16_spec, u16_ty, Canonical::U16, u8_ty);
width!(U32_LAZY, u32_spec, u32_ty, Canonical::U32, u16_ty);
width!(U64_LAZY, u64_spec, u64_ty, Canonical::U64, u32_ty);
width!(U128_LAZY, u128_spec, u128_ty, Canonical::U128, u64_ty);
width!(U256_LAZY, u256_spec, u256_ty, Canonical::U256, u128_ty);
width!(U512_LAZY, u512_spec, u512_ty, Canonical::U512, u256_ty);

// ============================================================================
// list 'a := stream (option 'a) where (eventually-none)
//
// The predicate selects streams where ∃n. for i < n the element is
// `some _` and for i ≥ n the element is `none`. Building this needs
// `natLt` / `natLe` / `some` / `none` as term-specs (term-level
// catalogue entries that don't yet exist in usable form). For now
// the carrier is correct but `tm` is the "any" placeholder — list α
// is currently *all* streams of options, not just finite ones. This
// is a known overreach; revisit when the term catalogue grows.
// ============================================================================

static LIST_LAZY: LazyLock<TypeSpecHandle> = LazyLock::new(|| {
    let alpha = Type::tfree("a");
    // carrier = stream (option α) = nat → (option α) = nat → carrier_of_option
    // We unfold option's carrier inline since option is parametric;
    // stream is also "nat → 'a" so stream (option α) carrier is
    // nat → α → unit → bool (option's unfolded carrier with α slotted).
    // For now we just use stream of option-alpha's *type* — kernel
    // builds the nominal `stream(option(α))` shape.
    let carrier = Type::fun(Type::nat(), option(alpha));
    let carrier_for_pred = carrier.clone();
    TypeSpecHandle::new(TypeSpec {
        symbol: Canonical::List,
        ty: Some(carrier),
        // TODO: replace with the eventually-none predicate once we have
        // `natLt` / `some` / `none` as usable term builders inside `defs`.
        tm: Some(any(&carrier_for_pred)),
    })
});

/// `list 'a := stream (option 'a) where (eventually-none)` —
/// finite-list type. **NOTE**: the `tm` predicate is currently the
/// `any` placeholder; `list α` is over-permissive.
pub fn list_spec() -> TypeSpecHandle {
    LIST_LAZY.clone()
}

/// `list α` — the finite-list type at carrier α.
pub fn list(alpha: Type) -> Type {
    Type::spec(list_spec(), vec![alpha])
}

// ============================================================================
// blob := list u8
// ============================================================================

static BLOB_LAZY: LazyLock<TypeSpecHandle> = LazyLock::new(|| {
    let carrier = Type::fun(Type::nat(), option(u8_ty()));
    let carrier_for_pred = carrier.clone();
    TypeSpecHandle::new(TypeSpec {
        symbol: Canonical::Blob,
        ty: Some(carrier),
        // TODO: same eventually-none predicate, instantiated at α := u8.
        tm: Some(any(&carrier_for_pred)),
    })
});

/// `blob := list u8`.
pub fn blob_spec() -> TypeSpecHandle {
    BLOB_LAZY.clone()
}

/// `blob` as a 0-ary `Type`.
pub fn blob_ty() -> Type {
    Type::spec(blob_spec(), vec![])
}

// ============================================================================
// result 'a 'b := coprod 'a 'b (alias — WASM component-model "result")
// ============================================================================

static RESULT_LAZY: LazyLock<TypeSpecHandle> = LazyLock::new(|| {
    // Same shape as coprod 'a 'b, just named "result" for the WASM
    // component-model surface.
    let alpha = Type::tfree("a");
    let beta = Type::tfree("b");
    let carrier = Type::fun(alpha.clone(), Type::fun(beta.clone(), Type::bool()));
    TypeSpecHandle::new(TypeSpec {
        symbol: Canonical::Result,
        ty: Some(carrier),
        tm: Some(coprod_predicate_at(alpha, beta)),
    })
});

/// `result 'a 'b := coprod 'a 'b`.
pub fn result_spec() -> TypeSpecHandle {
    RESULT_LAZY.clone()
}

/// `result α β` — the WASM-component-model result type.
pub fn result(alpha: Type, beta: Type) -> Type {
    Type::spec(result_spec(), vec![alpha, beta])
}

// ============================================================================
// signed1 'a := prod bit 'a — "value + sign" representation
// signed2 'a := prod bit 'a — two's-complement-style
//
// Both share the carrier `bit → α → bool` and the prod predicate
// (instantiated at bit, α). The semantic split — interpret as "a or
// −a" (signed1) vs "a or −(a+1)" (signed2) — lives outside the
// kernel's structural definition; the `tm` predicate is the same.
// ============================================================================

fn build_signed_spec(symbol: Canonical) -> TypeSpecHandle {
    let alpha = Type::tfree("a");
    let bit_t = bit_ty();
    let carrier = Type::fun(bit_t.clone(), Type::fun(alpha.clone(), Type::bool()));
    TypeSpecHandle::new(TypeSpec {
        symbol,
        ty: Some(carrier),
        tm: Some(prod_predicate_at(bit_t, alpha)),
    })
}

/// Concrete-types version of the prod selector.
fn prod_predicate_at(alpha: Type, beta: Type) -> Term {
    use crate::hol;
    let rel_ty = Type::fun(alpha.clone(), Type::fun(beta.clone(), Type::bool()));
    let r = Term::free("R", rel_ty.clone());

    let body = {
        let a_free = Term::free("a", alpha.clone());
        let b_free = Term::free("b", beta.clone());
        let x_free = Term::free("x", alpha.clone());
        let y_free = Term::free("y", beta.clone());
        let eq_x_a = hol::hol_eq(x_free, a_free);
        let eq_y_b = hol::hol_eq(y_free, b_free);
        let conj = crate::hol::hol_and(eq_x_a, eq_y_b);
        let lam_y = hol::pub_abs("y", beta.clone(), conj);
        let lam_xy = hol::pub_abs("x", alpha.clone(), lam_y);
        let r_eq = hol::hol_eq(r.clone(), lam_xy);
        let inner_exists = hol::hol_exists("b", beta.clone(), r_eq);
        hol::hol_exists("a", alpha.clone(), inner_exists)
    };

    hol::pub_abs("R", rel_ty, body)
}

static SIGNED1_LAZY: LazyLock<TypeSpecHandle> =
    LazyLock::new(|| build_signed_spec(Canonical::Signed1));
static SIGNED2_LAZY: LazyLock<TypeSpecHandle> =
    LazyLock::new(|| build_signed_spec(Canonical::Signed2));

/// `signed1 'a := prod bit 'a` — value + sign bit; pair interpreted
/// as `(s, a) ↦ if s then a else −a`.
pub fn signed1_spec() -> TypeSpecHandle {
    SIGNED1_LAZY.clone()
}

/// `signed1 α`.
pub fn signed1(alpha: Type) -> Type {
    Type::spec(signed1_spec(), vec![alpha])
}

/// `signed2 'a := prod bit 'a` — two's-complement-style; pair
/// interpreted as `(s, a) ↦ if s then a else −(a+1)`.
pub fn signed2_spec() -> TypeSpecHandle {
    SIGNED2_LAZY.clone()
}

/// `signed2 α`.
pub fn signed2(alpha: Type) -> Type {
    Type::spec(signed2_spec(), vec![alpha])
}

// ============================================================================
// F32 := u32, F64 := u64 — bitwise aliases for IEEE 754 floats.
// ============================================================================

static F32_LAZY: LazyLock<TypeSpecHandle> = LazyLock::new(|| {
    // f32's carrier is u32's carrier (it IS u32 bitwise).
    let u32_handle_carrier = u32_spec()
        .as_spec()
        .ty
        .clone()
        .expect("u32 has carrier");
    let u32_handle_tm = u32_spec()
        .as_spec()
        .tm
        .clone()
        .expect("u32 has tm");
    TypeSpecHandle::new(TypeSpec {
        symbol: Canonical::F32,
        ty: Some(u32_handle_carrier),
        tm: Some(u32_handle_tm),
    })
});

static F64_LAZY: LazyLock<TypeSpecHandle> = LazyLock::new(|| {
    let u64_handle_carrier = u64_spec()
        .as_spec()
        .ty
        .clone()
        .expect("u64 has carrier");
    let u64_handle_tm = u64_spec()
        .as_spec()
        .tm
        .clone()
        .expect("u64 has tm");
    TypeSpecHandle::new(TypeSpec {
        symbol: Canonical::F64,
        ty: Some(u64_handle_carrier),
        tm: Some(u64_handle_tm),
    })
});

/// `f32 := u32` — bitwise; floating-point ops + axiomatisation
/// against `real` land later.
pub fn f32_spec() -> TypeSpecHandle {
    F32_LAZY.clone()
}
/// `f32` as a 0-ary `Type`.
pub fn f32_ty() -> Type {
    Type::spec(f32_spec(), vec![])
}

/// `f64 := u64`.
pub fn f64_spec() -> TypeSpecHandle {
    F64_LAZY.clone()
}
/// `f64` as a 0-ary `Type`.
pub fn f64_ty() -> Type {
    Type::spec(f64_spec(), vec![])
}

// ============================================================================
// Relation properties: preord / pord / per / part
//
// These are 1-ary specs whose carrier is `rel 'a 'a = 'a → 'a → bool`
// and whose predicate selects the relations satisfying a particular
// algebraic property:
//
// - preord 'a: transitive + reflexive
// - pord   'a: transitive + reflexive + antisymmetric
// - per    'a: transitive + symmetric
// - part   'a: transitive + symmetric + reflexive (partial equivalence
//   relation, total over its domain)
//
// Each is built from the per-property building-block predicates
// `transitive_pred(α)`, `reflexive_pred(α)`, `symmetric_pred(α)`,
// `antisymmetric_pred(α)` — each a `λR. ∀…. …` term that selects R
// satisfying the property.
// ============================================================================

/// `λR:α→α→bool. ∀x y z. R x y ⟹ R y z ⟹ R x z`
fn transitive_pred(alpha: Type) -> Term {
    use crate::hol;
    let r_ty = Type::fun(alpha.clone(), Type::fun(alpha.clone(), Type::bool()));
    let r = Term::free("R", r_ty.clone());
    let x = Term::free("x", alpha.clone());
    let y = Term::free("y", alpha.clone());
    let z = Term::free("z", alpha.clone());
    let r_xy = Term::app(Term::app(r.clone(), x.clone()), y.clone());
    let r_yz = Term::app(Term::app(r.clone(), y.clone()), z.clone());
    let r_xz = Term::app(Term::app(r.clone(), x.clone()), z.clone());
    let body = hol::hol_imp(r_xy, hol::hol_imp(r_yz, r_xz));
    let all_z = hol::hol_forall("z", alpha.clone(), body);
    let all_yz = hol::hol_forall("y", alpha.clone(), all_z);
    let all_xyz = hol::hol_forall("x", alpha.clone(), all_yz);
    hol::pub_abs("R", r_ty, all_xyz)
}

/// `λR:α→α→bool. ∀x. R x x`
fn reflexive_pred(alpha: Type) -> Term {
    use crate::hol;
    let r_ty = Type::fun(alpha.clone(), Type::fun(alpha.clone(), Type::bool()));
    let r = Term::free("R", r_ty.clone());
    let x = Term::free("x", alpha.clone());
    let r_xx = Term::app(Term::app(r.clone(), x.clone()), x);
    let body = hol::hol_forall("x", alpha.clone(), r_xx);
    hol::pub_abs("R", r_ty, body)
}

/// `λR:α→α→bool. ∀x y. R x y ⟹ R y x`
fn symmetric_pred(alpha: Type) -> Term {
    use crate::hol;
    let r_ty = Type::fun(alpha.clone(), Type::fun(alpha.clone(), Type::bool()));
    let r = Term::free("R", r_ty.clone());
    let x = Term::free("x", alpha.clone());
    let y = Term::free("y", alpha.clone());
    let r_xy = Term::app(Term::app(r.clone(), x.clone()), y.clone());
    let r_yx = Term::app(Term::app(r.clone(), y.clone()), x.clone());
    let body = hol::hol_imp(r_xy, r_yx);
    let all_y = hol::hol_forall("y", alpha.clone(), body);
    let all_xy = hol::hol_forall("x", alpha.clone(), all_y);
    hol::pub_abs("R", r_ty, all_xy)
}

/// `λR:α→α→bool. ∀x y. R x y ⟹ R y x ⟹ x = y`
fn antisymmetric_pred(alpha: Type) -> Term {
    use crate::hol;
    let r_ty = Type::fun(alpha.clone(), Type::fun(alpha.clone(), Type::bool()));
    let r = Term::free("R", r_ty.clone());
    let x = Term::free("x", alpha.clone());
    let y = Term::free("y", alpha.clone());
    let r_xy = Term::app(Term::app(r.clone(), x.clone()), y.clone());
    let r_yx = Term::app(Term::app(r.clone(), y.clone()), x.clone());
    let x_eq_y = hol::hol_eq(x.clone(), y.clone());
    let body = hol::hol_imp(r_xy, hol::hol_imp(r_yx, x_eq_y));
    let all_y = hol::hol_forall("y", alpha.clone(), body);
    let all_xy = hol::hol_forall("x", alpha.clone(), all_y);
    hol::pub_abs("R", r_ty, all_xy)
}

/// Combine a sequence of property predicates over the same carrier
/// `α → α → bool` into a single λR. ∧ properties. Uses `App` to
/// apply each property to R, then folds with `∧`.
fn combine_props(alpha: Type, props: &[fn(Type) -> Term]) -> Term {
    use crate::hol;
    let r_ty = Type::fun(alpha.clone(), Type::fun(alpha.clone(), Type::bool()));
    let r = Term::free("R", r_ty.clone());
    // Apply each property predicate to R, getting a list of bool terms.
    let mut applications: Vec<Term> = props
        .iter()
        .map(|p| Term::app(p(alpha.clone()), r.clone()))
        .collect();
    // Conjoin left-to-right.
    let mut result = applications.remove(0);
    for next in applications {
        result = hol::hol_and(result, next);
    }
    hol::pub_abs("R", r_ty, result)
}

/// Builder for a 1-ary relation-property spec: carrier `α → α → bool`,
/// predicate is the combined-property predicate.
fn rel_property_spec(symbol: Canonical, props: &[fn(Type) -> Term]) -> TypeSpecHandle {
    let alpha = Type::tfree("a");
    let carrier = Type::fun(alpha.clone(), Type::fun(alpha.clone(), Type::bool()));
    TypeSpecHandle::new(TypeSpec {
        symbol,
        ty: Some(carrier),
        tm: Some(combine_props(alpha, props)),
    })
}

static PREORD_LAZY: LazyLock<TypeSpecHandle> = LazyLock::new(|| {
    rel_property_spec(Canonical::Preord, &[transitive_pred, reflexive_pred])
});

/// `preord 'a := rel 'a 'a where (transitive ∧ reflexive)`.
pub fn preord_spec() -> TypeSpecHandle {
    PREORD_LAZY.clone()
}
/// `preord α`.
pub fn preord(alpha: Type) -> Type {
    Type::spec(preord_spec(), vec![alpha])
}

static POR_LAZY: LazyLock<TypeSpecHandle> = LazyLock::new(|| {
    rel_property_spec(
        Canonical::Pord,
        &[transitive_pred, reflexive_pred, antisymmetric_pred],
    )
});

/// `pord 'a := rel 'a 'a where (transitive ∧ reflexive ∧ antisymmetric)`.
pub fn pord_spec() -> TypeSpecHandle {
    POR_LAZY.clone()
}
/// `pord α`.
pub fn pord(alpha: Type) -> Type {
    Type::spec(pord_spec(), vec![alpha])
}

static PER_LAZY: LazyLock<TypeSpecHandle> = LazyLock::new(|| {
    rel_property_spec(Canonical::Per, &[transitive_pred, symmetric_pred])
});

/// `per 'a := rel 'a 'a where (transitive ∧ symmetric)`.
pub fn per_spec() -> TypeSpecHandle {
    PER_LAZY.clone()
}
/// `per α` — partial equivalence relation.
pub fn per(alpha: Type) -> Type {
    Type::spec(per_spec(), vec![alpha])
}

static PART_LAZY: LazyLock<TypeSpecHandle> = LazyLock::new(|| {
    rel_property_spec(
        Canonical::Part,
        &[transitive_pred, symmetric_pred, reflexive_pred],
    )
});

/// `part 'a := rel 'a 'a where (transitive ∧ symmetric ∧ reflexive)`.
pub fn part_spec() -> TypeSpecHandle {
    PART_LAZY.clone()
}
/// `part α` — total equivalence relation.
pub fn part(alpha: Type) -> Type {
    Type::spec(part_spec(), vec![alpha])
}

// ============================================================================
// close / quot factories
//
// From docs/type-hierarchy.md:
//   def name args := { car } close pred:
//     ty = car → bool
//     tm = λS. (∀x y. pred x y ⟹ S x ⟹ S y) ∧ (∃x. S x)
//   def name args := car quot pred:
//     ≡ { car } close (λx y. pred x y ∨ pred y x)
//
// Both factories take a concrete car (Type) and pred (Term of type
// car → car → bool) — they don't try to be polymorphic; the caller
// is expected to bake in the relevant type so the resulting spec is
// fully self-contained. (Generic versions can land later if we want
// catalogue entries parametric in their pred.)
// ============================================================================

/// Build `λS:car→bool. (∀x y. pred x y ⟹ S x ⟹ S y) ∧ (∃x. S x)`.
fn close_predicate(car: Type, pred: Term) -> Term {
    use crate::hol;
    let carrier = Type::fun(car.clone(), Type::bool());
    let s = Term::free("S", carrier.clone());

    let x = Term::free("x", car.clone());
    let y = Term::free("y", car.clone());
    let s_x = Term::app(s.clone(), x.clone());
    let s_y = Term::app(s.clone(), y.clone());
    let pred_xy = Term::app(Term::app(pred.clone(), x.clone()), y.clone());
    let closed_imp = hol::hol_imp(pred_xy, hol::hol_imp(s_x, s_y));
    let inner = hol::hol_forall("y", car.clone(), closed_imp);
    let closed_part = hol::hol_forall("x", car.clone(), inner);

    let x2 = Term::free("x", car.clone());
    let s_x2 = Term::app(s.clone(), x2);
    let nonempty_part = hol::hol_exists("x", car.clone(), s_x2);

    let body = hol::hol_and(closed_part, nonempty_part);
    hol::pub_abs("S", carrier, body)
}

/// `{ car } close pred` factory. The resulting TypeSpec has carrier
/// `car → bool` and selects subsets of `car` that are pred-closed
/// and non-empty.
pub fn close_spec(symbol: Canonical, car: Type, pred: Term) -> TypeSpecHandle {
    let carrier = Type::fun(car.clone(), Type::bool());
    let tm = close_predicate(car, pred);
    TypeSpecHandle::new(TypeSpec {
        symbol,
        ty: Some(carrier),
        tm: Some(tm),
    })
}

/// `car quot pred` factory — equivalent to `{ car } close (sym pred)`.
pub fn quot_spec(symbol: Canonical, car: Type, pred: Term) -> TypeSpecHandle {
    use crate::hol;
    let x = Term::free("x", car.clone());
    let y = Term::free("y", car.clone());
    let pred_xy = Term::app(Term::app(pred.clone(), x.clone()), y.clone());
    let pred_yx = Term::app(Term::app(pred.clone(), y.clone()), x.clone());
    let disj = hol::hol_or(pred_xy, pred_yx);
    let lam_y = hol::pub_abs("y", car.clone(), disj);
    let sym_pred = hol::pub_abs("x", car.clone(), lam_y);
    close_spec(symbol, car, sym_pred)
}

// ============================================================================
// rat / real — placeholder
//
// Eventually:
//   rat := fieldOfFractions int
//   real := { rat } close ratLe
//
// fieldOfFractions itself is a `quot_spec` over prod 'a 'a with the
// standard cross-multiplication equivalence. For now we ship rat /
// real with the `any` predicate so the catalogue is name-complete;
// proper definitions land once `intMul` / `ratLe` are term-specs
// and the term builders for the predicates are wired in.
// ============================================================================

static RAT_LAZY: LazyLock<TypeSpecHandle> = LazyLock::new(|| {
    // TODO: rat := fieldOfFractions int (quot_spec over prod int int
    // with the (p, q) ~ (p', q') iff p*q' = p'*q predicate).
    let carrier = Type::int();
    let carrier_for_pred = carrier.clone();
    TypeSpecHandle::new(TypeSpec {
        symbol: Canonical::Rat,
        ty: Some(carrier),
        tm: Some(any(&carrier_for_pred)),
    })
});

/// `rat` — currently a placeholder (carrier := int with `any`
/// predicate). Once the term-spec catalogue grows enough to express
/// `(p, q) ∼ (p', q') iff p*q' = p'*q`, this will be a real
/// `quot_spec` over `prod int int`.
pub fn rat_spec() -> TypeSpecHandle {
    RAT_LAZY.clone()
}
/// `rat` as a 0-ary `Type`.
pub fn rat_ty() -> Type {
    Type::spec(rat_spec(), vec![])
}

static REAL_LAZY: LazyLock<TypeSpecHandle> = LazyLock::new(|| {
    // TODO: real := { rat } close ratLe — full Dedekind cut.
    // Currently uses `any` over the rat carrier (which is itself
    // a placeholder).
    let rat = rat_ty();
    let carrier = Type::fun(rat, Type::bool());
    let carrier_for_pred = carrier.clone();
    TypeSpecHandle::new(TypeSpec {
        symbol: Canonical::Real,
        ty: Some(carrier),
        tm: Some(any(&carrier_for_pred)),
    })
});

/// `real` — currently a placeholder. Will become `{ rat } close ratLe`
/// once `ratLe` is a usable term-spec.
pub fn real_spec() -> TypeSpecHandle {
    REAL_LAZY.clone()
}
/// `real` as a 0-ary `Type`.
pub fn real_ty() -> Type {
    Type::spec(real_spec(), vec![])
}

// ============================================================================
// fieldOfFractions 'a — placeholder
// ============================================================================

static FIELD_OF_FRACTIONS_LAZY: LazyLock<TypeSpecHandle> = LazyLock::new(|| {
    // TODO: build the quot_spec at prod 'a 'a with the equivalence
    // (p, q) ∼ (p', q') ⟺ p*q' = p'*q.
    let alpha = Type::tfree("a");
    let carrier = prod(alpha.clone(), alpha);
    let carrier_for_pred = carrier.clone();
    TypeSpecHandle::new(TypeSpec {
        symbol: Canonical::FieldOfFractions,
        ty: Some(carrier),
        tm: Some(any(&carrier_for_pred)),
    })
});

/// `fieldOfFractions 'a` — placeholder; eventually a `quot_spec` over
/// `prod 'a 'a` with the cross-multiplication equivalence.
pub fn field_of_fractions_spec() -> TypeSpecHandle {
    FIELD_OF_FRACTIONS_LAZY.clone()
}
/// `fieldOfFractions α`.
pub fn field_of_fractions(alpha: Type) -> Type {
    Type::spec(field_of_fractions_spec(), vec![alpha])
}

// ============================================================================
// Term catalogue: nat arithmetic
// ============================================================================
//
// For now each entry has `ty = Some(...)` (the signature) and
// `tm = None` (no body yet — the reduction-by-pointer-identity
// dispatch in `Thm::reduce_prim` lands in a follow-up that wires
// each handle to a Rust computation closure). Consumers can already
// build `Term::term_spec(spec, [])` leaves and run them through
// type-checking / display / hash / sexp.

fn nat_bin_op(symbol: Canonical) -> TermSpecHandle {
    let nat = Type::nat();
    TermSpecHandle::new(TermSpec {
        symbol,
        ty: Some(Type::fun(nat.clone(), Type::fun(nat.clone(), nat))),
        tm: None,
    })
}

fn nat_cmp_op(symbol: Canonical) -> TermSpecHandle {
    let nat = Type::nat();
    TermSpecHandle::new(TermSpec {
        symbol,
        ty: Some(Type::fun(nat.clone(), Type::fun(nat, Type::bool()))),
        tm: None,
    })
}

fn int_bin_op(symbol: Canonical) -> TermSpecHandle {
    let int = Type::int();
    TermSpecHandle::new(TermSpec {
        symbol,
        ty: Some(Type::fun(int.clone(), Type::fun(int.clone(), int))),
        tm: None,
    })
}

fn int_cmp_op(symbol: Canonical) -> TermSpecHandle {
    let int = Type::int();
    TermSpecHandle::new(TermSpec {
        symbol,
        ty: Some(Type::fun(int.clone(), Type::fun(int, Type::bool()))),
        tm: None,
    })
}

static NAT_ADD_LAZY: LazyLock<TermSpecHandle> = LazyLock::new(|| nat_bin_op(Canonical::NatAdd));
static NAT_MUL_LAZY: LazyLock<TermSpecHandle> = LazyLock::new(|| nat_bin_op(Canonical::NatMul));
static NAT_SUB_LAZY: LazyLock<TermSpecHandle> = LazyLock::new(|| nat_bin_op(Canonical::NatSub));
static NAT_LE_LAZY: LazyLock<TermSpecHandle> = LazyLock::new(|| nat_cmp_op(Canonical::NatLe));
static NAT_LT_LAZY: LazyLock<TermSpecHandle> = LazyLock::new(|| nat_cmp_op(Canonical::NatLt));

static INT_ADD_LAZY: LazyLock<TermSpecHandle> = LazyLock::new(|| int_bin_op(Canonical::IntAdd));
static INT_MUL_LAZY: LazyLock<TermSpecHandle> = LazyLock::new(|| int_bin_op(Canonical::IntMul));
static INT_SUB_LAZY: LazyLock<TermSpecHandle> = LazyLock::new(|| int_bin_op(Canonical::IntSub));
static INT_LE_LAZY: LazyLock<TermSpecHandle> = LazyLock::new(|| int_cmp_op(Canonical::IntLe));
static INT_LT_LAZY: LazyLock<TermSpecHandle> = LazyLock::new(|| int_cmp_op(Canonical::IntLt));

/// `natAdd : nat → nat → nat`.
pub fn nat_add_spec() -> TermSpecHandle {
    NAT_ADD_LAZY.clone()
}
/// `natMul : nat → nat → nat`.
pub fn nat_mul_spec() -> TermSpecHandle {
    NAT_MUL_LAZY.clone()
}
/// `natSub : nat → nat → nat`.
pub fn nat_sub_spec() -> TermSpecHandle {
    NAT_SUB_LAZY.clone()
}
/// `natLe : nat → nat → bool`.
pub fn nat_le_spec() -> TermSpecHandle {
    NAT_LE_LAZY.clone()
}
/// `natLt : nat → nat → bool`.
pub fn nat_lt_spec() -> TermSpecHandle {
    NAT_LT_LAZY.clone()
}

/// `intAdd : int → int → int`.
pub fn int_add_spec() -> TermSpecHandle {
    INT_ADD_LAZY.clone()
}
/// `intMul : int → int → int`.
pub fn int_mul_spec() -> TermSpecHandle {
    INT_MUL_LAZY.clone()
}
/// `intSub : int → int → int`.
pub fn int_sub_spec() -> TermSpecHandle {
    INT_SUB_LAZY.clone()
}
/// `intLe : int → int → bool`.
pub fn int_le_spec() -> TermSpecHandle {
    INT_LE_LAZY.clone()
}
/// `intLt : int → int → bool`.
pub fn int_lt_spec() -> TermSpecHandle {
    INT_LT_LAZY.clone()
}

/// `natAdd` as a [`Term`]. No type arguments — the spec is
/// monomorphic at `nat → nat → nat`.
pub fn nat_add() -> Term {
    Term::term_spec(nat_add_spec(), vec![])
}
/// `natMul` as a [`Term`].
pub fn nat_mul() -> Term {
    Term::term_spec(nat_mul_spec(), vec![])
}
/// `natSub` as a [`Term`] (saturating).
pub fn nat_sub() -> Term {
    Term::term_spec(nat_sub_spec(), vec![])
}
/// `natLe` as a [`Term`].
pub fn nat_le() -> Term {
    Term::term_spec(nat_le_spec(), vec![])
}
/// `natLt` as a [`Term`].
pub fn nat_lt() -> Term {
    Term::term_spec(nat_lt_spec(), vec![])
}
/// `intAdd` as a [`Term`].
pub fn int_add() -> Term {
    Term::term_spec(int_add_spec(), vec![])
}
/// `intMul` as a [`Term`].
pub fn int_mul() -> Term {
    Term::term_spec(int_mul_spec(), vec![])
}
/// `intSub` as a [`Term`].
pub fn int_sub() -> Term {
    Term::term_spec(int_sub_spec(), vec![])
}
/// `intLe` as a [`Term`].
pub fn int_le() -> Term {
    Term::term_spec(int_le_spec(), vec![])
}
/// `intLt` as a [`Term`].
pub fn int_lt() -> Term {
    Term::term_spec(int_lt_spec(), vec![])
}

// ============================================================================
// Term catalogue: option constructors
// ============================================================================

static NONE_LAZY: LazyLock<TermSpecHandle> = LazyLock::new(|| {
    let alpha = Type::tfree("a");
    TermSpecHandle::new(TermSpec {
        symbol: Canonical::None,
        ty: Some(option(alpha)),
        tm: None,
    })
});

static SOME_LAZY: LazyLock<TermSpecHandle> = LazyLock::new(|| {
    let alpha = Type::tfree("a");
    TermSpecHandle::new(TermSpec {
        symbol: Canonical::Some,
        ty: Some(Type::fun(alpha.clone(), option(alpha))),
        tm: None,
    })
});

/// `none : option 'a`.
pub fn none_spec() -> TermSpecHandle {
    NONE_LAZY.clone()
}
/// `none α` as a [`Term`] at concrete carrier α.
pub fn none(alpha: Type) -> Term {
    Term::term_spec(none_spec(), vec![alpha])
}

/// `some : 'a → option 'a`.
pub fn some_spec() -> TermSpecHandle {
    SOME_LAZY.clone()
}
/// `some α` as a [`Term`] at concrete carrier α.
pub fn some(alpha: Type) -> Term {
    Term::term_spec(some_spec(), vec![alpha])
}

// ============================================================================
// Term catalogue: list constructors and destructors
// ============================================================================

static NIL_LAZY: LazyLock<TermSpecHandle> = LazyLock::new(|| {
    let alpha = Type::tfree("a");
    TermSpecHandle::new(TermSpec {
        symbol: Canonical::Nil,
        ty: Some(list(alpha)),
        tm: None,
    })
});

static CONS_LAZY: LazyLock<TermSpecHandle> = LazyLock::new(|| {
    let alpha = Type::tfree("a");
    let list_a = list(alpha.clone());
    TermSpecHandle::new(TermSpec {
        symbol: Canonical::Cons,
        ty: Some(Type::fun(alpha, Type::fun(list_a.clone(), list_a))),
        tm: None,
    })
});

static HEAD_LAZY: LazyLock<TermSpecHandle> = LazyLock::new(|| {
    let alpha = Type::tfree("a");
    let list_a = list(alpha.clone());
    TermSpecHandle::new(TermSpec {
        symbol: Canonical::Head,
        ty: Some(Type::fun(list_a, option(alpha))),
        tm: None,
    })
});

static TAIL_LAZY: LazyLock<TermSpecHandle> = LazyLock::new(|| {
    let alpha = Type::tfree("a");
    let list_a = list(alpha);
    TermSpecHandle::new(TermSpec {
        symbol: Canonical::Tail,
        ty: Some(Type::fun(list_a.clone(), list_a)),
        tm: None,
    })
});

/// `nil : list 'a`.
pub fn nil_spec() -> TermSpecHandle {
    NIL_LAZY.clone()
}
/// `nil α` — empty list at carrier α.
pub fn nil(alpha: Type) -> Term {
    Term::term_spec(nil_spec(), vec![alpha])
}

/// `cons : 'a → list 'a → list 'a`.
pub fn cons_spec() -> TermSpecHandle {
    CONS_LAZY.clone()
}
/// `cons α` — list cons at carrier α (partially applicable).
pub fn cons(alpha: Type) -> Term {
    Term::term_spec(cons_spec(), vec![alpha])
}

/// `head : list 'a → option 'a` — total (returns `none` on empty).
pub fn head_spec() -> TermSpecHandle {
    HEAD_LAZY.clone()
}
/// `head α`.
pub fn head(alpha: Type) -> Term {
    Term::term_spec(head_spec(), vec![alpha])
}

/// `tail : list 'a → list 'a` — total (returns `nil` on empty).
pub fn tail_spec() -> TermSpecHandle {
    TAIL_LAZY.clone()
}
/// `tail α`.
pub fn tail(alpha: Type) -> Term {
    Term::term_spec(tail_spec(), vec![alpha])
}
