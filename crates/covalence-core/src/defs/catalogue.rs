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
        let conj = hol_and(eq_x_a, eq_y_b);
        let lam_y = hol::pub_abs("y", beta.clone(), conj);
        let lam_xy = hol::pub_abs("x", alpha.clone(), lam_y);
        let r_eq = hol::hol_eq(r.clone(), lam_xy);
        let inner_exists = hol::hol_exists("b", beta.clone(), r_eq);
        hol::hol_exists("a", alpha.clone(), inner_exists)
    };

    hol::pub_abs("R", rel_ty, body)
}

/// HOL `∧`: a small adapter so we can build inside this module
/// without re-exporting hol_and. Replicated locally rather than
/// extending `hol.rs`'s public surface further than necessary.
fn hol_and(p: Term, q: Term) -> Term {
    let b = Type::bool();
    let op = Term::hol_op(
        crate::term::HolOp::And,
        Type::fun(b.clone(), Type::fun(b.clone(), b)),
    );
    Term::app(Term::app(op, p), q)
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

static BIT_LAZY: LazyLock<TypeSpecHandle> =
    LazyLock::new(|| fixed_width_spec(Canonical::Bit, Type::unit()));

/// `u1 (bit) := coprod unit unit`.
pub fn bit_spec() -> TypeSpecHandle {
    BIT_LAZY.clone()
}
/// `bit` as a 0-ary `Type`.
pub fn bit() -> Type {
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

width!(U2_LAZY, u2_spec, u2, Canonical::U2, bit);
width!(U4_LAZY, u4_spec, u4, Canonical::U4, u2);
width!(U8_LAZY, u8_spec, u8, Canonical::U8, u4);
width!(U16_LAZY, u16_spec, u16, Canonical::U16, u8);
width!(U32_LAZY, u32_spec, u32, Canonical::U32, u16);
width!(U64_LAZY, u64_spec, u64, Canonical::U64, u32);
width!(U128_LAZY, u128_spec, u128, Canonical::U128, u64);
width!(U256_LAZY, u256_spec, u256, Canonical::U256, u128);
width!(U512_LAZY, u512_spec, u512, Canonical::U512, u256);

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
