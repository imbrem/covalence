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
