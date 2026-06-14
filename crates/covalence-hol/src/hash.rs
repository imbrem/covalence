//! Content hashing for kernel terms and types.
//!
//! Outside the TCB. Hashes are computed on demand by walking the
//! graph. No inference rule in `covalence-core` consumes a hash, so
//! a bug here cannot produce a false `Thm` — at worst it confuses a
//! downstream cache.
//!
//! ## Tag values are NOT stable yet
//!
//! The `T_*` / `TY_*` tag bytes below are an internal, in-flux
//! encoding. While the kernel surface is still moving we reassign and
//! reuse them freely — there is no persisted-hash backwards-compat to
//! preserve, so do not add "reserved, do not reuse" bookkeeping. This
//! changes once we commit to a stable content-address format; that
//! transition will be called out explicitly when it happens.
//!
//! ## Observer payloads
//!
//! Because the kernel compares `Obs` leaves by `Arc` pointer
//! identity, hashing them by pointer would *not* be deterministic
//! across processes or sessions. So hashing an `Obs` leaf requires
//! caller-supplied payload bytes — provided via [`ObsHasher`]. The
//! default [`UnitObsHasher`] handles the trivial `()` observer by
//! contributing zero bytes; user crates with custom observer types
//! plug in their own.
//!
//! Two flavours of the term hasher are provided:
//!
//! - **Stateless walk** ([`hash_term`], [`hash_type`]) — recompute
//!   every call. O(size) per query.
//! - **Cached walk via [`Hasher`]** — caches each subtree by `Arc`
//!   pointer identity.

use std::collections::HashMap;

use covalence_hash::{Blake3Ctx, HashCtx, O256};
use covalence_core::{Object, Term, TermKind, Type, TypeKind};

// ============================================================================
// Observer payload trait
// ============================================================================

/// Provides deterministic content bytes for an [`Object`] leaf.
/// Implementations typically `downcast` to known concrete observer
/// types and emit a stable byte representation.
pub trait ObsHasher {
    fn obs_payload(&self, observer: &Object) -> Vec<u8>;
}

/// Trivial handler: contributes zero bytes for the `()` observer,
/// panics for any other type. Real callers compose `UnitObsHasher`
/// with their own handlers.
pub struct UnitObsHasher;

impl ObsHasher for UnitObsHasher {
    fn obs_payload(&self, observer: &Object) -> Vec<u8> {
        if observer.downcast::<()>().is_some() {
            Vec::new()
        } else {
            panic!(
                "UnitObsHasher: cannot hash observer of type {:?}",
                observer.type_id()
            )
        }
    }
}

// ============================================================================
// Domain-separated BLAKE3 contexts
// ============================================================================

fn term_ctx() -> &'static Blake3Ctx {
    static CTX: std::sync::OnceLock<Blake3Ctx> = std::sync::OnceLock::new();
    CTX.get_or_init(|| Blake3Ctx::new("covalence pure term v0"))
}

fn type_ctx() -> &'static Blake3Ctx {
    static CTX: std::sync::OnceLock<Blake3Ctx> = std::sync::OnceLock::new();
    CTX.get_or_init(|| Blake3Ctx::new("covalence pure type v0"))
}

// ---- type tags (unstable; see module doc) ----
const TY_TFREE: u8 = 0x00;
const TY_FUN: u8 = 0x03;
const TY_TYCON: u8 = 0x04;
const TY_TYCON_OBS: u8 = 0x05;
const TY_NAT: u8 = 0x06;
// 0x08 = TY_UNIT (removed; `unit` is now the bool-subtype TypeSpec,
// hashed via TY_SPEC). Do not reuse.
const TY_SPEC: u8 = 0x09;
const TY_BOOL: u8 = 0x0a;

// ---- term tags ----
//
// 0x05 = T_IMP (removed Pure ⟹), 0x06 = T_ALL (removed Pure ⋀),
// 0x07 = T_EQ (removed Pure ≡). Do not reuse.
const T_BOUND: u8 = 0x00;
const T_FREE: u8 = 0x01;
const T_CONST: u8 = 0x02;
const T_APP: u8 = 0x03;
const T_ABS: u8 = 0x04;
const T_BLOB: u8 = 0x08;
const T_OBS: u8 = 0x09;
const T_DEF: u8 = 0x0a;
const T_NAT_LIT: u8 = 0x0b;
const T_INT_LIT: u8 = 0x0c;
const T_BOOL: u8 = 0x0e;
const T_EQ: u8 = 0x0f;
const T_SPEC: u8 = 0x10;
const T_SELECT: u8 = 0x11;
const T_SPEC_ABS: u8 = 0x12;
const T_SPEC_REP: u8 = 0x13;
const T_SMALL_INT: u8 = 0x14;

// ============================================================================
// Stateless API
// ============================================================================

/// Compute the content hash of `t`. Recomputes from scratch on every
/// call. For repeated hashing of overlapping subterms, prefer
/// [`Hasher`] which caches by `Arc` identity.
pub fn hash_term(t: &Term, oh: &dyn ObsHasher) -> O256 {
    Hasher::new().hash_term(t, oh)
}

/// Compute the content hash of `ty`. The observer hasher is consulted
/// when the type contains a `TyConObs` constructor; pass any handler
/// (commonly [`UnitObsHasher`]) when working with types known to be
/// free of observer constructors.
pub fn hash_type(ty: &Type, oh: &dyn ObsHasher) -> O256 {
    Hasher::new().hash_type(ty, oh)
}

// ============================================================================
// Cached walk
// ============================================================================

/// A cached walker. Hashes are memoised by `Term`/`Type` pointer
/// identity (`ptr_id()`), so when several callers ask the same
/// `Hasher` for the same shared subtree only one BLAKE3 pass runs.
pub struct Hasher {
    term_cache: HashMap<usize, O256>,
    type_cache: HashMap<usize, O256>,
}

impl Hasher {
    pub fn new() -> Self {
        Self {
            term_cache: HashMap::new(),
            type_cache: HashMap::new(),
        }
    }

    pub fn hash_term(&mut self, t: &Term, oh: &dyn ObsHasher) -> O256 {
        let key = t.ptr_id();
        if let Some(h) = self.term_cache.get(&key) {
            return *h;
        }
        let h = self.compute_term(t, oh);
        self.term_cache.insert(key, h);
        h
    }

    pub fn hash_type(&mut self, ty: &Type, oh: &dyn ObsHasher) -> O256 {
        let key = ty.ptr_id();
        if let Some(h) = self.type_cache.get(&key) {
            return *h;
        }
        let h = self.compute_type(ty, oh);
        self.type_cache.insert(key, h);
        h
    }

    fn compute_type(&mut self, ty: &Type, oh: &dyn ObsHasher) -> O256 {
        let ctx = type_ctx();
        match ty.kind() {
            TypeKind::TFree(name) => {
                let bytes = name.as_bytes();
                let mut buf = Vec::with_capacity(1 + 4 + bytes.len());
                buf.push(TY_TFREE);
                buf.extend_from_slice(&(bytes.len() as u32).to_le_bytes());
                buf.extend_from_slice(bytes);
                ctx.tag(buf)
            }
            TypeKind::Nat => ctx.tag([TY_NAT]),
            TypeKind::Bool => ctx.tag([TY_BOOL]),
            TypeKind::Fun(a, b) => {
                let ah = self.hash_type(a, oh);
                let bh = self.hash_type(b, oh);
                binary(ctx, TY_FUN, ah, bh)
            }
            TypeKind::Tycon(name, args) => {
                let name_bytes = name.as_bytes();
                let mut buf = Vec::with_capacity(1 + 4 + name_bytes.len() + 4 + 32 * args.len());
                buf.push(TY_TYCON);
                buf.extend_from_slice(&(name_bytes.len() as u32).to_le_bytes());
                buf.extend_from_slice(name_bytes);
                buf.extend_from_slice(&(args.len() as u32).to_le_bytes());
                for arg in args {
                    let h = self.hash_type(arg, oh);
                    buf.extend_from_slice(h.as_bytes());
                }
                ctx.tag(buf)
            }
            // Hash by the observer's caller-supplied payload + arg
            // hashes. `BinderHint` is α-transparent in the kernel (excluded
            // from `Hash`/`Eq`) so we exclude it here too — two
            // α-equivalent `TyConObs` types must hash equally.
            TypeKind::TyConObs(observer, _hint, args) => {
                let payload = oh.obs_payload(observer);
                let mut buf = Vec::with_capacity(1 + 4 + payload.len() + 4 + 32 * args.len());
                buf.push(TY_TYCON_OBS);
                buf.extend_from_slice(&(payload.len() as u32).to_le_bytes());
                buf.extend_from_slice(&payload);
                buf.extend_from_slice(&(args.len() as u32).to_le_bytes());
                for arg in args {
                    let h = self.hash_type(arg, oh);
                    buf.extend_from_slice(h.as_bytes());
                }
                ctx.tag(buf)
            }
            TypeKind::Spec(spec, args) => {
                // Hash by the spec's canonical-symbol label + arg
                // hashes. The spec's `ty`/`tm` factories aren't
                // hashed inline — two equally-labelled canonical
                // specs are kernel-shipped singletons (LazyLock),
                // so structural identity is the right model.
                let label = spec.symbol().label().as_bytes();
                let mut buf = Vec::with_capacity(1 + 4 + label.len() + 4 + 32 * args.len());
                buf.push(TY_SPEC);
                buf.extend_from_slice(&(label.len() as u32).to_le_bytes());
                buf.extend_from_slice(label);
                buf.extend_from_slice(&(args.len() as u32).to_le_bytes());
                for arg in args {
                    let h = self.hash_type(arg, oh);
                    buf.extend_from_slice(h.as_bytes());
                }
                ctx.tag(buf)
            }
        }
    }

    fn compute_term(&mut self, t: &Term, oh: &dyn ObsHasher) -> O256 {
        let ctx = term_ctx();
        match t.kind() {
            TermKind::Bound(i) => {
                let mut buf = [0u8; 1 + 4];
                buf[0] = T_BOUND;
                buf[1..5].copy_from_slice(&i.to_le_bytes());
                ctx.tag(buf)
            }
            TermKind::Free(name, ty) => {
                let th = self.hash_type(ty, oh);
                named_with_ty(ctx, T_FREE, name.as_bytes(), th)
            }
            TermKind::Const(name, ty) => {
                let th = self.hash_type(ty, oh);
                named_with_ty(ctx, T_CONST, name.as_bytes(), th)
            }
            TermKind::App(f, x) => {
                let fh = self.hash_term(f, oh);
                let xh = self.hash_term(x, oh);
                binary(ctx, T_APP, fh, xh)
            }
            TermKind::Abs(_, ty, body) => {
                let th = self.hash_type(ty, oh);
                let bh = self.hash_term(body, oh);
                binary(ctx, T_ABS, th, bh)
            }
            TermKind::Blob(bytes) => {
                let mut buf = Vec::with_capacity(1 + 4 + bytes.len());
                buf.push(T_BLOB);
                buf.extend_from_slice(&(bytes.len() as u32).to_le_bytes());
                buf.extend_from_slice(bytes);
                ctx.tag(buf)
            }
            TermKind::Obs(observer, ty) => {
                let payload = oh.obs_payload(observer);
                let th = self.hash_type(ty, oh);
                let mut buf = Vec::with_capacity(1 + 4 + payload.len() + 32);
                buf.push(T_OBS);
                buf.extend_from_slice(&(payload.len() as u32).to_le_bytes());
                buf.extend_from_slice(&payload);
                buf.extend_from_slice(th.as_bytes());
                ctx.tag(buf)
            }
            // Hash a `Def` by its display name + its body's hash. This
            // is *content-based* (cross-process stable) and may
            // collide for two distinct `Def`s with identical name and
            // body — that's fine for the `Hash`-vs-`Eq` contract,
            // which only requires equal values to hash equally.
            TermKind::Def(d) => {
                let name_bytes = d.name().as_str().as_bytes();
                let body_h = self.hash_term(&d.body(), oh);
                let mut buf = Vec::with_capacity(1 + 4 + name_bytes.len() + 32);
                buf.push(T_DEF);
                buf.extend_from_slice(&(name_bytes.len() as u32).to_le_bytes());
                buf.extend_from_slice(name_bytes);
                buf.extend_from_slice(body_h.as_bytes());
                ctx.tag(buf)
            }
            TermKind::Nat(n) => {
                let s = n.as_inner().to_string();
                let bytes = s.as_bytes();
                let mut buf = Vec::with_capacity(1 + 4 + bytes.len());
                buf.push(T_NAT_LIT);
                buf.extend_from_slice(&(bytes.len() as u32).to_le_bytes());
                buf.extend_from_slice(bytes);
                ctx.tag(buf)
            }
            TermKind::Int(n) => {
                let s = n.as_inner().to_string();
                let bytes = s.as_bytes();
                let mut buf = Vec::with_capacity(1 + 4 + bytes.len());
                buf.push(T_INT_LIT);
                buf.extend_from_slice(&(bytes.len() as u32).to_le_bytes());
                buf.extend_from_slice(bytes);
                ctx.tag(buf)
            }
            // Hash a small-int literal by its tag label + the raw
            // `u64` bits — both stable across processes.
            TermKind::SmallInt(lit) => {
                let label = lit.tag.label().as_bytes();
                let mut buf = Vec::with_capacity(1 + 1 + label.len() + 8);
                buf.push(T_SMALL_INT);
                buf.push(label.len() as u8);
                buf.extend_from_slice(label);
                buf.extend_from_slice(&lit.bits.to_le_bytes());
                ctx.tag(buf)
            }
            TermKind::Bool(b) => ctx.tag([T_BOOL, u8::from(*b)]),
            // `=` and `ε` carry their element type α.
            TermKind::Eq(alpha) => {
                let ty_h = self.hash_type(alpha, oh);
                let mut buf = Vec::with_capacity(1 + 32);
                buf.push(T_EQ);
                buf.extend_from_slice(ty_h.as_bytes());
                ctx.tag(buf)
            }
            TermKind::Select(alpha) => {
                let ty_h = self.hash_type(alpha, oh);
                let mut buf = Vec::with_capacity(1 + 32);
                buf.push(T_SELECT);
                buf.extend_from_slice(ty_h.as_bytes());
                ctx.tag(buf)
            }
            TermKind::Spec(spec, args) => {
                let label = spec.symbol().label().as_bytes();
                let mut buf = Vec::with_capacity(1 + 1 + label.len() + 4 + 32 * args.len());
                buf.push(T_SPEC);
                buf.push(label.len() as u8);
                buf.extend_from_slice(label);
                buf.extend_from_slice(&(args.len() as u32).to_le_bytes());
                for arg in args {
                    let h = self.hash_type(arg, oh);
                    buf.extend_from_slice(h.as_bytes());
                }
                ctx.tag(buf)
            }
            // `abs`/`rep` coercions: tag + spec label + type args,
            // exactly like `T_SPEC` but with their own tag byte so the
            // abstraction and its representation never collide with the
            // bare spec leaf.
            TermKind::SpecAbs(spec, args) => {
                self.hash_coercion(T_SPEC_ABS, spec.symbol().label(), args, oh, ctx)
            }
            TermKind::SpecRep(spec, args) => {
                self.hash_coercion(T_SPEC_REP, spec.symbol().label(), args, oh, ctx)
            }
        }
    }

    /// Hash an `abs`/`rep` spec coercion leaf: `tag · |label| · label ·
    /// |args| · arg-hashes…`. Shared by the [`TermKind::SpecAbs`] and
    /// [`TermKind::SpecRep`] arms.
    fn hash_coercion(
        &mut self,
        tag: u8,
        label: &str,
        args: &[Type],
        oh: &dyn ObsHasher,
        ctx: &Blake3Ctx,
    ) -> O256 {
        let label = label.as_bytes();
        let mut buf = Vec::with_capacity(1 + 1 + label.len() + 4 + 32 * args.len());
        buf.push(tag);
        buf.push(label.len() as u8);
        buf.extend_from_slice(label);
        buf.extend_from_slice(&(args.len() as u32).to_le_bytes());
        for arg in args {
            let h = self.hash_type(arg, oh);
            buf.extend_from_slice(h.as_bytes());
        }
        ctx.tag(buf)
    }
}

impl Default for Hasher {
    fn default() -> Self {
        Self::new()
    }
}

// ============================================================================
// Helpers
// ============================================================================

fn binary(ctx: &Blake3Ctx, tag: u8, a: O256, b: O256) -> O256 {
    let mut buf = [0u8; 1 + 32 + 32];
    buf[0] = tag;
    buf[1..33].copy_from_slice(a.as_bytes());
    buf[33..65].copy_from_slice(b.as_bytes());
    ctx.tag(buf)
}

fn named_with_ty(ctx: &Blake3Ctx, tag: u8, name: &[u8], ty: O256) -> O256 {
    let mut buf = Vec::with_capacity(1 + 4 + name.len() + 32);
    buf.push(tag);
    buf.extend_from_slice(&(name.len() as u32).to_le_bytes());
    buf.extend_from_slice(name);
    buf.extend_from_slice(ty.as_bytes());
    ctx.tag(buf)
}
