//! Content hashing for Pure terms and types.
//!
//! Outside the TCB. Hashes are computed on demand by walking the
//! graph. No inference rule in `covalence-pure` consumes a hash, so
//! a bug here cannot produce a false `Thm` — at worst it confuses a
//! downstream cache.
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
use covalence_pure::{DynObs, Term, TermKind, Type, TypeKind};

// ============================================================================
// Observer payload trait
// ============================================================================

/// Provides deterministic content bytes for an [`DynObs`] leaf.
/// Implementations typically `downcast` to known concrete observer
/// types and emit a stable byte representation.
pub trait ObsHasher {
    fn obs_payload(&self, observer: &DynObs) -> Vec<u8>;
}

/// Trivial handler: contributes zero bytes for the `()` observer,
/// panics for any other type. Real callers compose `UnitObsHasher`
/// with their own handlers.
pub struct UnitObsHasher;

impl ObsHasher for UnitObsHasher {
    fn obs_payload(&self, observer: &DynObs) -> Vec<u8> {
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

// ---- type tags ----
const TY_TFREE: u8 = 0x00;
const TY_PROP: u8 = 0x01;
const TY_BYTES: u8 = 0x02;
const TY_FUN: u8 = 0x03;
const TY_TYCON: u8 = 0x04;

// ---- term tags ----
const T_BOUND: u8 = 0x00;
const T_FREE: u8 = 0x01;
const T_CONST: u8 = 0x02;
const T_APP: u8 = 0x03;
const T_ABS: u8 = 0x04;
const T_IMP: u8 = 0x05;
const T_ALL: u8 = 0x06;
const T_EQ: u8 = 0x07;
const T_BLOB: u8 = 0x08;
const T_OBS: u8 = 0x09;
const T_DEF: u8 = 0x0a;

// ============================================================================
// Stateless API
// ============================================================================

/// Compute the content hash of `t`. Recomputes from scratch on every
/// call. For repeated hashing of overlapping subterms, prefer
/// [`Hasher`] which caches by `Arc` identity.
pub fn hash_term(t: &Term, oh: &dyn ObsHasher) -> O256 {
    Hasher::new().hash_term(t, oh)
}

/// Compute the content hash of `ty`. See [`hash_term`].
pub fn hash_type(ty: &Type) -> O256 {
    Hasher::new().hash_type(ty)
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

    pub fn hash_type(&mut self, ty: &Type) -> O256 {
        let key = ty.ptr_id();
        if let Some(h) = self.type_cache.get(&key) {
            return *h;
        }
        let h = self.compute_type(ty);
        self.type_cache.insert(key, h);
        h
    }

    fn compute_type(&mut self, ty: &Type) -> O256 {
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
            TypeKind::Prop => ctx.tag([TY_PROP]),
            TypeKind::Bytes => ctx.tag([TY_BYTES]),
            TypeKind::Fun(a, b) => {
                let ah = self.hash_type(a);
                let bh = self.hash_type(b);
                binary(ctx, TY_FUN, ah, bh)
            }
            TypeKind::Tycon(name, args) => {
                let name_bytes = name.as_bytes();
                let mut buf =
                    Vec::with_capacity(1 + 4 + name_bytes.len() + 4 + 32 * args.len());
                buf.push(TY_TYCON);
                buf.extend_from_slice(&(name_bytes.len() as u32).to_le_bytes());
                buf.extend_from_slice(name_bytes);
                buf.extend_from_slice(&(args.len() as u32).to_le_bytes());
                for arg in args {
                    let h = self.hash_type(arg);
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
                let th = self.hash_type(ty);
                named_with_ty(ctx, T_FREE, name.as_bytes(), th)
            }
            TermKind::Const(name, ty) => {
                let th = self.hash_type(ty);
                named_with_ty(ctx, T_CONST, name.as_bytes(), th)
            }
            TermKind::App(f, x) => {
                let fh = self.hash_term(f, oh);
                let xh = self.hash_term(x, oh);
                binary(ctx, T_APP, fh, xh)
            }
            TermKind::Abs(_, ty, body) => {
                let th = self.hash_type(ty);
                let bh = self.hash_term(body, oh);
                binary(ctx, T_ABS, th, bh)
            }
            TermKind::Imp(a, b) => {
                let ah = self.hash_term(a, oh);
                let bh = self.hash_term(b, oh);
                binary(ctx, T_IMP, ah, bh)
            }
            TermKind::All(_, ty, body) => {
                let th = self.hash_type(ty);
                let bh = self.hash_term(body, oh);
                binary(ctx, T_ALL, th, bh)
            }
            TermKind::Eq(a, b) => {
                let ah = self.hash_term(a, oh);
                let bh = self.hash_term(b, oh);
                binary(ctx, T_EQ, ah, bh)
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
                let th = self.hash_type(ty);
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
                let body_h = self.hash_term(d.body(), oh);
                let mut buf = Vec::with_capacity(1 + 4 + name_bytes.len() + 32);
                buf.push(T_DEF);
                buf.extend_from_slice(&(name_bytes.len() as u32).to_le_bytes());
                buf.extend_from_slice(name_bytes);
                buf.extend_from_slice(body_h.as_bytes());
                ctx.tag(buf)
            }
        }
    }
}

impl Default for Hasher {
    fn default() -> Self { Self::new() }
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
