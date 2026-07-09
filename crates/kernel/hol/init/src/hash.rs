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
//! ## Fresh-identity leaves
//!
//! The kernel compares `FreshConst` / `FreshTyCon` leaves by `Arc`
//! pointer identity, and a pointer is *not* deterministic across
//! processes — so those leaves hash by their structural payload only
//! (the constant's type / the constructor's args), deliberately
//! ignoring the identity token. Two distinct fresh constants of the
//! same type therefore collide; that satisfies the `Hash`-vs-`Eq`
//! contract (equal values hash equally), which is all callers rely on.
//!
//! Two flavours of the term hasher are provided:
//!
//! - **Stateless walk** ([`hash_term`], [`hash_type`]) — recompute
//!   every call. O(size) per query.
//! - **Cached walk via [`Hasher`]** — caches each subtree by `Arc`
//!   pointer identity.

use std::collections::HashMap;

use covalence_core::{Term, TermKind, Type, TypeKind};
use covalence_hash::{Blake3Ctx, HashCtx, O256};

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
const TY_NAT: u8 = 0x06;
// 0x08 = TY_UNIT (removed; `unit` is now the bool-subtype TypeSpec,
// hashed via TY_SPEC). Do not reuse.
const TY_SPEC: u8 = 0x09;
const TY_BOOL: u8 = 0x0a;
const TY_FRESH_TYCON: u8 = 0x0b;

// ---- term tags ----
//
// 0x05 = T_IMP (removed Core ⟹), 0x06 = T_ALL (removed Core ⋀),
// 0x07 = T_EQ (removed Core ≡). Do not reuse.
const T_BOUND: u8 = 0x00;
const T_FREE: u8 = 0x01;
const T_CONST: u8 = 0x02;
const T_APP: u8 = 0x03;
const T_ABS: u8 = 0x04;
const T_BLOB: u8 = 0x08;
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
const T_SUCC: u8 = 0x15;
const T_FRESH_CONST: u8 = 0x16;
const T_ZERO: u8 = 0x17;

// ============================================================================
// Stateless API
// ============================================================================

/// Compute the content hash of `t`. Recomputes from scratch on every
/// call. For repeated hashing of overlapping subterms, prefer
/// [`Hasher`] which caches by `Arc` identity.
pub fn hash_term(t: &Term) -> O256 {
    Hasher::new().hash_term(t)
}

/// Compute the content hash of `ty`.
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

    pub fn hash_term(&mut self, t: &Term) -> O256 {
        let key = t.ptr_id();
        if let Some(h) = self.term_cache.get(&key) {
            return *h;
        }
        let h = self.compute_term(t);
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
            TypeKind::Nat => ctx.tag([TY_NAT]),
            TypeKind::Bool => ctx.tag([TY_BOOL]),
            TypeKind::Fun(a, b) => {
                let ah = self.hash_type(a);
                let bh = self.hash_type(b);
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
                    let h = self.hash_type(arg);
                    buf.extend_from_slice(h.as_bytes());
                }
                ctx.tag(buf)
            }
            // A fresh tycon's identity is a process-local pointer, so it
            // is deliberately excluded: hash tag + arg hashes only. Two
            // distinct fresh tycons with equal args collide — fine for
            // the `Hash`-vs-`Eq` contract (equal values hash equally).
            TypeKind::FreshTyCon(leaf) => {
                let args = leaf.args();
                let mut buf = Vec::with_capacity(1 + 4 + 32 * args.len());
                buf.push(TY_FRESH_TYCON);
                buf.extend_from_slice(&(args.len() as u32).to_le_bytes());
                for arg in args {
                    let h = self.hash_type(arg);
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
                    let h = self.hash_type(arg);
                    buf.extend_from_slice(h.as_bytes());
                }
                ctx.tag(buf)
            }
        }
    }

    fn compute_term(&mut self, t: &Term) -> O256 {
        let ctx = term_ctx();
        match t.kind() {
            TermKind::Bound(i) => {
                let mut buf = [0u8; 1 + 4];
                buf[0] = T_BOUND;
                buf[1..5].copy_from_slice(&i.to_le_bytes());
                ctx.tag(buf)
            }
            TermKind::Free(v) => {
                let th = self.hash_type(v.ty());
                named_with_ty(ctx, T_FREE, v.name().as_bytes(), th)
            }
            TermKind::Const(name, ty) => {
                let th = self.hash_type(ty);
                named_with_ty(ctx, T_CONST, name.as_bytes(), th)
            }
            TermKind::App(f, x) => {
                let fh = self.hash_term(f);
                let xh = self.hash_term(x);
                binary(ctx, T_APP, fh, xh)
            }
            TermKind::Abs(ty, body) => {
                let th = self.hash_type(ty);
                let bh = self.hash_term(body);
                binary(ctx, T_ABS, th, bh)
            }
            TermKind::Blob(bytes) => {
                let mut buf = Vec::with_capacity(1 + 4 + bytes.len());
                buf.push(T_BLOB);
                buf.extend_from_slice(&(bytes.len() as u32).to_le_bytes());
                buf.extend_from_slice(bytes);
                ctx.tag(buf)
            }
            // A fresh constant's identity is a process-local pointer, so
            // it is deliberately excluded: hash tag + type hash only (see
            // the module doc — equal values still hash equally).
            TermKind::FreshConst(leaf) => {
                let th = self.hash_type(leaf.ty());
                let mut buf = Vec::with_capacity(1 + 32);
                buf.push(T_FRESH_CONST);
                buf.extend_from_slice(th.as_bytes());
                ctx.tag(buf)
            }
            // Hash a `Def` by its display name + its body's hash. This
            // is *content-based* (cross-process stable) and may
            // collide for two distinct `Def`s with identical name and
            // body — that's fine for the `Hash`-vs-`Eq` contract,
            // which only requires equal values to hash equally.
            TermKind::Def(d) => {
                let name_bytes = d.name().as_bytes();
                let body_h = self.hash_term(&d.body());
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
                let label = lit.tag().label().as_bytes();
                let mut buf = Vec::with_capacity(1 + 1 + label.len() + 8);
                buf.push(T_SMALL_INT);
                buf.push(label.len() as u8);
                buf.extend_from_slice(label);
                buf.extend_from_slice(&lit.bits().to_le_bytes());
                ctx.tag(buf)
            }
            TermKind::Bool(b) => ctx.tag([T_BOOL, u8::from(*b)]),
            // The primitive zero / successor constants — bare tags.
            TermKind::Zero => ctx.tag([T_ZERO]),
            TermKind::Succ => ctx.tag([T_SUCC]),
            // `=` and `ε` carry their element type α.
            TermKind::Eq(alpha) => {
                let ty_h = self.hash_type(alpha);
                let mut buf = Vec::with_capacity(1 + 32);
                buf.push(T_EQ);
                buf.extend_from_slice(ty_h.as_bytes());
                ctx.tag(buf)
            }
            TermKind::Select(alpha) => {
                let ty_h = self.hash_type(alpha);
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
                    let h = self.hash_type(arg);
                    buf.extend_from_slice(h.as_bytes());
                }
                ctx.tag(buf)
            }
            // `abs`/`rep` coercions: tag + spec label + type args,
            // exactly like `T_SPEC` but with their own tag byte so the
            // abstraction and its representation never collide with the
            // bare spec leaf.
            TermKind::SpecAbs(spec, args) => {
                self.hash_coercion(T_SPEC_ABS, spec.symbol().label(), args, ctx)
            }
            TermKind::SpecRep(spec, args) => {
                self.hash_coercion(T_SPEC_REP, spec.symbol().label(), args, ctx)
            }
        }
    }

    /// Hash an `abs`/`rep` spec coercion leaf: `tag · |label| · label ·
    /// |args| · arg-hashes…`. Shared by the [`TermKind::SpecAbs`] and
    /// [`TermKind::SpecRep`] arms.
    fn hash_coercion(&mut self, tag: u8, label: &str, args: &[Type], ctx: &Blake3Ctx) -> O256 {
        let label = label.as_bytes();
        let mut buf = Vec::with_capacity(1 + 1 + label.len() + 4 + 32 * args.len());
        buf.push(tag);
        buf.push(label.len() as u8);
        buf.extend_from_slice(label);
        buf.extend_from_slice(&(args.len() as u32).to_le_bytes());
        for arg in args {
            let h = self.hash_type(arg);
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

#[cfg(test)]
mod zero_leaf_tests {
    use super::*;
    use covalence_core::Term;

    /// EG3a: the primitive `zero` leaf hashes stably and DISTINCT from
    /// both the `Nat(0)` literal and `succ` (injective tag catalogue).
    #[test]
    fn zero_hash_distinct() {
        let z = hash_term(&Term::zero());
        assert_eq!(z, hash_term(&Term::zero()));
        // The literal built via the lit facade (the sanctioned chokepoint).
        let lit = covalence_hol_eval::lit::mk_nat(covalence_types::Nat::zero());
        assert_ne!(z, hash_term(&lit));
        assert_ne!(z, hash_term(&Term::succ()));
    }
}
