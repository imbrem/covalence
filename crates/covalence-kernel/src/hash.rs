//! Content hashing for [`Arena`] and [`Prop`] (Phase H).
//!
//! BLAKE3 streaming hash over the arena's linear buffers — types,
//! terms, term-props, imports (recursively by source-arena hash),
//! interned strings/bytes/ints/nats, tyargs, and substitution tables.
//!
//! **Invariant.** The hash uniquely identifies the bytes that went
//! in: `hash → arena` is injective. The reverse direction is **not**
//! required — two arenas built with different allocation orders that
//! express the same logical content can hash differently. The
//! kernel doesn't canonicalise.

use covalence_hash::{O256, blake3};

use crate::arena::Arena;
use crate::prop::Prop;
use crate::term::{Packed64, TermDef, TermRef};
use crate::ty::{TypeDef, TypeRef};

/// Domain-separation tags. Each byte introduces a distinct prefix so
/// distinct field families can't collide.
const TAG_ARENA: u8 = 0x01;
const TAG_PROP: u8 = 0x02;
const TAG_CONTEXT: u8 = 0x03;

const TAG_TYPE: u8 = 0x10;
const TAG_TERM: u8 = 0x11;
const TAG_TERMPROPS: u8 = 0x12;
const TAG_IMPORT: u8 = 0x13;
const TAG_STRING: u8 = 0x14;
const TAG_BYTES: u8 = 0x15;
const TAG_INT: u8 = 0x16;
const TAG_NAT: u8 = 0x17;
const TAG_TYARGS: u8 = 0x18;
const TAG_TERMSUBST: u8 = 0x19;
const TAG_TYPESUBST: u8 = 0x1A;

/// Streaming hasher wrapping `blake3::Hasher` with length-prefixed
/// helpers for variable-size fields.
pub(crate) struct Hasher {
    inner: blake3::Hasher,
}

impl Hasher {
    fn new() -> Self {
        Self {
            inner: blake3::Hasher::new(),
        }
    }

    fn u8(&mut self, v: u8) {
        self.inner.update(&[v]);
    }
    fn u32(&mut self, v: u32) {
        self.inner.update(&v.to_le_bytes());
    }
    fn i32(&mut self, v: i32) {
        self.inner.update(&v.to_le_bytes());
    }
    fn u64(&mut self, v: u64) {
        self.inner.update(&v.to_le_bytes());
    }
    fn bytes(&mut self, b: &[u8]) {
        self.u64(b.len() as u64);
        self.inner.update(b);
    }
    fn o256(&mut self, h: O256) {
        self.inner.update(h.as_bytes());
    }
    fn finalize(self) -> O256 {
        O256::from_bytes(*self.inner.finalize().as_bytes())
    }
}

/// Compute the content hash of an arena. See module docs.
pub fn arena(arena: &Arena) -> O256 {
    let mut h = Hasher::new();
    h.u8(TAG_ARENA);
    feed_arena(&mut h, arena);
    h.finalize()
}

/// Compute the content hash of a `Prop` against its arena.
///
/// `arena_hash` lets callers reuse a pre-computed [`arena`] result;
/// pass `arena_hash` matching the arena that interprets `prop.concl`.
pub fn prop(prop: &Prop, arena_hash: O256) -> O256 {
    let mut h = Hasher::new();
    h.u8(TAG_PROP);
    h.o256(arena_hash);
    h.u32(prop.concl.0);
    // Context: hash each assumption's concl in order (using the same
    // arena_hash — assumptions live in the same arena as the Prop).
    h.u8(TAG_CONTEXT);
    h.u64(prop.context.len() as u64);
    for i in 0..prop.context.len() {
        let assum = prop.context.assumption(i).expect("len/index invariant");
        h.u32(assum.concl.0);
    }
    // Precondition chain (Phase P2) — hash each precondition prop's
    // concl in chain order. The chain elements are Arc<Prop> so we
    // recurse via their concls.
    h.u64(prop.precondition_chain().len() as u64);
    for p in prop.precondition_chain() {
        h.u32(p.concl.0);
    }
    h.finalize()
}

// -----------------------------------------------------------------------
// Arena field feeders
// -----------------------------------------------------------------------

fn feed_arena(h: &mut Hasher, a: &Arena) {
    // Types.
    h.u8(TAG_TYPE);
    let types = a.all_types();
    h.u64(types.len() as u64);
    for t in types {
        feed_type_def(h, t);
    }

    // Terms.
    h.u8(TAG_TERM);
    let terms = a.all_terms();
    h.u64(terms.len() as u64);
    for t in terms {
        feed_term_def(h, t);
    }

    // Term props (parallel to terms).
    h.u8(TAG_TERMPROPS);
    let props = a.all_term_props();
    h.u64(props.len() as u64);
    for p in props {
        h.i32(p.type_info.encoded_for_hash());
        h.u8(p.has_free as u8);
    }

    // Imports — recurse via source arena hash.
    h.u8(TAG_IMPORT);
    let imports = a.imports();
    h.u64(imports.len() as u64);
    for imp in imports {
        let src_hash = arena(&imp.arena);
        h.o256(src_hash);
        h.u32(imp.term_subst.0);
        h.u32(imp.type_subst.0);
    }

    // Strings.
    h.u8(TAG_STRING);
    let strings = a.all_strings();
    h.u64(strings.len() as u64);
    for s in strings {
        h.bytes(s.as_bytes());
    }

    // Bytes.
    h.u8(TAG_BYTES);
    let bytes_table = a.all_bytes();
    h.u64(bytes_table.len() as u64);
    for b in bytes_table {
        h.bytes(b.as_ref());
    }

    // Ints (arbitrary-precision). Sign byte + magnitude bytes.
    h.u8(TAG_INT);
    let ints = a.all_ints();
    h.u64(ints.len() as u64);
    for i in ints {
        let (sign, mag) = i.to_bytes_le();
        h.u8(sign as u8);
        h.bytes(&mag);
    }

    // Nats (arbitrary-precision).
    h.u8(TAG_NAT);
    let nats = a.all_nats();
    h.u64(nats.len() as u64);
    for n in nats {
        h.bytes(&n.to_bytes_le());
    }

    // Tyargs.
    h.u8(TAG_TYARGS);
    let tyargs = a.all_tyargs();
    h.u64(tyargs.len() as u64);
    for args in tyargs {
        h.u64(args.len() as u64);
        for r in args {
            feed_type_ref(h, *r);
        }
    }

    // Term substs.
    h.u8(TAG_TERMSUBST);
    let term_substs = a.all_term_substs();
    h.u64(term_substs.len() as u64);
    for s in term_substs {
        h.u64(s.entries.len() as u64);
        for (name, image) in &s.entries {
            h.u32(name.0);
            feed_term_ref(h, *image);
        }
    }

    // Type substs.
    h.u8(TAG_TYPESUBST);
    let type_substs = a.all_type_substs();
    h.u64(type_substs.len() as u64);
    for s in type_substs {
        h.u64(s.entries.len() as u64);
        for (name, image) in &s.entries {
            h.u32(name.0);
            feed_type_ref(h, *image);
        }
    }
}

fn feed_type_ref(h: &mut Hasher, r: TypeRef) {
    h.i32(r.raw());
}

fn feed_term_ref(h: &mut Hasher, r: TermRef) {
    h.u32(r.raw());
}

fn feed_packed64(h: &mut Hasher, p: Packed64) {
    h.u64(p.to_u64());
}

fn feed_type_def(h: &mut Hasher, d: &TypeDef) {
    match d {
        TypeDef::Bool => h.u8(0),
        TypeDef::Bytes => h.u8(1),
        TypeDef::Int => h.u8(2),
        TypeDef::Nat => h.u8(3),
        TypeDef::Fun(a, b) => {
            h.u8(4);
            feed_type_ref(h, *a);
            feed_type_ref(h, *b);
        }
        TypeDef::TVar(s) => {
            h.u8(5);
            h.u32(s.0);
        }
        TypeDef::Tyapp(s, args) => {
            h.u8(6);
            h.u32(s.0);
            h.u32(args.0);
        }
        TypeDef::Subset(parent, p) => {
            h.u8(7);
            feed_type_ref(h, *parent);
            h.u32(p.0);
        }
        TypeDef::Foreign(imp, src) => {
            h.u8(8);
            h.u32(imp.0);
            h.u32(src.0);
        }
    }
}

fn feed_term_def(h: &mut Hasher, d: &TermDef) {
    match d {
        TermDef::Bound(i) => {
            h.u8(0);
            h.u32(*i);
        }
        TermDef::Free(name, ty) => {
            h.u8(1);
            h.u32(name.0);
            feed_type_ref(h, *ty);
        }
        TermDef::Const(name, ty) => {
            h.u8(2);
            h.u32(name.0);
            feed_type_ref(h, *ty);
        }
        TermDef::Comb(f, x) => {
            h.u8(3);
            feed_term_ref(h, *f);
            feed_term_ref(h, *x);
        }
        TermDef::Lam(ty, body) => {
            h.u8(4);
            feed_type_ref(h, *ty);
            feed_term_ref(h, *body);
        }
        TermDef::Bool(b) => {
            h.u8(5);
            h.u8(*b as u8);
        }
        TermDef::Eq(a, b) => {
            h.u8(6);
            feed_term_ref(h, *a);
            feed_term_ref(h, *b);
        }
        TermDef::Forall(p) => {
            h.u8(7);
            feed_term_ref(h, *p);
        }
        TermDef::Exists(p) => {
            h.u8(8);
            feed_term_ref(h, *p);
        }
        TermDef::Eps(ty, p) => {
            h.u8(9);
            feed_type_ref(h, *ty);
            feed_term_ref(h, *p);
        }
        TermDef::Abs(ty) => {
            h.u8(10);
            feed_type_ref(h, *ty);
        }
        TermDef::Rep(ty) => {
            h.u8(11);
            feed_type_ref(h, *ty);
        }
        TermDef::Op1(op, x) => {
            h.u8(12);
            h.u8(*op as u8);
            feed_term_ref(h, *x);
        }
        TermDef::Op2(op, a, b) => {
            h.u8(13);
            h.u8(*op as u8);
            feed_term_ref(h, *a);
            feed_term_ref(h, *b);
        }
        TermDef::IntInline(p) => {
            h.u8(14);
            feed_packed64(h, *p);
        }
        TermDef::IntStored(id) => {
            h.u8(15);
            h.u32(id.0);
        }
        TermDef::NatInline(p) => {
            h.u8(16);
            feed_packed64(h, *p);
        }
        TermDef::NatStored(id) => {
            h.u8(17);
            h.u32(id.0);
        }
        TermDef::BytesStored(id) => {
            h.u8(18);
            h.u32(id.0);
        }
        TermDef::Foreign(imp, src) => {
            h.u8(19);
            h.u32(imp.0);
            h.u32(src.0);
        }
    }
}
