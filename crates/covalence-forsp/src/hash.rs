//! Content hashing for Forsp values.
//!
//! Every cell hashes to an [`O256`] under the domain-separated context
//! `"covalence forsp cell v0"`. The encoding is a single linear buffer per
//! cell — child cells are referenced by their own hash, so the whole heap
//! forms a Merkle DAG.
//!
//! Encoding (after the leading tag byte):
//!
//! | Tag | Cell      | Payload                                       |
//! |----:|-----------|-----------------------------------------------|
//! | 00  | `Nil`     | (empty)                                       |
//! | 01  | `Cons`    | `car_hash[32] ‖ cdr_hash[32]`                 |
//! | 02  | `Atom`    | `len[u32 LE] ‖ bytes`                         |
//! | 03  | `Int`     | `value[i32 LE]`                               |
//! | 04  | `Hash`    | `raw[32]`                                     |
//! | 05  | `Blob`    | `len[u32 LE] ‖ bytes`                         |
//! | 06  | `Closure` | `body_hash[32] ‖ env_hash[32]`                |
//! | 07  | `Prim`    | `id[u8]`                                      |
//!
//! Domain separation: every payload is hashed via `FORSP_CTX.tag(buf)`, so
//! Forsp hashes cannot collide with raw BLAKE3 blob hashes used elsewhere.

use std::sync::LazyLock;

use covalence_hash::{Blake3Ctx, HashCtx, O256};

use super::{Cell, Heap, Prim, ValRef};

/// Domain context for Forsp cell hashes.
static FORSP_CTX: LazyLock<Blake3Ctx> =
    LazyLock::new(|| Blake3Ctx::new("covalence forsp cell v0"));

// --- tag bytes ---

const TAG_NIL: u8 = 0x00;
const TAG_CONS: u8 = 0x01;
const TAG_ATOM: u8 = 0x02;
const TAG_INT: u8 = 0x03;
const TAG_HASH: u8 = 0x04;
const TAG_BLOB: u8 = 0x05;
const TAG_CLOSURE: u8 = 0x06;
const TAG_PRIM: u8 = 0x07;

fn prim_id(p: Prim) -> u8 {
    match p {
        Prim::Push => 0,
        Prim::Pop => 1,
        Prim::Eq => 2,
        Prim::Cons => 3,
        Prim::Car => 4,
        Prim::Cdr => 5,
        Prim::Cswap => 6,
        Prim::Tag => 7,
        Prim::Force => 8,
        Prim::Add => 9,
        Prim::Sub => 10,
        Prim::Mul => 11,
        Prim::Nand => 12,
        Prim::Lsh => 13,
        Prim::Rsh => 14,
        Prim::Stack => 15,
        Prim::Env => 16,
    }
}

/// Compute (and cache) the content hash of `v`, recursively hashing children
/// first. Every visited cell ends up registered in `heap.by_hash`.
pub(crate) fn hash_of(heap: &mut Heap, v: ValRef) -> O256 {
    if let Some(h) = heap.hash_cache[v.0 as usize] {
        return h;
    }
    // Snapshot the cell so we can recurse without holding a borrow on the heap.
    let cell = heap.cells[v.0 as usize].clone();
    let h = match cell {
        Cell::Nil => FORSP_CTX.tag([TAG_NIL]),
        Cell::Cons { car, cdr } => {
            let car_h = hash_of(heap, car);
            let cdr_h = hash_of(heap, cdr);
            let mut buf = [0u8; 1 + 32 + 32];
            buf[0] = TAG_CONS;
            buf[1..33].copy_from_slice(car_h.as_bytes());
            buf[33..65].copy_from_slice(cdr_h.as_bytes());
            FORSP_CTX.tag(buf)
        }
        Cell::Atom(s) => {
            let bytes = s.as_bytes();
            let mut buf = Vec::with_capacity(1 + 4 + bytes.len());
            buf.push(TAG_ATOM);
            buf.extend_from_slice(&(bytes.len() as u32).to_le_bytes());
            buf.extend_from_slice(bytes);
            FORSP_CTX.tag(buf)
        }
        Cell::Int(n) => {
            let mut buf = [0u8; 1 + 4];
            buf[0] = TAG_INT;
            buf[1..5].copy_from_slice(&n.to_le_bytes());
            FORSP_CTX.tag(buf)
        }
        Cell::Hash(h) => {
            let mut buf = [0u8; 1 + 32];
            buf[0] = TAG_HASH;
            buf[1..33].copy_from_slice(h.as_bytes());
            FORSP_CTX.tag(buf)
        }
        Cell::Blob(b) => {
            let mut buf = Vec::with_capacity(1 + 4 + b.len());
            buf.push(TAG_BLOB);
            buf.extend_from_slice(&(b.len() as u32).to_le_bytes());
            buf.extend_from_slice(&b);
            FORSP_CTX.tag(buf)
        }
        Cell::Closure { body, env } => {
            let body_h = hash_of(heap, body);
            let env_h = hash_of(heap, env);
            let mut buf = [0u8; 1 + 32 + 32];
            buf[0] = TAG_CLOSURE;
            buf[1..33].copy_from_slice(body_h.as_bytes());
            buf[33..65].copy_from_slice(env_h.as_bytes());
            FORSP_CTX.tag(buf)
        }
        Cell::Prim(p) => FORSP_CTX.tag([TAG_PRIM, prim_id(p)]),
    };
    heap.hash_cache[v.0 as usize] = Some(h);
    heap.by_hash.insert(h, v);
    h
}
