use covalence_sexp::{SExp, SExpr, prettyprint};

use super::{Cell, Heap, Prim, ValRef};

/// Convert a heap value to an SExpr for display/serialisation.
///
/// Closures are content-addressed: a closure prints as `!<hash>` and its
/// content hash is registered on the heap so the reader can recover it.
pub fn to_sexp(heap: &mut Heap, v: ValRef) -> SExpr {
    // Snapshot the cell tag/payload we need *before* any recursive call that
    // could borrow `heap` mutably (closure hashing recurses).
    match heap.get(v).clone() {
        Cell::Nil => SExp::List(vec![]),
        Cell::Atom(s) => SExp::symbol(s),
        Cell::Int(n) => SExp::symbol(n.to_string()),
        Cell::Hash(h) => SExp::symbol(h.to_string()),
        Cell::Blob(b) => SExp::string("", b),
        Cell::Cons { .. } => {
            let mut items = Vec::new();
            let mut cur = v;
            loop {
                let cell = heap.get(cur).clone();
                match cell {
                    Cell::Nil => break,
                    Cell::Cons { car, cdr } => {
                        items.push(to_sexp(heap, car));
                        cur = cdr;
                    }
                    _ => {
                        items.push(SExp::symbol("."));
                        items.push(to_sexp(heap, cur));
                        break;
                    }
                }
            }
            SExp::List(items)
        }
        Cell::Closure { .. } => {
            let h = heap.content_hash(v);
            SExp::symbol(format!("!{h}"))
        }
        Cell::Prim(p) => SExp::symbol(format!("#<prim:{}>", prim_name(p))),
    }
}

/// Format a heap value as a string via covalence-sexp prettyprint.
pub fn show(heap: &mut Heap, v: ValRef) -> String {
    let sexp = to_sexp(heap, v);
    let mut buf = Vec::new();
    prettyprint(&[sexp], &mut buf).expect("write to Vec never fails");
    String::from_utf8(buf).expect("prettyprint produces valid UTF-8")
}

fn prim_name(p: Prim) -> &'static str {
    match p {
        Prim::Push => "push",
        Prim::Pop => "pop",
        Prim::Eq => "eq",
        Prim::Cons => "cons",
        Prim::Car => "car",
        Prim::Cdr => "cdr",
        Prim::Cswap => "cswap",
        Prim::Tag => "tag",
        Prim::Force => "force",
        Prim::Add => "+",
        Prim::Sub => "-",
        Prim::Mul => "*",
        Prim::Nand => "nand",
        Prim::Lsh => "<<",
        Prim::Rsh => ">>",
        Prim::Stack => "stack",
        Prim::Env => "env",
    }
}
