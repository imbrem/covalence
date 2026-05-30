use covalence_sexp::{SExp, SExpr, prettyprint};

use super::{Cell, Heap, Prim, ValRef};

/// Convert a heap value to an SExpr for display/serialisation.
pub fn to_sexp(heap: &Heap, v: ValRef) -> SExpr {
    match heap.get(v) {
        Cell::Nil => SExp::List(vec![]),
        Cell::Atom(s) => SExp::symbol(s.as_str()),
        Cell::Int(n) => SExp::symbol(n.to_string()),
        Cell::Hash(h) => SExp::symbol(h.to_string()),
        Cell::Blob(b) => SExp::string("", b.clone()),
        Cell::Cons { .. } => {
            let mut items = Vec::new();
            let mut cur = v;
            loop {
                match heap.get(cur) {
                    Cell::Nil => break,
                    Cell::Cons { car, cdr } => {
                        items.push(to_sexp(heap, *car));
                        cur = *cdr;
                    }
                    _ => {
                        // improper list: (a b . c)
                        items.push(SExp::symbol("."));
                        items.push(to_sexp(heap, cur));
                        break;
                    }
                }
            }
            SExp::List(items)
        }
        Cell::Closure { body, .. } => {
            SExp::List(vec![SExp::symbol("#<closure>"), to_sexp(heap, *body)])
        }
        Cell::Prim(p) => SExp::symbol(format!("#<prim:{}>", prim_name(*p))),
    }
}

/// Format a heap value as a string via covalence-sexp prettyprint.
pub fn show(heap: &Heap, v: ValRef) -> String {
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
