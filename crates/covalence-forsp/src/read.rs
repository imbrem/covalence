use covalence_hash::O256;
use covalence_sexp::{SExp, SExpr, parse_smt};

use super::{FError, Heap, Tag, ValRef, vec_to_list};

/// Parse an entire source string as a flat instruction list.
/// Sugar is expanded inline: `$x` → `quote x pop`, etc.
pub fn read(heap: &mut Heap, source: &str) -> Result<ValRef, FError> {
    let sexps = parse_smt(source).map_err(|e| FError::Parse(e.to_string()))?;
    let mut elems = Vec::new();
    convert_body(&sexps, heap, &mut elems);
    Ok(vec_to_list(heap, &elems))
}

/// Parse a single S-expression from source (first expression only).
pub fn read_one(heap: &mut Heap, source: &str) -> Result<ValRef, FError> {
    let sexps = parse_smt(source).map_err(|e| FError::Parse(e.to_string()))?;
    if sexps.is_empty() {
        return Err(FError::Parse("empty input".into()));
    }
    Ok(convert_expr(&sexps[0], heap))
}

/// Convert a sequence of SExprs into flat ValRef list elements,
/// expanding Forsp sugar inline.
fn convert_body(sexps: &[SExpr], heap: &mut Heap, out: &mut Vec<ValRef>) {
    let mut i = 0;
    while i < sexps.len() {
        if let Some(sym) = sexps[i].as_symbol() {
            // Standalone sugar character followed by a next expression.
            if matches!(sym, "'" | "$" | "^") {
                if i + 1 < sexps.len() {
                    let expr = convert_expr(&sexps[i + 1], heap);
                    out.push(heap.atom("quote"));
                    out.push(expr);
                    match sym {
                        "$" => out.push(heap.atom("pop")),
                        "^" => out.push(heap.atom("push")),
                        _ => {}
                    }
                    i += 2;
                    continue;
                }
            }
            // Sugar prefix attached to atom: `$x`, `^foo`, `'bar`.
            if let Some(expanded) = try_expand_sugar(sym, heap) {
                out.extend(expanded);
                i += 1;
                continue;
            }
        }
        out.push(convert_expr(&sexps[i], heap));
        i += 1;
    }
}

/// Try to expand a symbol with a leading sugar character.
/// Returns `None` if the symbol doesn't start with sugar.
fn try_expand_sugar(sym: &str, heap: &mut Heap) -> Option<Vec<ValRef>> {
    let (prefix, rest) = sym.split_at(1);
    if rest.is_empty() {
        return None;
    }
    let sigil = prefix.as_bytes()[0];
    if !matches!(sigil, b'\'' | b'$' | b'^') {
        return None;
    }
    let expr = symbol_to_val(rest, heap);
    let mut out = vec![heap.atom("quote"), expr];
    match sigil {
        b'$' => out.push(heap.atom("pop")),
        b'^' => out.push(heap.atom("push")),
        _ => {}
    }
    Some(out)
}

/// Convert a single SExpr into a ValRef.
/// Sugar in expression position produces a list value.
fn convert_expr(sexp: &SExpr, heap: &mut Heap) -> ValRef {
    match sexp {
        SExp::Atom(atom) => match atom {
            covalence_sexp::Atom::Symbol(s) => {
                let sym = s.as_str();
                // Sugar in expression position → produce a list value.
                if let Some(elems) = try_expand_sugar(sym, heap) {
                    return vec_to_list(heap, &elems);
                }
                symbol_to_val(sym, heap)
            }
            covalence_sexp::Atom::Str { bytes, .. } => heap.blob(bytes.to_vec()),
        },
        SExp::List(children) if children.is_empty() => ValRef::NIL,
        SExp::List(children) => {
            let mut elems = Vec::new();
            convert_body(children, heap, &mut elems);
            build_list(heap, &elems)
        }
    }
}

/// Build a cons-list from expanded elements, recognizing dot notation.
/// `(a b . c)` → `cons(a, cons(b, c))`.
fn build_list(heap: &mut Heap, elems: &[ValRef]) -> ValRef {
    let len = elems.len();
    if len >= 3 {
        let dot = elems[len - 2];
        if heap.tag(dot) == Tag::Atom && heap.as_atom(dot) == "." {
            let mut list = elems[len - 1];
            for &e in elems[..len - 2].iter().rev() {
                list = heap.cons(e, list);
            }
            return list;
        }
    }
    vec_to_list(heap, elems)
}

/// Convert a symbol string to a ValRef.
/// - integers → Int
/// - 64 hex chars → Hash
/// - everything else → Atom
fn symbol_to_val(s: &str, heap: &mut Heap) -> ValRef {
    if let Ok(n) = s.parse::<i32>() {
        heap.int(n)
    } else if let Some(h) = O256::from_hex(s) {
        heap.hash(h)
    } else {
        heap.atom(s)
    }
}
