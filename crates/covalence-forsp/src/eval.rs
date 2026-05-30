use super::{Cell, FCtx, FError, ForeignPrims, Forsp, Heap, Prim, Tag, ValRef};

/// Compute (execute) a flat instruction list.
pub fn compute<F: ForeignPrims>(f: &mut Forsp<F>, instrs: ValRef) -> Result<(), FError> {
    let mut ip = instrs;
    while !ip.is_nil() {
        let instr = f.heap.car(ip);
        ip = f.heap.cdr(ip);

        // `quote` is the only special form: push the next value literally.
        if f.heap.tag(instr) == Tag::Atom && f.heap.as_atom(instr) == "quote" {
            if ip.is_nil() {
                return Err(FError::DanglingQuote);
            }
            let val = f.heap.car(ip);
            ip = f.heap.cdr(ip);
            f.push(val);
            continue;
        }

        eval_one(f, instr)?;
    }
    Ok(())
}

/// Evaluate a single expression.
fn eval_one<F: ForeignPrims>(f: &mut Forsp<F>, expr: ValRef) -> Result<(), FError> {
    match f.heap.tag(expr) {
        Tag::Int | Tag::Hash | Tag::Blob => f.push(expr),
        Tag::Nil | Tag::Cons => {
            let env = f.env;
            let clos = f.heap.closure(expr, env);
            f.push(clos);
        }
        Tag::Atom => {
            match env_find(&f.heap, f.env, expr) {
                Ok(val) => apply(f, val)?,
                Err(FError::Unbound(name)) => {
                    // Destructure to allow disjoint field borrows.
                    let Forsp {
                        ref mut foreign,
                        ref mut heap,
                        ref mut stack,
                        ..
                    } = *f;
                    let mut ctx = FCtx { heap, stack };
                    if !foreign.call(&name, &mut ctx)? {
                        return Err(FError::Unbound(name));
                    }
                }
                Err(e) => return Err(e),
            }
            return Ok(());
        }
        Tag::Closure | Tag::Prim => {
            f.push(expr);
        }
    }
    Ok(())
}

/// Apply a value: force closures, call primitives, push anything else.
fn apply<F: ForeignPrims>(f: &mut Forsp<F>, val: ValRef) -> Result<(), FError> {
    match f.heap.tag(val) {
        Tag::Closure => {
            let (body, cenv) = match f.heap.get(val) {
                Cell::Closure { body, env } => (*body, *env),
                _ => unreachable!(),
            };
            let saved = f.env;
            f.env = cenv;
            compute(f, body)?;
            f.env = saved;
        }
        Tag::Prim => {
            let p = match f.heap.get(val) {
                Cell::Prim(p) => *p,
                _ => unreachable!(),
            };
            exec_prim(f, p)?;
        }
        _ => f.push(val),
    }
    Ok(())
}

/// Look up `name` (an Atom ValRef) in the environment.
fn env_find(heap: &Heap, env: ValRef, name: ValRef) -> Result<ValRef, FError> {
    let target = heap.as_atom(name);
    let mut cur = env;
    while !cur.is_nil() {
        let pair = heap.car(cur);
        let key = heap.car(pair);
        if heap.tag(key) == Tag::Atom && heap.as_atom(key) == target {
            return Ok(heap.cdr(pair));
        }
        cur = heap.cdr(cur);
    }
    Err(FError::Unbound(target.to_string()))
}

fn exec_prim<F: ForeignPrims>(f: &mut Forsp<F>, p: Prim) -> Result<(), FError> {
    match p {
        Prim::Push => {
            let name = f.try_pop()?;
            let val = env_find(&f.heap, f.env, name)?;
            f.push(val);
        }
        Prim::Pop => {
            let name = f.try_pop()?;
            let val = f.try_pop()?;
            let pair = f.heap.cons(name, val);
            f.env = f.heap.cons(pair, f.env);
        }
        Prim::Eq => {
            let a = f.try_pop()?;
            let b = f.try_pop()?;
            if val_eq(&f.heap, a, b) {
                let t = f.heap.atom("t");
                f.push(t);
            } else {
                f.push(ValRef::NIL);
            }
        }
        Prim::Cons => {
            let car = f.try_pop()?;
            let cdr = f.try_pop()?;
            let pair = f.heap.cons(car, cdr);
            f.push(pair);
        }
        Prim::Car => {
            let v = f.try_pop()?;
            let car = f.heap.try_car(v)?;
            f.push(car);
        }
        Prim::Cdr => {
            let v = f.try_pop()?;
            let cdr = f.heap.try_cdr(v)?;
            f.push(cdr);
        }
        Prim::Cswap => {
            let cond = f.try_pop()?;
            if cond.is_nil() {
                let a = f.try_pop()?;
                let b = f.try_pop()?;
                f.push(a);
                f.push(b);
            }
        }
        Prim::Tag => {
            let val = f.try_peek()?;
            let tag = match f.heap.tag(val) {
                Tag::Nil => "nil",
                Tag::Atom => "atom",
                Tag::Int => "num",
                Tag::Hash => "hash",
                Tag::Blob => "blob",
                Tag::Cons => "pair",
                Tag::Closure => "closure",
                Tag::Prim => "prim",
            };
            let t = f.heap.atom(tag);
            f.push(t);
        }
        Prim::Force => {
            let val = f.try_pop()?;
            apply(f, val)?;
        }
        Prim::Add => int_binop(f, "+", |a, b| a.wrapping_add(b))?,
        Prim::Sub => int_binop(f, "-", |a, b| a.wrapping_sub(b))?,
        Prim::Mul => int_binop(f, "*", |a, b| a.wrapping_mul(b))?,
        Prim::Nand => int_binop(f, "nand", |a, b| !(a & b))?,
        Prim::Lsh => int_binop(f, "<<", |a, b| a.wrapping_shl(b as u32))?,
        Prim::Rsh => int_binop(f, ">>", |a, b| a.wrapping_shr(b as u32))?,
        Prim::Stack => {
            let s = f.stack;
            f.push(s);
        }
        Prim::Env => {
            let e = f.env;
            f.push(e);
        }
    }
    Ok(())
}

fn int_binop<F: ForeignPrims>(
    f: &mut Forsp<F>,
    op: &'static str,
    func: impl FnOnce(i32, i32) -> i32,
) -> Result<(), FError> {
    let bv = f.try_pop()?;
    let av = f.try_pop()?;
    let b = f.heap.try_as_int(bv).map_err(|_| FError::Type {
        op,
        expected: "int",
        got: f.heap.tag(bv),
    })?;
    let a = f.heap.try_as_int(av).map_err(|_| FError::Type {
        op,
        expected: "int",
        got: f.heap.tag(av),
    })?;
    let r = f.heap.int(func(a, b));
    f.push(r);
    Ok(())
}

fn val_eq(heap: &super::Heap, a: ValRef, b: ValRef) -> bool {
    if a == b {
        return true;
    }
    match (heap.get(a), heap.get(b)) {
        (Cell::Nil, Cell::Nil) => true,
        (Cell::Atom(a), Cell::Atom(b)) => a == b,
        (Cell::Int(a), Cell::Int(b)) => a == b,
        (Cell::Hash(a), Cell::Hash(b)) => a == b,
        (Cell::Blob(a), Cell::Blob(b)) => a == b,
        _ => false,
    }
}
