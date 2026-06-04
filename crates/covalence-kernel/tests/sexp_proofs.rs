//! End-to-end MVP tests driven through an S-expression surface.
//!
//! Each test parses a tiny DSL into terms / proofs against the kernel
//! and renders the resulting Thm's conclusion back to S-expression
//! text. The DSL is the contract: as long as kernel changes preserve
//! the meaning of these scripts, the tests stay green.
//!
//! Scope: nat / int literals and their op1/op2 primitives, plus
//! `comb`, `lam`, `eq`, and the inference rules `refl`, `reduce`,
//! `sym`, `trans`, `cong`, `beta`, `abs`, `inst`, `union`. Boolean
//! and fixed-width primops are intentionally left out — they're
//! still in flux.
//!
//! DSL grammar (sketch):
//! ```text
//! term  ::= <natlit>                  ; bare digits → Nat
//!         | (int <signed>)            ; explicit Int literal
//!         | (free <name> <ty>)        ; free variable
//!         | (comb <term> <term>)
//!         | (lam <name> <ty> <term>)  ; closes <term> over Free(name, ty)
//!         | (eq <term> <term>)
//!         | (nat+ a b) | (nat- a b) | (nat* a b) | (nat/ a b)
//!         | (nat.succ a) | (nat.pred a)
//!         | (int+ a b) | (int- a b) | (int.neg a)
//! ty    ::= nat | int
//! proof ::= (refl <term>)
//!         | (reduce <term>)
//!         | (sym <proof>)
//!         | (trans <proof> <proof>)
//!         | (cong <term> <term> <natlit>)
//!         | (beta <term>)
//!         | (abs <proof> <name> <ty>)
//!         | (inst <proof> <name> <ty> <term>)
//! ```
//!
//! The driver also exposes a side command `(union <term> <term>)` for
//! tests that need to seed the UF before a congruence step.

use std::collections::HashMap;

use covalence_kernel::{
    Arena, Kernel, PrimOp1, PrimOp2, ProofError, Thm,
};
use covalence_kernel::id::TermId;
use covalence_kernel::term::{TermDef, TermRef};
use covalence_kernel::ty::TypeRef;
use covalence_sexp::{SExpr, parse};

#[derive(Debug)]
enum DriverError {
    Parse(covalence_sexp::ParseError),
    Eval(String),
    Proof(ProofError),
}

impl From<ProofError> for DriverError {
    fn from(e: ProofError) -> Self {
        DriverError::Proof(e)
    }
}

impl std::fmt::Display for DriverError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DriverError::Parse(e) => write!(f, "parse: {e}"),
            DriverError::Eval(s) => write!(f, "eval: {s}"),
            DriverError::Proof(e) => write!(f, "proof: {e}"),
        }
    }
}

struct Driver {
    kernel: Kernel,
    /// Raw-def dedup: same structural def → same TermId. Used at
    /// parse-time to avoid re-allocating identical literals.
    intern_memo: HashMap<TermDef, TermRef>,
    /// Canonical-def → first-seen ref. Drives UF unification of
    /// structurally-different-but-canonically-equivalent terms
    /// (e.g. `(nat+ x 3)` and `(nat+ y 3)` when `x ≡ y` already).
    canon_memo: HashMap<TermDef, TermRef>,
    /// Term-table watermark: first unswept term. Sweep walks any
    /// new terms allocated by kernel internals (subst, reduce, …)
    /// and registers them in both memos.
    swept: u32,
}

impl Driver {
    fn new() -> Self {
        Self {
            kernel: Kernel::new(),
            intern_memo: HashMap::new(),
            canon_memo: HashMap::new(),
            swept: 0,
        }
    }

    fn intern_term(&mut self, def: TermDef) -> TermRef {
        // Walk any backstage allocations first so we see existing
        // structurally-identical terms (e.g. β-substitution products).
        self.sweep();
        if let Some(&r) = self.intern_memo.get(&def) {
            return r;
        }
        let r = TermRef::local(self.kernel.arena_mut().alloc_term(def));
        self.intern_memo.insert(def, r);
        let canon = self.canonicalize_def(def);
        self.canon_memo.entry(canon).or_insert(r);
        self.swept = self.kernel.arena().num_terms();
        r
    }

    /// Walk every term allocated since `self.swept` and reconcile it
    /// with both memos. New raw-def terms go into `intern_memo`; new
    /// canonical-def keys go into `canon_memo`; any duplicate canonical
    /// keys trigger a UF union to keep level-0 equality consistent.
    fn sweep(&mut self) {
        let total = self.kernel.arena().num_terms();
        while self.swept < total {
            let id = TermId(self.swept);
            self.swept += 1;
            let raw = *self.kernel.arena().term_def(id);
            let canon = self.canonicalize_def(raw);
            let this = TermRef::local(id);
            self.intern_memo.entry(raw).or_insert(this);
            if let Some(&existing) = self.canon_memo.get(&canon) {
                if existing != this {
                    let _ = self.kernel.uf_mut().union(this, existing);
                }
            } else {
                self.canon_memo.insert(canon, this);
            }
        }
    }

    fn canonicalize_def(&self, def: TermDef) -> TermDef {
        let uf = self.kernel.uf();
        let cm = |r: TermRef| uf.canonical_local(r);
        use TermDef::*;
        match def {
            Comb(a, b) => Comb(cm(a), cm(b)),
            Eq(a, b) => Eq(cm(a), cm(b)),
            Op2(o, a, b) => Op2(o, cm(a), cm(b)),
            Op1(o, x) => Op1(o, cm(x)),
            Forall(x) => Forall(cm(x)),
            Exists(x) => Exists(cm(x)),
            Eps(t, x) => Eps(t, cm(x)),
            Lam(t, x) => Lam(t, cm(x)),
            other => other,
        }
    }

    fn arena(&self) -> &Arena {
        self.kernel.arena()
    }

    /// Parse, then dispatch the first form. Returns the resulting
    /// rendered conclusion if it's a proof form; for raw terms,
    /// returns the rendered term.
    fn run(&mut self, src: &str) -> Result<String, DriverError> {
        let forms = parse(src).map_err(DriverError::Parse)?;
        let form = forms.into_iter().next().ok_or_else(|| {
            DriverError::Eval("empty input".into())
        })?;
        let value = self.eval(&form)?;
        self.sweep();
        match value {
            Value::Thm(thm) => Ok(self.render_term_id(thm.concl())),
            Value::Term(r) => Ok(self.render_termref(r)),
            Value::Unit => Ok(String::new()),
        }
    }

    fn eval(&mut self, e: &SExpr) -> Result<Value, DriverError> {
        // Symbol → either a nat literal or a built-in symbol.
        if let Some(sym) = e.as_symbol() {
            return Ok(Value::Term(self.parse_natlit(sym)?));
        }
        let list = e.as_list().ok_or_else(|| {
            DriverError::Eval(format!("expected list or symbol, got {e:?}"))
        })?;
        let head = list.first().and_then(|h| h.as_symbol()).ok_or_else(|| {
            DriverError::Eval(format!("expected head symbol in {list:?}"))
        })?;
        let args = &list[1..];
        match head {
            // ---- term forms ------------------------------------------------
            "int" => self.eval_int_lit(args).map(Value::Term),
            "free" => self.eval_free(args).map(Value::Term),
            "comb" => self.eval_binary_term(args, |f, x| TermDef::Comb(f, x)),
            "eq" => self.eval_binary_term(args, |a, b| TermDef::Eq(a, b)),
            "lam" => self.eval_lam(args).map(Value::Term),
            // Nat ops.
            "nat+" => self.eval_op2(args, PrimOp2::NatAdd),
            "nat-" => self.eval_op2(args, PrimOp2::NatSub),
            "nat*" => self.eval_op2(args, PrimOp2::NatMul),
            "nat/" => self.eval_op2(args, PrimOp2::NatDiv),
            "nat%" => self.eval_op2(args, PrimOp2::NatMod),
            "nat=" => self.eval_op2(args, PrimOp2::NatEq),
            "nat<" => self.eval_op2(args, PrimOp2::NatLt),
            "nat<=" => self.eval_op2(args, PrimOp2::NatLe),
            "nat.succ" => self.eval_op1(args, PrimOp1::NatSucc),
            "nat.pred" => self.eval_op1(args, PrimOp1::NatPred),
            "nat.popcount" => self.eval_op1(args, PrimOp1::NatPopcount),
            // Int ops.
            "int+" => self.eval_op2(args, PrimOp2::IntAdd),
            "int-" => self.eval_op2(args, PrimOp2::IntSub),
            "int*" => self.eval_op2(args, PrimOp2::IntMul),
            "int=" => self.eval_op2(args, PrimOp2::IntEq),
            "int<" => self.eval_op2(args, PrimOp2::IntLt),
            "int<=" => self.eval_op2(args, PrimOp2::IntLe),
            "int.neg" => self.eval_op1(args, PrimOp1::IntNeg),
            // ---- proof forms ----------------------------------------------
            "refl" => self.eval_unary_proof(args, |k, t| k.refl(t)),
            "reduce" => self.eval_unary_proof(args, |k, t| k.reduce(t)),
            "sym" => self.eval_unary_thm(args, |k, p| k.sym(p)),
            "trans" => self.eval_binary_thm(args, |k, a, b| k.trans(a, b)),
            "cong" => self.eval_cong(args),
            "beta" => self.eval_unary_proof(args, |k, t| k.beta(t)),
            "abs" => self.eval_abs(args),
            "inst" => self.eval_inst(args),
            // ---- side effects ---------------------------------------------
            "union" => self.eval_union(args),
            other => Err(DriverError::Eval(format!("unknown head `{other}`"))),
        }
    }

    // ---- term parsers ------------------------------------------------------

    fn parse_natlit(&mut self, sym: &str) -> Result<TermRef, DriverError> {
        let n: u64 = sym.parse().map_err(|_| {
            DriverError::Eval(format!("not a Nat literal: `{sym}`"))
        })?;
        Ok(self.intern_term(TermDef::nat_inline(n)))
    }

    fn parse_int(&mut self, sym: &str) -> Result<i64, DriverError> {
        sym.parse::<i64>()
            .map_err(|_| DriverError::Eval(format!("not an Int literal: `{sym}`")))
    }

    fn eval_int_lit(&mut self, args: &[SExpr]) -> Result<TermRef, DriverError> {
        let [n] = self.exact(args, 1)?;
        let sym = n.as_symbol().ok_or_else(|| {
            DriverError::Eval(format!("(int …) needs a symbol arg, got {n:?}"))
        })?;
        let v = self.parse_int(sym)?;
        Ok(self.intern_term(TermDef::int_inline(v)))
    }

    fn eval_free(&mut self, args: &[SExpr]) -> Result<TermRef, DriverError> {
        let [name, ty] = self.exact(args, 2)?;
        let name = name.as_symbol().ok_or_else(|| {
            DriverError::Eval("free: name must be symbol".into())
        })?;
        let ty = self.parse_ty(ty)?;
        let n = self.kernel.arena_mut().intern_string(name.into());
        Ok(self.intern_term(TermDef::Free(n, ty)))
    }

    fn eval_lam(&mut self, args: &[SExpr]) -> Result<TermRef, DriverError> {
        let [name, ty, body] = self.exact(args, 3)?;
        let name = name
            .as_symbol()
            .ok_or_else(|| DriverError::Eval("lam: name must be symbol".into()))?;
        let ty = self.parse_ty(ty)?;
        let body = self.eval_term(body)?;
        let n = self.kernel.arena_mut().intern_string(name.into());
        let abstracted = self.kernel.arena_mut().abstract_over(body, n, ty, 0);
        let result = self.intern_term(TermDef::Lam(ty, abstracted));
        // Resolve cached type info under binders so downstream Thm
        // rules read this as well-typed.
        if let Some(id) = result.as_local() {
            self.kernel.arena_mut().infer(id);
        }
        Ok(result)
    }

    fn parse_ty(&self, ty: &SExpr) -> Result<TypeRef, DriverError> {
        let sym = ty.as_symbol().ok_or_else(|| {
            DriverError::Eval(format!("type must be symbol, got {ty:?}"))
        })?;
        match sym {
            "nat" => Ok(self.kernel.nat_ty()),
            "int" => Ok(self.kernel.int_ty()),
            other => Err(DriverError::Eval(format!("unknown type `{other}`"))),
        }
    }

    fn eval_term(&mut self, e: &SExpr) -> Result<TermRef, DriverError> {
        match self.eval(e)? {
            Value::Term(t) => Ok(t),
            Value::Thm(_) => Err(DriverError::Eval("expected term, got Thm".into())),
            Value::Unit => Err(DriverError::Eval("expected term, got unit".into())),
        }
    }

    fn eval_thm(&mut self, e: &SExpr) -> Result<Thm, DriverError> {
        match self.eval(e)? {
            Value::Thm(t) => Ok(t),
            Value::Term(_) => Err(DriverError::Eval("expected Thm, got term".into())),
            Value::Unit => Err(DriverError::Eval("expected Thm, got unit".into())),
        }
    }

    fn eval_op1(&mut self, args: &[SExpr], op: PrimOp1) -> Result<Value, DriverError> {
        let [a] = self.exact(args, 1)?;
        let a = self.eval_term(a)?;
        Ok(Value::Term(self.intern_term(TermDef::Op1(op, a))))
    }

    fn eval_op2(&mut self, args: &[SExpr], op: PrimOp2) -> Result<Value, DriverError> {
        let [a, b] = self.exact(args, 2)?;
        let a = self.eval_term(a)?;
        let b = self.eval_term(b)?;
        Ok(Value::Term(self.intern_term(TermDef::Op2(op, a, b))))
    }

    fn eval_binary_term<F: FnOnce(TermRef, TermRef) -> TermDef>(
        &mut self,
        args: &[SExpr],
        f: F,
    ) -> Result<Value, DriverError> {
        let [a, b] = self.exact(args, 2)?;
        let a = self.eval_term(a)?;
        let b = self.eval_term(b)?;
        let def = f(a, b);
        Ok(Value::Term(self.intern_term(def)))
    }

    // ---- proof parsers -----------------------------------------------------

    fn eval_unary_proof<F: FnOnce(&mut Kernel, TermRef) -> Result<Thm, ProofError>>(
        &mut self,
        args: &[SExpr],
        f: F,
    ) -> Result<Value, DriverError> {
        let [t] = self.exact(args, 1)?;
        let t = self.eval_term(t)?;
        let thm = f(&mut self.kernel, t)?;
        Ok(Value::Thm(thm))
    }

    fn eval_unary_thm<F: FnOnce(&mut Kernel, Thm) -> Result<Thm, ProofError>>(
        &mut self,
        args: &[SExpr],
        f: F,
    ) -> Result<Value, DriverError> {
        let [p] = self.exact(args, 1)?;
        let p = self.eval_thm(p)?;
        let thm = f(&mut self.kernel, p)?;
        Ok(Value::Thm(thm))
    }

    fn eval_binary_thm<F: FnOnce(&mut Kernel, Thm, Thm) -> Result<Thm, ProofError>>(
        &mut self,
        args: &[SExpr],
        f: F,
    ) -> Result<Value, DriverError> {
        let [a, b] = self.exact(args, 2)?;
        let a = self.eval_thm(a)?;
        let b = self.eval_thm(b)?;
        let thm = f(&mut self.kernel, a, b)?;
        Ok(Value::Thm(thm))
    }

    fn eval_cong(&mut self, args: &[SExpr]) -> Result<Value, DriverError> {
        let [a, b, d] = self.exact(args, 3)?;
        let a = self.eval_term(a)?;
        let b = self.eval_term(b)?;
        let depth: u32 = d
            .as_symbol()
            .and_then(|s| s.parse().ok())
            .ok_or_else(|| DriverError::Eval("cong: depth must be a u32 literal".into()))?;
        Ok(Value::Thm(self.kernel.cong(a, b, depth)?))
    }

    fn eval_abs(&mut self, args: &[SExpr]) -> Result<Value, DriverError> {
        let [p, name, ty] = self.exact(args, 3)?;
        let p = self.eval_thm(p)?;
        let name = name
            .as_symbol()
            .ok_or_else(|| DriverError::Eval("abs: name must be symbol".into()))?;
        let ty = self.parse_ty(ty)?;
        let thm = self.kernel.abs(p, name, ty)?;
        Ok(Value::Thm(thm))
    }

    fn eval_inst(&mut self, args: &[SExpr]) -> Result<Value, DriverError> {
        let [p, name, ty, t] = self.exact(args, 4)?;
        let p = self.eval_thm(p)?;
        let name = name
            .as_symbol()
            .ok_or_else(|| DriverError::Eval("inst: name must be symbol".into()))?;
        let ty = self.parse_ty(ty)?;
        let t = self.eval_term(t)?;
        let thm = self.kernel.inst(p, name, ty, t)?;
        Ok(Value::Thm(thm))
    }

    fn eval_union(&mut self, args: &[SExpr]) -> Result<Value, DriverError> {
        let [a, b] = self.exact(args, 2)?;
        let a = self.eval_term(a)?;
        let b = self.eval_term(b)?;
        self.kernel
            .union(a, b)
            .map_err(|e| DriverError::Eval(format!("union: {e:?}")))?;
        Ok(Value::Unit)
    }

    fn exact<'a, const N: usize>(
        &self,
        args: &'a [SExpr],
        _n: usize,
    ) -> Result<&'a [SExpr; N], DriverError> {
        <&[SExpr; N]>::try_from(args).map_err(|_| {
            DriverError::Eval(format!("expected {N} args, got {}", args.len()))
        })
    }

    // ---- rendering ---------------------------------------------------------

    fn render_term_id(&self, id: TermId) -> String {
        self.render_termref(TermRef::local(id))
    }

    fn render_termref(&self, r: TermRef) -> String {
        use covalence_kernel::term::TermKind;
        let Some(id) = r.as_local() else {
            return "<foreign>".to_string();
        };
        match self.arena().kind(id) {
            TermKind::Nat(n) => format!("{n}"),
            TermKind::Int(n) => format!("(int {n})"),
            TermKind::Free(n, _) => self.arena().string(n).to_string(),
            TermKind::Bound(i) => format!("(bound {i})"),
            TermKind::Bool(true) => "true".to_string(),
            TermKind::Bool(false) => "false".to_string(),
            TermKind::Comb(f, x) => {
                format!("(comb {} {})", self.render_termref(f), self.render_termref(x))
            }
            TermKind::Eq(a, b) => {
                format!("(eq {} {})", self.render_termref(a), self.render_termref(b))
            }
            TermKind::Lam(ty, body) => format!(
                "(lam {} {})",
                self.render_ty(ty),
                self.render_termref(body)
            ),
            TermKind::Op1(op, x) => format!("({} {})", op1_sym(op), self.render_termref(x)),
            TermKind::Op2(op, a, b) => format!(
                "({} {} {})",
                op2_sym(op),
                self.render_termref(a),
                self.render_termref(b)
            ),
            other => format!("<{other:?}>"),
        }
    }

    fn render_ty(&self, ty: TypeRef) -> String {
        if ty == self.kernel.nat_ty() {
            "nat".to_string()
        } else if ty == self.kernel.int_ty() {
            "int".to_string()
        } else {
            format!("<ty {:?}>", ty)
        }
    }
}

enum Value {
    Term(TermRef),
    Thm(Thm),
    Unit,
}

fn op1_sym(op: PrimOp1) -> &'static str {
    match op {
        PrimOp1::NatSucc => "nat.succ",
        PrimOp1::NatPred => "nat.pred",
        PrimOp1::NatPopcount => "nat.popcount",
        PrimOp1::IntNeg => "int.neg",
        _ => "<op1>",
    }
}

fn op2_sym(op: PrimOp2) -> &'static str {
    use PrimOp2::*;
    match op {
        NatAdd => "nat+",
        NatSub => "nat-",
        NatMul => "nat*",
        NatDiv => "nat/",
        NatMod => "nat%",
        NatEq => "nat=",
        NatLt => "nat<",
        NatLe => "nat<=",
        IntAdd => "int+",
        IntSub => "int-",
        IntMul => "int*",
        IntEq => "int=",
        IntLt => "int<",
        IntLe => "int<=",
        _ => "<op2>",
    }
}


// ===========================================================================
// Tests
// ===========================================================================

fn check(src: &str, expected: &str) {
    let mut d = Driver::new();
    let actual = match d.run(src) {
        Ok(s) => s,
        Err(e) => panic!("driver error on `{src}`: {e}"),
    };
    assert_eq!(actual, expected, "input: {src}");
}

// --- arithmetic reductions ---

#[test]
fn nat_add_reduces() {
    check("(reduce (nat+ 1 2))", "(eq (nat+ 1 2) 3)");
}

#[test]
fn nat_succ_reduces() {
    check("(reduce (nat.succ 4))", "(eq (nat.succ 4) 5)");
}

#[test]
fn nat_mul_reduces() {
    check("(reduce (nat* 6 7))", "(eq (nat* 6 7) 42)");
}

#[test]
fn nat_div_by_zero_reduces_to_zero() {
    check("(reduce (nat/ 5 0))", "(eq (nat/ 5 0) 0)");
}

#[test]
fn int_add_reduces() {
    check("(reduce (int+ (int 5) (int -3)))", "(eq (int+ (int 5) (int -3)) (int 2))");
}

#[test]
fn int_neg_reduces() {
    check("(reduce (int.neg (int 7)))", "(eq (int.neg (int 7)) (int -7))");
}

// --- congruence chains ---

#[test]
fn cong_succeeds_on_already_unioned_children() {
    let mut d = Driver::new();
    d.run("(union 1 9)").unwrap();
    let actual = d.run("(cong (nat+ 1 2) (nat+ 9 2) 1)").unwrap();
    assert_eq!(actual, "(eq (nat+ 1 2) (nat+ 9 2))");
}

#[test]
fn cong_depth_two_matches_structural_leaves() {
    // No UF setup needed at depth 2: structural equality of leaves
    // suffices when the literals are identical TermIds (alloc_term
    // doesn't dedupe but Nat 5 ≡ Nat 5 structurally at depth ≥ 1).
    check(
        "(cong (nat+ 5 6) (nat+ 5 6) 2)",
        "(eq (nat+ 5 6) (nat+ 5 6))",
    );
}

// --- compound: union + cong + trans for chained arithmetic ---

#[test]
fn chained_nat_add_via_union_cong_trans() {
    // Prove (1+2)+3 = 6 via:
    //   - reduce (1+2) = 3
    //   - union 1+2 with 3 in UF
    //   - cong on (1+2)+3 vs 3+3 (depth 1; outer-children canonical-equal)
    //   - reduce 3+3 = 6
    //   - trans
    let mut d = Driver::new();
    let _ = d.run("(reduce (nat+ 1 2))").unwrap();
    d.run("(union (nat+ 1 2) 3)").unwrap();
    let actual = d
        .run("(trans (cong (nat+ (nat+ 1 2) 3) (nat+ 3 3) 1) (reduce (nat+ 3 3)))")
        .unwrap();
    assert_eq!(actual, "(eq (nat+ (nat+ 1 2) 3) 6)");
}

// --- beta reduction ---

#[test]
fn beta_identity_on_nat() {
    // (λx:nat. x) 7  =β=>  7.
    check(
        "(beta (comb (lam x nat (free x nat)) 7))",
        "(eq (comb (lam nat (bound 0)) 7) 7)",
    );
}

#[test]
fn beta_then_reduce_succ() {
    // (λx:nat. nat.succ x) 4  =β=>  nat.succ 4  =reduce=>  5.
    let mut d = Driver::new();
    let lam_src = "(lam x nat (nat.succ (free x nat)))";
    let app_src = format!("(comb {lam_src} 4)");
    let beta_src = format!("(beta {app_src})");
    let beta_rhs_src = format!("(nat.succ 4)"); // RHS of beta-expanded form
    let trans_src = format!("(trans {beta_src} (reduce {beta_rhs_src}))");
    let actual = d.run(&trans_src).unwrap();
    assert_eq!(actual, "(eq (comb (lam nat (nat.succ (bound 0))) 4) 5)");
}

// --- abstraction proofs ---

#[test]
fn abs_lifts_refl_over_free_variable() {
    check(
        "(abs (refl (free x nat)) x nat)",
        "(eq (lam nat (bound 0)) (lam nat (bound 0)))",
    );
}

#[test]
fn inst_specializes_refl() {
    check(
        "(inst (refl (free x nat)) x nat 9)",
        "(eq 9 9)",
    );
}
