//! `KernelAletheBridge` — concrete `AletheBridge` impl against any
//! `covalence_shell::Prover`.
//!
//! This is the **only** file in the bridge crate that mentions specific
//! prover operations. The trait surface ([`AletheBridge`]) and the driver
//! stay stable while this file (and the underlying `Prover` impl) churn
//! alongside the kernel.
//!
//! Today the bridge:
//!
//!   - Translates SMT-LIB sorts (`Bool`, `Int`, user sorts via `tyapp`) and
//!     terms (equality, application, n-ary `and`/`or`, propositional
//!     primops, `! :named` annotation passthrough) into `Prover`-level
//!     types/terms.
//!   - Implements `assume` via `push_assumption` + `Prover::assume`.
//!   - Every step rule returns `BridgeError::NotImplemented(rule_name)` —
//!     loud, structured failure tagged with the Alethe rule.
//!
//! Wiring a new rule means adding a match arm in `step()` and calling out
//! to `Prover` methods (`refl`, `trans`, `eq_mp`, `cong`, …). The trait
//! surface above never changes.

use std::collections::HashMap;

use covalence_sexp::{SExp, SExpr};
use covalence_shell::{PrimOp1, PrimOp2, Prover};
use covalence_types::Decision;

use crate::bridge::AletheBridge;
use crate::error::BridgeError;

/// Bridge an Alethe proof into any `P: Prover`.
///
/// Owns:
///   - a mutable prover borrow,
///   - SMT-LIB sort and function environments (so syntactic lookups in
///     `translate_term` can re-construct the kernel type each time),
///   - a stack of locally-bound variables (for future quantifier / anchor
///     support),
///   - the `@named` term cache for SMT-LIB `(! t :named @x)` annotations,
///   - the running `Decision` (flipped to `Unsat` when a step derives the
///     empty clause).
pub struct KernelAletheBridge<'a, P: Prover> {
    prover: &'a mut P,
    /// SMT sort symbol → kernel type. Arity > 0 lives behind the trait via
    /// `tyapp`; we store the *base* type so look-ups are O(1).
    sorts: HashMap<String, P::Type>,
    /// SMT function/constant symbol → kernel type (the constant's signature).
    funs: HashMap<String, P::Type>,
    /// Local variables in scope (innermost last). Each entry is
    /// `(smt-symbol, kernel type)`. Populated by quantifier translation
    /// and (future) anchor scopes; the kernel handles its own name interning
    /// at the `free_var` call site.
    locals: Vec<(String, P::Type)>,
    /// `:named` bindings — `@name` → already-translated kernel term.
    named: HashMap<String, P::Term>,
    /// Set once a step derives the empty clause `(cl)`.
    derived_empty: bool,
}

impl<'a, P: Prover> KernelAletheBridge<'a, P> {
    /// Build a fresh bridge wrapping the given prover.
    pub fn new(prover: &'a mut P) -> Self {
        KernelAletheBridge {
            prover,
            sorts: HashMap::new(),
            funs: HashMap::new(),
            locals: Vec::new(),
            named: HashMap::new(),
            derived_empty: false,
        }
    }

    /// Borrow the underlying prover (e.g. for inspecting kernel state in tests).
    pub fn prover(&self) -> &P {
        self.prover
    }

    /// Look up a declared sort by SMT-LIB symbol.
    pub fn lookup_sort(&self, name: &str) -> Option<P::Type> {
        self.sorts.get(name).copied()
    }

    /// Look up a declared function/constant by SMT-LIB symbol.
    pub fn lookup_fun(&self, name: &str) -> Option<P::Type> {
        self.funs.get(name).copied()
    }

    // ----------------------------------------------------------------
    // Sort translation
    // ----------------------------------------------------------------

    fn translate_sort(&mut self, sort: &SExpr) -> Result<P::Type, BridgeError> {
        match sort {
            SExp::Atom(_) => {
                let sym = sort
                    .as_symbol()
                    .ok_or_else(|| BridgeError::Malformed("sort: expected symbol".into()))?;
                match sym {
                    "Bool" => Ok(self.prover.bool_ty()?),
                    "Int" => Ok(self.prover.int_ty()?),
                    "Real" => Err(BridgeError::NotImplemented("Real sort".into())),
                    other => self
                        .sorts
                        .get(other)
                        .copied()
                        .ok_or_else(|| BridgeError::UnknownSort(other.to_string())),
                }
            }
            SExp::List(_) => Err(BridgeError::Malformed(
                "parametric sort applications not yet supported".into(),
            )),
        }
    }

    fn function_type(
        &mut self,
        params: &[SExpr],
        result: &SExpr,
    ) -> Result<P::Type, BridgeError> {
        let mut ty = self.translate_sort(result)?;
        for p in params.iter().rev() {
            let pty = self.translate_sort(p)?;
            ty = self.prover.fun_ty(pty, ty)?;
        }
        Ok(ty)
    }

    // ----------------------------------------------------------------
    // Term translation
    // ----------------------------------------------------------------

    fn translate_term(&mut self, term: &SExpr) -> Result<P::Term, BridgeError> {
        match term {
            SExp::Atom(_) => {
                let sym = term
                    .as_symbol()
                    .ok_or_else(|| BridgeError::Malformed("term: non-symbol atom".into()))?;
                self.lookup_atom(sym)
            }
            SExp::List(items) => self.translate_app(items),
        }
    }

    fn lookup_atom(&mut self, sym: &str) -> Result<P::Term, BridgeError> {
        // Named-term reference: `@something`.
        if let Some(stripped) = sym.strip_prefix('@') {
            return self
                .named
                .get(&format!("@{stripped}"))
                .copied()
                .ok_or_else(|| BridgeError::UnknownFun(sym.to_string()));
        }

        // Boolean literals (SMT-LIB spelling).
        if sym == "true" {
            return Ok(self.prover.truth()?);
        }
        if sym == "false" {
            return Ok(self.prover.falsity()?);
        }

        // Numeric literals. SMT-LIB numerals are bare digit sequences;
        // negative values use the unary `(- n)` form handled in translate_app.
        if let Ok(n) = sym.parse::<i64>() {
            return Ok(self.prover.int_lit(n)?);
        }

        // Local variable (innermost-first).
        // Clone the snapshot to avoid holding a borrow across the prover call.
        let local = self
            .locals
            .iter()
            .rev()
            .find(|(s, _)| s == sym)
            .map(|(_, ty)| *ty);
        if let Some(ty) = local {
            return Ok(self.prover.free_var(sym, ty)?);
        }

        // Declared function / constant.
        if let Some(ty) = self.funs.get(sym).copied() {
            return Ok(self.prover.const_term(sym, ty)?);
        }

        Err(BridgeError::UnknownFun(sym.to_string()))
    }

    fn translate_app(&mut self, items: &[SExpr]) -> Result<P::Term, BridgeError> {
        let head = items
            .first()
            .ok_or_else(|| BridgeError::Malformed("term: empty application".into()))?;
        let head_sym = head
            .as_symbol()
            .ok_or_else(|| BridgeError::Malformed("term: non-symbol head".into()))?;
        let rest = &items[1..];

        match head_sym {
            "=" => {
                if rest.len() != 2 {
                    return Err(BridgeError::Malformed("=: expected 2 arguments".into()));
                }
                let lhs = self.translate_term(&rest[0])?;
                let rhs = self.translate_term(&rest[1])?;
                Ok(self.prover.eq(lhs, rhs)?)
            }
            "!" => self.translate_annotated(rest),
            "not" => {
                if rest.len() != 1 {
                    return Err(BridgeError::Malformed("not: expected 1 argument".into()));
                }
                let p = self.translate_term(&rest[0])?;
                Ok(self.prover.op1(PrimOp1::LogicalNot, p)?)
            }
            "and" => self.left_fold_op2(PrimOp2::LogicalAnd, rest),
            "or" => self.left_fold_op2(PrimOp2::LogicalOr, rest),
            "=>" => self.right_fold_op2(PrimOp2::LogicalImp, rest),
            "xor" => self.left_fold_op2(PrimOp2::LogicalXor, rest),
            "ite" => Err(BridgeError::NotImplemented("ite".into())),
            "forall" | "exists" | "let" => {
                Err(BridgeError::NotImplemented(format!("binder `{head_sym}`")))
            }
            // -------- LIA arithmetic --------
            //
            // SMT-LIB unifies binary `-` and unary `-` (negation) under one
            // symbol: `(- 5)` is `-5`, `(- x y)` is `x - y`. Disambiguate by
            // arity. n-ary forms left-fold per the SMT-LIB standard.
            "+" => self.left_fold_op2(PrimOp2::IntAdd, rest),
            "*" => self.left_fold_op2(PrimOp2::IntMul, rest),
            "-" => match rest.len() {
                0 => Err(BridgeError::Malformed("-: zero arguments".into())),
                1 => {
                    let x = self.translate_term(&rest[0])?;
                    Ok(self.prover.op1(PrimOp1::IntNeg, x)?)
                }
                _ => self.left_fold_op2(PrimOp2::IntSub, rest),
            },
            "<=" => self.binary_op2(PrimOp2::IntLe, head_sym, rest),
            "<" => self.binary_op2(PrimOp2::IntLt, head_sym, rest),
            // `(>= a b)` is `(<= b a)`; `(> a b)` is `(< b a)`.
            ">=" => self.swapped_binary_op2(PrimOp2::IntLe, head_sym, rest),
            ">" => self.swapped_binary_op2(PrimOp2::IntLt, head_sym, rest),
            _ => {
                // Curried application of a declared constant / local.
                let f = self.lookup_atom(head_sym)?;
                let mut acc = f;
                for arg in rest {
                    let a = self.translate_term(arg)?;
                    acc = self.prover.comb(acc, a)?;
                }
                Ok(acc)
            }
        }
    }

    /// `(op a b)` — exactly two arguments.
    fn binary_op2(
        &mut self,
        op: PrimOp2,
        name: &str,
        args: &[SExpr],
    ) -> Result<P::Term, BridgeError> {
        if args.len() != 2 {
            return Err(BridgeError::Malformed(format!(
                "{name}: expected 2 arguments"
            )));
        }
        let a = self.translate_term(&args[0])?;
        let b = self.translate_term(&args[1])?;
        Ok(self.prover.op2(op, a, b)?)
    }

    /// `(op a b)` translated as `(op' b a)` — used for `>=` ↦ `<=` and
    /// `>` ↦ `<` since the kernel only ships the lesser-than direction.
    fn swapped_binary_op2(
        &mut self,
        op: PrimOp2,
        name: &str,
        args: &[SExpr],
    ) -> Result<P::Term, BridgeError> {
        if args.len() != 2 {
            return Err(BridgeError::Malformed(format!(
                "{name}: expected 2 arguments"
            )));
        }
        let a = self.translate_term(&args[0])?;
        let b = self.translate_term(&args[1])?;
        Ok(self.prover.op2(op, b, a)?)
    }

    /// `(op a1 a2 ... an)` → `(((op a1 a2) a3) ... an)`. Used for n-ary
    /// `and`/`or`/`xor` (left-associative per SMT-LIB).
    fn left_fold_op2(&mut self, op: PrimOp2, args: &[SExpr]) -> Result<P::Term, BridgeError> {
        if args.len() < 2 {
            return Err(BridgeError::Malformed(
                "left_fold_op2: expected ≥ 2 arguments".into(),
            ));
        }
        let first = self.translate_term(&args[0])?;
        let second = self.translate_term(&args[1])?;
        let mut acc = self.prover.op2(op, first, second)?;
        for arg in &args[2..] {
            let next = self.translate_term(arg)?;
            acc = self.prover.op2(op, acc, next)?;
        }
        Ok(acc)
    }

    /// `(=> a1 a2 ... an)` → `(=> a1 (=> a2 (... (=> a_{n-1} an))))`.
    /// Right-associative per SMT-LIB.
    fn right_fold_op2(
        &mut self,
        op: PrimOp2,
        args: &[SExpr],
    ) -> Result<P::Term, BridgeError> {
        if args.len() < 2 {
            return Err(BridgeError::Malformed(
                "right_fold_op2: expected ≥ 2 arguments".into(),
            ));
        }
        let mut translated: Vec<P::Term> = Vec::with_capacity(args.len());
        for a in args {
            translated.push(self.translate_term(a)?);
        }
        let mut acc = *translated.last().expect("non-empty");
        for t in translated.iter().rev().skip(1) {
            acc = self.prover.op2(op, *t, acc)?;
        }
        Ok(acc)
    }

    /// `(! <term> :named @x [:other ...] ...)` — strip the annotation, bind
    /// `@x` → translated term in the named cache.
    fn translate_annotated(&mut self, rest: &[SExpr]) -> Result<P::Term, BridgeError> {
        let inner = rest
            .first()
            .ok_or_else(|| BridgeError::Malformed("!: missing term".into()))?;
        let translated = self.translate_term(inner)?;

        let mut i = 1;
        while i < rest.len() {
            if let Some(kw) = rest[i].as_symbol() {
                if kw == ":named" {
                    i += 1;
                    if let Some(name) = rest.get(i).and_then(|s| s.as_symbol()) {
                        self.named.insert(name.to_string(), translated);
                    } else {
                        return Err(BridgeError::Malformed(":named: missing name".into()));
                    }
                }
            }
            i += 1;
        }
        Ok(translated)
    }

    // ----------------------------------------------------------------
    // Rule handlers
    // ----------------------------------------------------------------
    //
    // Each handler takes the *already-resolved* clause + premise list and
    // returns a kernel-verified Thm. The bridge trait's `step` method
    // dispatches into here; rules not yet wired surface as
    // `BridgeError::NotImplemented`.

    /// `refl`: `Γ ⊢ (= t t)`. Alethe writes this as `(cl (= t t))`.
    fn rule_refl(&mut self, clause: &[SExpr]) -> Result<P::Thm, BridgeError> {
        if clause.len() != 1 {
            return Err(BridgeError::Malformed(
                "refl: expected unit clause `(cl (= t t))`".into(),
            ));
        }
        let eq_lit = clause[0]
            .as_list()
            .ok_or_else(|| BridgeError::Malformed("refl: clause head not a list".into()))?;
        if eq_lit.len() != 3 || eq_lit[0].as_symbol() != Some("=") {
            return Err(BridgeError::Malformed(
                "refl: clause must be `(= t t)`".into(),
            ));
        }
        let t = self.translate_term(&eq_lit[1])?;
        Ok(self.prover.refl(t)?)
    }

    /// `trans`: `Γ ⊢ (= t₀ t₁), Γ ⊢ (= t₁ t₂), …, Γ ⊢ (= t_{n-1} t_n)`
    /// ↦ `Γ ⊢ (= t₀ t_n)`. The premises are already a list of equality
    /// theorems; we chain them via `Prover::trans` left-to-right.
    fn rule_trans(
        &mut self,
        clause: &[SExpr],
        premises: &[P::Thm],
    ) -> Result<P::Thm, BridgeError> {
        if premises.is_empty() {
            return Err(BridgeError::Malformed(
                "trans: no premises".into(),
            ));
        }
        // Eagerly translate the clause so missing terms surface even though
        // the rule itself only needs the premise chain.
        if clause.len() != 1 {
            return Err(BridgeError::Malformed(
                "trans: expected unit clause".into(),
            ));
        }
        let mut acc = premises[0].clone();
        for prem in &premises[1..] {
            acc = self.prover.trans(acc, prem.clone())?;
        }
        Ok(acc)
    }
}

// =====================================================================
// AletheBridge impl
// =====================================================================

impl<'a, P: Prover> AletheBridge for KernelAletheBridge<'a, P> {
    type Thm = P::Thm;

    fn declare_sort(&mut self, name: &str, arity: u32) -> Result<(), BridgeError> {
        if arity != 0 {
            return Err(BridgeError::ParametricSort {
                name: name.to_string(),
                arity,
            });
        }
        let ty = self.prover.tyapp(name, &[])?;
        self.sorts.insert(name.to_string(), ty);
        Ok(())
    }

    fn declare_fun(
        &mut self,
        name: &str,
        params: &[SExpr],
        sort: &SExpr,
    ) -> Result<(), BridgeError> {
        let ty = self.function_type(params, sort)?;
        self.funs.insert(name.to_string(), ty);
        Ok(())
    }

    fn assert(&mut self, term: &SExpr) -> Result<(), BridgeError> {
        // Translate eagerly so any UnknownFun / NotImplemented surfaces
        // before we silently move past a malformed assertion. We don't yet
        // materialise the assertion as a hypothesis; the matching `(assume
        // ...)` in the proof will do that.
        let _ = self.translate_term(term)?;
        Ok(())
    }

    fn assume(&mut self, _id: &str, term: &SExpr) -> Result<P::Thm, BridgeError> {
        let t = self.translate_term(term)?;
        let prop = self.prover.push_assumption(t)?;
        Ok(self.prover.assume(prop)?)
    }

    fn step(
        &mut self,
        _id: &str,
        clause: &[SExpr],
        rule: &str,
        premises: &[P::Thm],
        _args: &[SExpr],
        _discharge: &[P::Thm],
    ) -> Result<P::Thm, BridgeError> {
        // Eagerly translate clause literals so syntactic errors surface
        // before we punt on the rule.
        for lit in clause {
            let _ = self.translate_term(lit)?;
        }
        if clause.is_empty() {
            self.derived_empty = true;
        }

        // Rule dispatch. As each rule gets wired up it moves out of the
        // catch-all and into its own arm; the unimplemented arms keep the
        // failure mode loud + structured.
        match rule {
            "refl" => self.rule_refl(clause),
            "trans" => self.rule_trans(clause, premises),
            other => Err(BridgeError::NotImplemented(format!("rule `{other}`"))),
        }
    }

    fn decision(&self) -> Decision {
        if self.derived_empty {
            Decision::Unsat
        } else {
            Decision::Unknown
        }
    }
}
