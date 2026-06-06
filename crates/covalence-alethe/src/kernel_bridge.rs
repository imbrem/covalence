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
    /// SMT function/constant symbol → (kernel type, cached const TermRef).
    ///
    /// The cached `P::Term` is what makes congruence work: the kernel doesn't
    /// hash-cons `alloc_term`, so re-calling `const_term("x", Int)` would
    /// produce a fresh `TermRef` each time. Caching the constant once at
    /// `declare_fun` and reusing it everywhere ensures `x` is *the same
    /// term* in every occurrence — required for UF-based congruence to fire.
    funs: HashMap<String, (P::Type, P::Term)>,
    /// Local variables in scope (innermost last). Each entry is
    /// `(smt-symbol, kernel type, cached free-var TermRef)`. Populated by
    /// quantifier translation and (future) anchor scopes.
    locals: Vec<(String, P::Type, P::Term)>,
    /// Cached integer literals: `n` → `int_lit(n)` term. Same hash-cons
    /// rationale as `funs`.
    int_lits: HashMap<i64, P::Term>,
    /// Cached `true` / `false`.
    cached_true: Option<P::Term>,
    cached_false: Option<P::Term>,
    /// Compound-term memos. The kernel doesn't hash-cons compound terms,
    /// so without these the same SExpr re-translates to a fresh `TermRef`
    /// each call — breaking later term-equality lookups (e.g. assertion →
    /// Prop matching).
    eq_memo: HashMap<(P::Term, P::Term), P::Term>,
    comb_memo: HashMap<(P::Term, P::Term), P::Term>,
    op1_memo: HashMap<(PrimOp1, P::Term), P::Term>,
    op2_memo: HashMap<(PrimOp2, P::Term, P::Term), P::Term>,
    /// `:named` bindings — `@name` → already-translated kernel term.
    named: HashMap<String, P::Term>,
    /// `(assert <term>)` results, in order: `(translated_term, prop)`. The
    /// proof's `(assume id <term>)` commands look up by translated term so
    /// every assume returns a Thm in the *same* (problem-level) context —
    /// avoiding `ContextMismatch` errors from `mp`/`trans` later.
    assertion_props: Vec<(P::Term, P::Prop)>,
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
            int_lits: HashMap::new(),
            cached_true: None,
            cached_false: None,
            eq_memo: HashMap::new(),
            comb_memo: HashMap::new(),
            op1_memo: HashMap::new(),
            op2_memo: HashMap::new(),
            named: HashMap::new(),
            assertion_props: Vec::new(),
            derived_empty: false,
        }
    }

    // ---- compound-term memoised constructors --------------------------

    fn mk_eq(&mut self, a: P::Term, b: P::Term) -> Result<P::Term, BridgeError> {
        if let Some(t) = self.eq_memo.get(&(a, b)).copied() {
            return Ok(t);
        }
        let t = self.prover.eq(a, b)?;
        self.eq_memo.insert((a, b), t);
        Ok(t)
    }

    fn mk_comb(&mut self, f: P::Term, x: P::Term) -> Result<P::Term, BridgeError> {
        if let Some(t) = self.comb_memo.get(&(f, x)).copied() {
            return Ok(t);
        }
        let t = self.prover.comb(f, x)?;
        self.comb_memo.insert((f, x), t);
        Ok(t)
    }

    fn mk_op1(&mut self, op: PrimOp1, x: P::Term) -> Result<P::Term, BridgeError> {
        if let Some(t) = self.op1_memo.get(&(op, x)).copied() {
            return Ok(t);
        }
        let t = self.prover.op1(op, x)?;
        self.op1_memo.insert((op, x), t);
        Ok(t)
    }

    fn mk_op2(
        &mut self,
        op: PrimOp2,
        a: P::Term,
        b: P::Term,
    ) -> Result<P::Term, BridgeError> {
        if let Some(t) = self.op2_memo.get(&(op, a, b)).copied() {
            return Ok(t);
        }
        let t = self.prover.op2(op, a, b)?;
        self.op2_memo.insert((op, a, b), t);
        Ok(t)
    }

    /// Borrow the underlying prover (e.g. for inspecting kernel state in tests).
    pub fn prover(&self) -> &P {
        self.prover
    }

    /// Look up a declared sort by SMT-LIB symbol.
    pub fn lookup_sort(&self, name: &str) -> Option<P::Type> {
        self.sorts.get(name).copied()
    }

    /// Look up a declared function/constant's *signature* by SMT-LIB symbol.
    pub fn lookup_fun(&self, name: &str) -> Option<P::Type> {
        self.funs.get(name).map(|(ty, _)| *ty)
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

        // Boolean literals — cached so every `true` / `false` occurrence
        // shares one TermRef.
        if sym == "true" {
            if let Some(t) = self.cached_true {
                return Ok(t);
            }
            let t = self.prover.truth()?;
            self.cached_true = Some(t);
            return Ok(t);
        }
        if sym == "false" {
            if let Some(t) = self.cached_false {
                return Ok(t);
            }
            let t = self.prover.falsity()?;
            self.cached_false = Some(t);
            return Ok(t);
        }

        // Numeric literals — cached.
        if let Ok(n) = sym.parse::<i64>() {
            if let Some(t) = self.int_lits.get(&n).copied() {
                return Ok(t);
            }
            let t = self.prover.int_lit(n)?;
            self.int_lits.insert(n, t);
            return Ok(t);
        }

        // Local variable (innermost-first); returns the cached free-var
        // TermRef from the scope frame.
        if let Some((_, _, term)) = self.locals.iter().rev().find(|(s, _, _)| s == sym) {
            return Ok(*term);
        }

        // Declared function / constant — return the cached const TermRef.
        if let Some((_, term)) = self.funs.get(sym).copied() {
            return Ok(term);
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
                Ok(self.mk_eq(lhs, rhs)?)
            }
            "!" => self.translate_annotated(rest),
            "not" => {
                if rest.len() != 1 {
                    return Err(BridgeError::Malformed("not: expected 1 argument".into()));
                }
                let p = self.translate_term(&rest[0])?;
                Ok(self.mk_op1(PrimOp1::LogicalNot, p)?)
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
                    Ok(self.mk_op1(PrimOp1::IntNeg, x)?)
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
                    acc = self.mk_comb(acc, a)?;
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
        Ok(self.mk_op2(op, a, b)?)
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
        Ok(self.mk_op2(op, b, a)?)
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
        let mut acc = self.mk_op2(op, first, second)?;
        for arg in &args[2..] {
            let next = self.translate_term(arg)?;
            acc = self.mk_op2(op, acc, next)?;
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
            acc = self.mk_op2(op, *t, acc)?;
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

    /// `refl`: `Γ ⊢ (= t t)`. Alethe writes this as `(cl (= t t))`. The
    /// clause literal may also be a `@named` reference to a previously
    /// constructed equality — translate via `translate_term` so the named
    /// cache path is exercised.
    fn rule_refl(&mut self, clause: &[SExpr]) -> Result<P::Thm, BridgeError> {
        if clause.len() != 1 {
            return Err(BridgeError::Malformed(
                "refl: expected unit clause".into(),
            ));
        }
        let lit = self.translate_term(&clause[0])?;
        let (lhs, _rhs) = self
            .prover
            .dest_eq(lit)
            .ok_or_else(|| BridgeError::Malformed("refl: literal is not an equality".into()))?;
        Ok(self.prover.refl(lhs)?)
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

    /// Alethe `cong`: congruence over function applications.
    ///
    /// `(step <id> (cl (= (op a_1 … a_n) (op b_1 … b_n))) :rule cong
    ///    :premises ((= a_{i_1} b_{i_1}) …))`
    ///
    /// Each premise is `Γ ⊢ (= a b)`. We inject the equality into the
    /// kernel's egraph union-find (untrusted from the kernel's POV but
    /// soundness-justified by the premise Thm itself — it's already
    /// verified), then ask the kernel to close `lhs = rhs` under congruence
    /// to the necessary depth.
    fn rule_cong(
        &mut self,
        clause: &[SExpr],
        premises: &[P::Thm],
    ) -> Result<P::Thm, BridgeError> {
        if clause.len() != 1 {
            return Err(BridgeError::Malformed(
                "cong: expected unit clause".into(),
            ));
        }

        // Process premises FIRST so the UF is populated before we materialise
        // the conclusion's lhs/rhs.
        for prem in premises {
            let concl = self.prover.conclusion(prem)?;
            let (a, b) = self.prover.dest_eq(concl).ok_or_else(|| {
                BridgeError::Malformed("cong: premise is not an equality".into())
            })?;
            self.prover.union(a, b)?;
        }

        let lit = self.translate_term(&clause[0])?;
        let (lhs, rhs) = self.prover.dest_eq(lit).ok_or_else(|| {
            BridgeError::Malformed("cong: conclusion is not an equality".into())
        })?;

        // Depth is the term tree depth at which we expect congruence to
        // match. For Alethe `cong` the conclusion is always a single
        // application layer over the premise-driven equalities; depth 32
        // is generously larger than anything cvc5 emits in practice.
        Ok(self.prover.cong(lhs, rhs, 32)?)
    }

    /// Alethe `hole`: a deliberately under-specified step. cvc5 uses it as
    /// a placeholder when it doesn't have a fine-grained Alethe rule — the
    /// `:args` carry a tag identifying what kind of trust is required.
    ///
    /// We currently accept exactly one variety: `TRUST_THEORY_REWRITE`,
    /// which always produces an equality `(= a b)`. We discharge it via
    /// the kernel's egraph: union `a` and `b` (the trust point), then
    /// close `a = b` via congruence at depth 0. Any other `hole` flavour
    /// punts with `NotImplemented` so the failure mode stays loud.
    fn rule_hole(
        &mut self,
        clause: &[SExpr],
        args: &[SExpr],
    ) -> Result<P::Thm, BridgeError> {
        // The tag arrives either as a string literal `"TRUST_THEORY_REWRITE"`
        // or (defensively) as a bare symbol.
        let tag = args
            .first()
            .and_then(|s| {
                s.as_str()
                    .and_then(|(_, bytes)| std::str::from_utf8(bytes).ok().map(str::to_string))
                    .or_else(|| s.as_symbol().map(str::to_string))
            })
            .ok_or_else(|| BridgeError::Malformed("hole: missing :args tag".into()))?;

        if tag != "TRUST_THEORY_REWRITE" {
            return Err(BridgeError::NotImplemented(format!(
                "hole variety `{tag}`"
            )));
        }

        if clause.len() != 1 {
            return Err(BridgeError::Malformed(
                "hole TRUST_THEORY_REWRITE: expected unit clause".into(),
            ));
        }
        // Route through translate_term so `(! (= a b) :named @x)` style
        // clauses are handled (annotation strip + name binding).
        let lit = self.translate_term(&clause[0])?;
        let (lhs, rhs) = self.prover.dest_eq(lit).ok_or_else(|| {
            BridgeError::Malformed("hole TRUST_THEORY_REWRITE: clause must be an equality".into())
        })?;
        // Trust point. Recorded but unproved.
        self.prover.union(lhs, rhs)?;
        Ok(self.prover.cong(lhs, rhs, 0)?)
    }

    // -----------------------------------------------------------------
    // Propositional-rule support
    // -----------------------------------------------------------------

    /// Translate a clause `(cl lit_1 lit_2 … lit_n)` into the equivalent
    /// disjunction term:
    ///
    ///   - empty clause → `False`
    ///   - single literal → the literal itself
    ///   - multiple literals → left-folded `Or(Or(lit_1, lit_2), lit_3)…`
    fn clause_to_disjunction(
        &mut self,
        clause: &[SExpr],
    ) -> Result<P::Term, BridgeError> {
        if clause.is_empty() {
            // Empty clause is False.
            // Cache via the bool-literal path so it shares a TermRef.
            if let Some(f) = self.cached_false {
                return Ok(f);
            }
            let f = self.prover.falsity()?;
            self.cached_false = Some(f);
            return Ok(f);
        }
        let first = self.translate_term(&clause[0])?;
        let mut acc = first;
        for lit in &clause[1..] {
            let t = self.translate_term(lit)?;
            acc = self.mk_op2(PrimOp2::LogicalOr, acc, t)?;
        }
        Ok(acc)
    }

    /// Any Alethe rule whose clause is a no-premise propositional
    /// tautology (`equiv_pos2`, `false`, `tautology`, `not_and`, …).
    /// Build the disjunction and discharge via `tautology_intro`.
    fn rule_propositional_tautology(
        &mut self,
        clause: &[SExpr],
    ) -> Result<P::Thm, BridgeError> {
        let disj = self.clause_to_disjunction(clause)?;
        Ok(self.prover.tautology_intro(disj)?)
    }

    /// Alethe `or`: from `Γ ⊢ (or l_1 … l_n)` derive `(cl l_1 … l_n)`.
    /// Semantically the same term; we just return the premise as-is after
    /// confirming arity.
    fn rule_or(
        &mut self,
        _clause: &[SExpr],
        premises: &[P::Thm],
    ) -> Result<P::Thm, BridgeError> {
        if premises.len() != 1 {
            return Err(BridgeError::Malformed(
                "or: expected exactly one premise".into(),
            ));
        }
        Ok(premises[0].clone())
    }

    /// Alethe `resolution` (and its `th_resolution` cousin).
    ///
    /// Premises are clauses-as-disjunctions; the conclusion is the
    /// propositional resolvent. Proof strategy:
    ///
    /// 1. Build the conclusion disjunction `R`.
    /// 2. Build the *curried* implication
    ///    `c_1 → c_2 → … → c_n → R` where `c_i` is `premises[i].conclusion`.
    /// 3. Discharge it via `tautology_intro` — propositional resolution is
    ///    a tautology under the truth-table semantics for `Or`/`Not`.
    /// 4. Chain `Prover::mp` with each premise to peel off the antecedents.
    fn rule_resolution(
        &mut self,
        clause: &[SExpr],
        premises: &[P::Thm],
    ) -> Result<P::Thm, BridgeError> {
        let result_disj = self.clause_to_disjunction(clause)?;

        // Gather premise conclusion terms (need them before borrowing the
        // prover mutably for the implication assembly).
        let mut premise_concls: Vec<P::Term> = Vec::with_capacity(premises.len());
        for prem in premises {
            premise_concls.push(self.prover.conclusion(prem)?);
        }

        // Build c_1 → c_2 → … → c_n → R from right to left.
        let mut implication = result_disj;
        for concl in premise_concls.iter().rev() {
            implication = self.mk_op2(PrimOp2::LogicalImp, *concl, implication)?;
        }

        let mut acc = self.prover.tautology_intro(implication)?;
        for prem in premises {
            acc = self.prover.mp(acc, prem.clone())?;
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
        // Pre-allocate the const term so every later `lookup_atom(name)`
        // returns the same TermRef. See the `funs` field doc.
        let term = self.prover.const_term(name, ty)?;
        self.funs.insert(name.to_string(), (ty, term));
        Ok(())
    }

    fn assert(&mut self, term: &SExpr) -> Result<(), BridgeError> {
        // Push every assertion onto the prover's context up-front so all
        // proof-level (assume id <term>) commands find their target Prop in
        // a *shared* context. This makes downstream mp / trans / resolution
        // calls context-compatible across all step Thms.
        let t = self.translate_term(term)?;
        let prop = self.prover.push_assumption(t)?;
        self.assertion_props.push((t, prop));
        Ok(())
    }

    fn assume(&mut self, _id: &str, term: &SExpr) -> Result<P::Thm, BridgeError> {
        let t = self.translate_term(term)?;
        // First try to match a pre-pushed assertion — keeps all step Thms
        // in the same context.
        if let Some((_, prop)) = self.assertion_props.iter().find(|(at, _)| *at == t) {
            return Ok(self.prover.assume(prop.clone())?);
        }
        // Otherwise (e.g. an anchor-introduced local hypothesis), push fresh.
        let prop = self.prover.push_assumption(t)?;
        Ok(self.prover.assume(prop)?)
    }

    fn step(
        &mut self,
        _id: &str,
        clause: &[SExpr],
        rule: &str,
        premises: &[P::Thm],
        args: &[SExpr],
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
            "cong" => self.rule_cong(clause, premises),
            "hole" => self.rule_hole(clause, args),
            // Propositional tautology rules — no premises (or premises already
            // dischargeable propositionally). All route through tautology_intro.
            "equiv_pos1" | "equiv_pos2" | "equiv_neg1" | "equiv_neg2" | "false"
            | "tautology" | "not_or" | "not_and" | "or_neg" | "and_pos"
            | "implies_pos" | "implies_neg1" | "implies_neg2" | "not_implies1"
            | "not_implies2" => self.rule_propositional_tautology(clause),
            "or" => self.rule_or(clause, premises),
            "resolution" | "th_resolution" => self.rule_resolution(clause, premises),
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
