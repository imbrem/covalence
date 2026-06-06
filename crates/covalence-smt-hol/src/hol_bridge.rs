//! `HolAletheBridge` — concrete `AletheBridge` impl over any `HolLightKernel`.
//!
//! This is the ONLY place that mentions kernel-specific types. The trait
//! surface stays stable; this impl is expected to churn alongside kernel
//! redesigns. Every Alethe rule that isn't wired through to the kernel
//! returns [`BridgeError::NotImplemented`] so the bridge compiles and parses
//! while individual rules are still in flight.

use std::collections::HashMap;

use covalence_hol::traits::HolLightKernel;
use covalence_hol::types::NameId;
use covalence_sexp::{SExp, SExpr};
use covalence_types::Decision;

use crate::bridge::AletheBridge;
use crate::error::BridgeError;
use crate::names::NameTable;

/// Bridge an Alethe proof into any `K: HolLightKernel`.
///
/// Owns:
///   - a mutable kernel borrow,
///   - a `NameTable` (well-known names pre-registered),
///   - the SMT-LIB sort + function environments,
///   - a stack of locally-bound variables (for future quantifier / anchor support),
///   - the running `Decision` (flipped to `Unsat` if a step derives the empty clause).
pub struct HolAletheBridge<'a, K: HolLightKernel> {
    kernel: &'a mut K,
    names: NameTable,
    /// SMT sort symbol → kernel type-constructor `NameId` (currently arity-0 only).
    sorts: HashMap<String, NameId>,
    /// SMT function/constant symbol → (`NameId`, kernel type).
    funs: HashMap<String, (NameId, K::Type)>,
    /// Local variables currently in scope (innermost last). Each entry is
    /// `(smt-symbol, kernel name, kernel type)`. Populated by quantifier
    /// translation and (future) `anchor` subproof scopes.
    locals: Vec<(String, NameId, K::Type)>,
    /// `:named` bindings — `@name` → already-translated kernel term.
    named: HashMap<String, K::Term>,
    /// Set once a step derives the empty clause `(cl)`.
    derived_empty: bool,
}

impl<'a, K: HolLightKernel> HolAletheBridge<'a, K> {
    /// Build a fresh bridge around a freshly-initialised kernel.
    ///
    /// The kernel is expected to have been constructed with the well-known
    /// IDs `FUN_TYCON_ID`/`BOOL_TYCON_ID`/`EQ_CONST_ID` (i.e. `HolKernel::new`).
    ///
    /// Registers the SMT-LIB Boolean connectives (`not`, `and`, `or`, `=>`,
    /// `xor`, `true`, `false`) as kernel constants with their standard types.
    /// These are unparameterised constants — no definitional content yet, just
    /// honest typing so translate_term can build well-formed terms.
    pub fn new(kernel: &'a mut K) -> Result<Self, BridgeError> {
        let mut this = HolAletheBridge {
            kernel,
            names: NameTable::new(),
            sorts: HashMap::new(),
            funs: HashMap::new(),
            locals: Vec::new(),
            named: HashMap::new(),
            derived_empty: false,
        };
        this.register_smt_builtins()?;
        Ok(this)
    }

    fn register_smt_builtins(&mut self) -> Result<(), BridgeError> {
        let bool_ty = self.kernel.bool_type();
        let bool_to_bool = self.kernel.fun_type(bool_ty, bool_ty);
        let bool_to_bool_to_bool = self.kernel.fun_type(bool_ty, bool_to_bool);

        // Nullary
        self.register_builtin("true", bool_ty)?;
        self.register_builtin("false", bool_ty)?;
        // Unary
        self.register_builtin("not", bool_to_bool)?;
        // Binary
        self.register_builtin("and", bool_to_bool_to_bool)?;
        self.register_builtin("or", bool_to_bool_to_bool)?;
        self.register_builtin("=>", bool_to_bool_to_bool)?;
        self.register_builtin("xor", bool_to_bool_to_bool)?;
        Ok(())
    }

    fn register_builtin(&mut self, name: &str, ty: K::Type) -> Result<(), BridgeError> {
        let id = self.names.intern_str(name);
        self.kernel.new_constant(id, ty)?;
        self.funs.insert(name.to_string(), (id, ty));
        Ok(())
    }

    /// Borrow the kernel (e.g. for printing or testing assertions).
    pub fn kernel(&self) -> &K {
        self.kernel
    }

    /// Borrow the name table (for resolving `NameId`s in tests).
    pub fn names(&self) -> &NameTable {
        &self.names
    }

    /// Look up a declared sort by its SMT-LIB symbol.
    pub fn lookup_sort(&self, name: &str) -> Option<NameId> {
        self.sorts.get(name).copied()
    }

    /// Look up a declared / built-in function symbol by its SMT-LIB symbol.
    pub fn lookup_fun(&self, name: &str) -> Option<(NameId, K::Type)> {
        self.funs.get(name).copied()
    }

    // ---------------------------------------------------------------
    // Sort translation
    // ---------------------------------------------------------------

    /// Translate an SMT-LIB sort S-expression into a kernel type.
    fn translate_sort(&mut self, sort: &SExpr) -> Result<K::Type, BridgeError> {
        match sort {
            SExp::Atom(_) => {
                let sym = sort
                    .as_symbol()
                    .ok_or_else(|| BridgeError::Malformed("sort: expected symbol".into()))?;
                if sym == "Bool" {
                    return Ok(self.kernel.bool_type());
                }
                let name = *self
                    .sorts
                    .get(sym)
                    .ok_or_else(|| BridgeError::UnknownSort(sym.to_string()))?;
                Ok(self.kernel.mk_tyapp(name, vec![]))
            }
            SExp::List(_) => Err(BridgeError::Malformed(
                "parametric sort applications not yet supported".into(),
            )),
        }
    }

    /// Build a curried function type `params -> ... -> result` from a list of
    /// SMT-LIB sorts.
    fn function_type(
        &mut self,
        params: &[SExpr],
        result: &SExpr,
    ) -> Result<K::Type, BridgeError> {
        let mut ty = self.translate_sort(result)?;
        for p in params.iter().rev() {
            let pty = self.translate_sort(p)?;
            ty = self.kernel.fun_type(pty, ty);
        }
        Ok(ty)
    }

    // ---------------------------------------------------------------
    // Term translation
    // ---------------------------------------------------------------

    /// Translate an SMT-LIB term S-expression into a kernel term.
    ///
    /// Currently supports:
    ///   - atomic constants from `declare-fun` / `declare-const`
    ///   - locally-bound variables (from quantifier / anchor scopes)
    ///   - `(= a b)` equality
    ///   - `(f a b ...)` curried application
    ///   - `(! term :named @x)` annotation passthrough (binds `@x` → translated term)
    ///   - `@x` named-term lookup
    ///
    /// Quantifiers, propositional connectives (`and`/`or`/`not`/`=>`), and
    /// theory-specific literals (`Int` / `Real` numerals, strings) are not
    /// yet handled — they return `NotImplemented` so the bridge fails loudly
    /// rather than silently producing wrong terms.
    fn translate_term(&mut self, term: &SExpr) -> Result<K::Term, BridgeError> {
        match term {
            SExp::Atom(_) => {
                let sym = term.as_symbol().ok_or_else(|| {
                    BridgeError::Malformed("term: non-symbol atom".into())
                })?;
                self.lookup_atom(sym)
            }
            SExp::List(items) => self.translate_app(items),
        }
    }

    fn lookup_atom(&mut self, sym: &str) -> Result<K::Term, BridgeError> {
        // Named-term reference: `@something`.
        if sym.starts_with('@') {
            return self
                .named
                .get(sym)
                .copied()
                .ok_or_else(|| BridgeError::UnknownFun(sym.to_string()));
        }

        // Local variable (innermost-first lookup).
        for (s, n, ty) in self.locals.iter().rev() {
            if s == sym {
                return Ok(self.kernel.mk_var(*n, *ty));
            }
        }

        // Declared function / constant.
        if let Some((n, ty)) = self.funs.get(sym).copied() {
            return Ok(self.kernel.mk_const(n, ty));
        }

        Err(BridgeError::UnknownFun(sym.to_string()))
    }

    fn translate_app(&mut self, items: &[SExpr]) -> Result<K::Term, BridgeError> {
        let head = items.first().ok_or_else(|| {
            BridgeError::Malformed("term: empty application".into())
        })?;
        let head_sym = head.as_symbol().ok_or_else(|| {
            BridgeError::Malformed("term: non-symbol head in application".into())
        })?;
        let rest = &items[1..];

        match head_sym {
            "=" => {
                if rest.len() != 2 {
                    return Err(BridgeError::Malformed(
                        "= : expected 2 arguments".into(),
                    ));
                }
                let lhs = self.translate_term(&rest[0])?;
                let rhs = self.translate_term(&rest[1])?;
                Ok(self.kernel.mk_eq(lhs, rhs))
            }
            "!" => self.translate_annotated(rest),
            // SMT-LIB allows n-ary `and`/`or` (n ≥ 2). Left-fold over the
            // pre-registered binary connective constant.
            "and" | "or" => {
                if rest.len() < 2 {
                    return Err(BridgeError::Malformed(format!(
                        "{head_sym}: expected ≥ 2 arguments"
                    )));
                }
                self.left_fold_app(head_sym, rest)
            }
            "ite" => Err(BridgeError::NotImplemented("ite".into())),
            "forall" | "exists" | "let" => Err(BridgeError::NotImplemented(format!(
                "binder `{head_sym}`"
            ))),
            _ => {
                // Curried application `(f a1 a2 ... an)` → `f a1 a2 ... an`.
                let f = self.lookup_atom(head_sym)?;
                let mut acc = f;
                for arg in rest {
                    let a = self.translate_term(arg)?;
                    acc = self.kernel.mk_comb(acc, a);
                }
                Ok(acc)
            }
        }
    }

    /// Translate `(op a1 a2 ... an)` for a *binary* op as the left-fold
    /// `(((op a1) a2) ... an)`. Used for n-ary `and` / `or`.
    fn left_fold_app(&mut self, op: &str, args: &[SExpr]) -> Result<K::Term, BridgeError> {
        let op_term = self.lookup_atom(op)?;
        let first = self.translate_term(&args[0])?;
        let mut acc = self.kernel.mk_comb(op_term, first);
        let mut i = 1;
        while i < args.len() {
            let next = self.translate_term(&args[i])?;
            // For each subsequent arg, re-apply op.
            if i == 1 {
                acc = self.kernel.mk_comb(acc, next);
            } else {
                let op_again = self.lookup_atom(op)?;
                let pair = self.kernel.mk_comb(op_again, next);
                acc = self.kernel.mk_comb(pair, acc);
            }
            i += 1;
        }
        Ok(acc)
    }

    /// `(! <term> :named @x [:other ...] ...)` — annotation passthrough.
    fn translate_annotated(&mut self, rest: &[SExpr]) -> Result<K::Term, BridgeError> {
        let inner = rest.first().ok_or_else(|| {
            BridgeError::Malformed("! : missing term".into())
        })?;
        let translated = self.translate_term(inner)?;

        // Scan for `:named @x` attribute.
        let mut i = 1;
        while i < rest.len() {
            if let Some(kw) = rest[i].as_symbol() {
                if kw == ":named" {
                    i += 1;
                    if let Some(name) = rest.get(i).and_then(|s| s.as_symbol()) {
                        self.named.insert(name.to_string(), translated);
                    } else {
                        return Err(BridgeError::Malformed(
                            ":named: missing name".into(),
                        ));
                    }
                }
            }
            i += 1;
        }
        Ok(translated)
    }
}

// =====================================================================
// AletheBridge impl
// =====================================================================

impl<'a, K: HolLightKernel> AletheBridge for HolAletheBridge<'a, K> {
    type Thm = K::Thm;

    fn declare_sort(&mut self, name: &str, arity: u32) -> Result<(), BridgeError> {
        if arity != 0 {
            return Err(BridgeError::ParametricSort {
                name: name.to_string(),
                arity,
            });
        }
        let id = self.names.intern_str(name);
        self.kernel.new_type(id, 0)?;
        self.sorts.insert(name.to_string(), id);
        Ok(())
    }

    fn declare_fun(
        &mut self,
        name: &str,
        params: &[SExpr],
        sort: &SExpr,
    ) -> Result<(), BridgeError> {
        let ty = self.function_type(params, sort)?;
        let id = self.names.intern_str(name);
        self.kernel.new_constant(id, ty)?;
        self.funs.insert(name.to_string(), (id, ty));
        Ok(())
    }

    fn assert(&mut self, term: &SExpr) -> Result<(), BridgeError> {
        // Translate so any UnknownFun / NotImplemented surfaces eagerly,
        // even though we don't yet materialise the assertion as a theorem.
        let _ = self.translate_term(term)?;
        Ok(())
    }

    fn assume(&mut self, _id: &str, term: &SExpr) -> Result<K::Thm, BridgeError> {
        let t = self.translate_term(term)?;
        Ok(self.kernel.assume_rule(t)?)
    }

    fn step(
        &mut self,
        _id: &str,
        clause: &[SExpr],
        rule: &str,
        _premises: &[K::Thm],
        _args: &[SExpr],
        _discharge: &[K::Thm],
    ) -> Result<K::Thm, BridgeError> {
        // Eagerly translate clause literals so syntactic errors surface
        // before we punt on the rule itself.
        for lit in clause {
            let _ = self.translate_term(lit)?;
        }
        if clause.is_empty() {
            self.derived_empty = true;
        }
        Err(BridgeError::NotImplemented(format!("rule `{rule}`")))
    }

    fn decision(&self) -> Decision {
        if self.derived_empty {
            Decision::Unsat
        } else {
            Decision::Unknown
        }
    }
}
