//! The Lisp **reduction relation as a [`Semantics`]** (`hol` feature).
//!
//! [`LispSemantics`] is the middle axis of the parametric reduction API: it
//! *is* the small-step reduction relation on carved `sexpr` operator terms.
//! Each [`step`](Semantics::step) finds the leftmost-innermost redex, applies
//! **one** computation law (a `proj_scons` / `consp` / `atom?` / `not`-fold
//! kernel theorem — the same laws the big-step the big-step evaluator
//! composed), and congruence-lifts it to a `⊢ term = term'` over the whole
//! term. [`compose`](Semantics::compose) is [`Thm::trans`], so a `drive` to a
//! normal form yields one composite `⊢ input = value`.
//!
//! A term is a **value** (normal form; `step` → `None`) when it is a carved
//! `sexpr` datum (`atom` / `snil` / `scons` chains) or a `bool` literal.
//!
//! Reduction runs over a **compiled program term**: [`LispSemantics::compile`]
//! lowers a parsed [`SExpr`] to the operator-application form (`quote` → data;
//! `car` / `cdr` / `cons` / `atom?` / `consp` → carved/Lisp operators applied
//! to compiled arguments; `null? E` → `¬ (consp E)`; `eq?` → a HOL equation at
//! `sexpr`; `if` / `cond` → the kernel `cond`; `lambda` → an abstraction; and a
//! call `(f args)` to a user [`defun`](crate::defs) → the def's free-variable
//! head applied to compiled args). This is the "data → operator application"
//! bridge the plain [`crate::Lisp::lower`] does not build.
//!
//! Two redexes are non-congruential:
//! - **`eq?`** on two atom values decides the HOL equation `atom b₁ = atom b₂`
//!   to `T`/`F` — the blob (dis)equality lifted through `atom` injectivity +
//!   congruence, a single self-contained step whose LHS *is* the redex, so it
//!   composes anywhere (not only at the top level).
//! - **`cond α c x y`** reduces only its condition `c` to a `bool` literal, then
//!   fires the selected `cond_true`/`cond_false` clause — the unselected branch
//!   is discarded, never reduced (the divergence guard for recursion).
//!
//! A **`defun` call** unfolds against the function's *assumed* equation
//! `{f = λ…} ⊢ f = λ…` (congruence to rewrite the head, then β), so the
//! `defun` equations ride the composite as **hypotheses** — sound recursion in
//! a total HOL without any new axiom. See [`crate::defs`].
//!
//! **Integers** (when an [`IntBackend`] is wired — the default): numerals in
//! expression position compile to kernel `int` literals, and `(+ a b)` /
//! `(- a b)` / `(* a b)` / `(<= a b)` / `(= a b)` compile to the kernel
//! `int.add` / `int.sub` / `int.mul` / `int.le` / `(=):int` operators applied
//! to the compiled operands — *typed kernel terms, no sexpr injection*. An
//! integer redex reduces its operands congruentially, then fires the
//! **kernel-proved** computation from [`IntBackend::prove_reduce`]
//! (`TermExt::reduce` underneath — never asserted), so integer results ride
//! the same `⊢ program = value` equations as everything else, hypothesis-free
//! for closed programs. Comparisons reduce to `bool` literals and print as
//! `t` / `nil`. The shared syntax preserves exact integers inside quoted data;
//! the current carved carrier can compile a top-level integer but still needs
//! a payload sum before it can embed integers inside S-expression structure.
//!
//! The value read off a normal form is always the RHS of a genuine kernel
//! theorem; nothing here mints new trusted rules.

use covalence_hol_eval::EvalThm as Thm;
use covalence_hol_eval::derived::DerivedRules;
use covalence_hol_eval::hol::hol_not;
use covalence_hol_eval::mk_blob;
use covalence_init::init::cond::{cond_false, cond_true};
use covalence_init::init::ext::{TermExt, ThmExt};
use covalence_init::init::inductive::carved::{CarvedSExpr, LeafKind, carved};
use covalence_init::init::lisp::{LeafArg, Lisp as KernelLisp, lisp};
use covalence_init::init::logic::simp;
use covalence_init::{Term, Type};
use covalence_kernel_lisp::{CoreExpr, Datum};

use std::sync::Arc;

use covalence_repl_core::{Repr, Semantics, StepCert};
use covalence_sexp::{Atom, SExpr};
use covalence_types::Int;

use covalence_sexp::abstract_sexpr::{AbstractSExpr, PayloadLit};

use crate::carrier::CarvedCarrier;
use crate::defs::Defs;
use crate::frontend::{CoreAtom, FrontendExpr, Primitive};
use crate::hol::HolError;
use crate::int_backend::{self, IntBackend, IntOp, IntVariant, NatVariant};

fn theory_err(e: impl core::fmt::Display) -> HolError {
    HolError::Theory(e.to_string())
}
fn kernel_err(e: impl core::fmt::Display) -> HolError {
    HolError::Kernel(e.to_string())
}

/// The value-kind of a normal form, for printing (mirrors the big-step
/// evaluator's `ValueKind`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ValueKind {
    /// A carved `sexpr` datum (`atom` / `snil` / `scons`).
    Data,
    /// A `bool` literal (a predicate / `eq?` / comparison result).
    Bool,
    /// A kernel `int` literal (an arithmetic result).
    Int,
}

// ============================================================================
// Repr — the kernel S-expression term encoding
// ============================================================================

/// The Lisp representation axis: reduction is over the kernel carved `sexpr`
/// operator [`Term`].
#[derive(Clone, Copy, Debug, Default)]
pub struct LispRepr;

impl Repr for LispRepr {
    type Term = Term;
}

// ============================================================================
// StepCert — one certified step
// ============================================================================

/// A single certified reduction step: the reduct term plus `⊢ from = to`.
#[derive(Clone, Debug)]
pub struct LispStep {
    to: Term,
    thm: Thm,
}

impl StepCert<LispRepr> for LispStep {
    type Thm = Thm;
    fn to(&self) -> &Term {
        &self.to
    }
    fn thm(&self) -> &Thm {
        &self.thm
    }
    fn into_parts(self) -> (Term, Thm) {
        (self.to, self.thm)
    }
}

// ============================================================================
// Semantics — THE small-step relation
// ============================================================================

/// The Lisp small-step reduction relation over the process-global carved +
/// Lisp theories, plus the session's user-`defun` dictionary
/// ([`Defs`]) — consulted to unfold `(f args)` calls against their assumed
/// equations (see [`crate::defs`]).
pub struct LispSemantics {
    cs: &'static CarvedSExpr,
    /// The shared abstract-sexpr adapter over `cs` (structural build/observe
    /// helpers — `as_scons`/`as_atom`/`is_snil`/`data` delegate here). Quote
    /// policy is `Sym`: numerals inside quoted data stay uninterpreted atoms
    /// even when the integer backend is on.
    carrier: CarvedCarrier,
    l: &'static KernelLisp,
    defs: Defs,
    /// The integer backend (`None` disables the integer forms entirely —
    /// numerals stay free variables and `+ - * <= =` stay user calls). The
    /// default constructors wire the signed [`IntVariant`].
    int: Option<Arc<dyn IntBackend + Send + Sync>>,
}

/// What a `t` / `nil` literal should compile to in a given position: a `bool`
/// literal (test / bool-valued branch) or a `sexpr` datum (data-valued branch).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Hint {
    /// Prefer a `bool` literal (`t` → `T`, `nil` → `F`).
    Bool,
    /// Prefer a `sexpr` datum (`t` → `atom t`, `nil` → `snil`).
    Data,
}

impl LispSemantics {
    /// Bind the process-global carved `sexpr` + Lisp theories, with no
    /// user definitions.
    pub fn new() -> Result<Self, HolError> {
        Self::with_defs(Defs::new())
    }

    /// Bind the theories with a user-`defun` dictionary — the calls in a
    /// compiled program unfold against these assumed equations. Integers are
    /// on (the signed [`IntVariant`] backend).
    pub fn with_defs(defs: Defs) -> Result<Self, HolError> {
        let cs = carved().map_err(theory_err)?;
        let (t, nil) = Self::truthiness(cs);
        let int: Arc<dyn IntBackend + Send + Sync> =
            Arc::new(IntVariant::new(cs.tau.clone(), t, nil));
        Self::with_defs_and_int(defs, Some(int))
    }

    /// [`with_defs`](Self::with_defs) with the **nat-restricted** integer
    /// backend ([`NatVariant`]): the same kernel computation, but negative
    /// results (e.g. `(- 2 5)`) are a clean error, never a value.
    pub fn with_defs_nat(defs: Defs) -> Result<Self, HolError> {
        let cs = carved().map_err(theory_err)?;
        let (t, nil) = Self::truthiness(cs);
        let int: Arc<dyn IntBackend + Send + Sync> =
            Arc::new(NatVariant::new(cs.tau.clone(), t, nil));
        Self::with_defs_and_int(defs, Some(int))
    }

    /// The fully-explicit constructor: a `defun` dictionary plus an optional
    /// [`IntBackend`] (`None` = the integer-free semantics — numerals stay
    /// free variables, the int ops stay ordinary user calls).
    pub fn with_defs_and_int(
        defs: Defs,
        int: Option<Arc<dyn IntBackend + Send + Sync>>,
    ) -> Result<Self, HolError> {
        let cs = carved().map_err(theory_err)?;
        Ok(LispSemantics {
            cs,
            carrier: CarvedCarrier::over(cs),
            l: lisp().map_err(theory_err)?,
            defs,
            int,
        })
    }

    /// The sexpr truthiness pair `(atom t, snil)` an [`IntBackend`] is
    /// constructed over (only its `prove_reduce` comparison path touches them;
    /// the value semantics reads comparison results off the `bool` equation).
    fn truthiness(cs: &'static CarvedSExpr) -> (Term, Term) {
        let t = Term::app(cs.atom.clone(), mk_blob(b"t".to_vec()));
        (t, cs.snil.clone())
    }

    /// The definition dictionary this semantics reduces against.
    pub fn defs(&self) -> &Defs {
        &self.defs
    }

    /// The `sexpr` carrier type.
    pub(crate) fn tau(&self) -> Type {
        self.cs.tau.clone()
    }

    /// Compile a parsed [`SExpr`] into the operator-application program term.
    /// A bare `t` / `nil` compiles as *data* by default (top level).
    pub fn compile(&self, e: &SExpr) -> Result<Term, HolError> {
        self.compile_h(e, Hint::Data)
    }

    /// Compile the stable backend-neutral Lisp core directly to HOL.
    ///
    /// Surface parsing and special-form validation happen in
    /// [`crate::frontend::Frontend`]. This is a proof-producing backend for
    /// that shared syntax; it does not execute through the host realization
    /// or round-trip through S-expression text.
    pub fn compile_core(&self, expression: &FrontendExpr) -> Result<Term, HolError> {
        self.compile_core_h(expression, Hint::Data)
    }

    fn compile_core_h(&self, expression: &FrontendExpr, hint: Hint) -> Result<Term, HolError> {
        use covalence_kernel_lisp::CoreExpr;
        match expression {
            CoreExpr::Literal(datum) | CoreExpr::Quote(datum) => {
                self.compile_core_datum(datum, hint)
            }
            CoreExpr::Truth(value) => Ok(match hint {
                Hint::Bool => covalence_hol_eval::mk_bool(*value),
                Hint::Data if *value => self.symbol_atom("t"),
                Hint::Data => self.cs.snil.clone(),
            }),
            CoreExpr::Variable(name) => Ok(Term::free(name, self.cs.tau.clone())),
            CoreExpr::If {
                condition,
                consequent,
                alternative,
            } => {
                let condition = self.compile_core_h(condition, Hint::Bool)?;
                self.compile_core_branches(condition, consequent, alternative)
            }
            CoreExpr::Cond { clauses } => self.compile_core_cond(clauses),
            CoreExpr::Sequence { .. } => {
                // TODO(cov:lisp.hol.strict-sequence, major): Model strict sequencing in a partial/effectful HOL semantics so divergence or failure in a discarded expression cannot be erased by pure equational compilation.
                Err(HolError::Stuck(
                    "strict sequencing needs the partial/effectful HOL semantics".into(),
                ))
            }
            CoreExpr::Lambda {
                parameters,
                rest,
                body,
                ..
            } => {
                if rest.is_some() {
                    // TODO(cov:lisp.hol.variadic-closures, major): Represent variadic closures in the equational HOL backend using the shared inductive proper-list carrier, without assuming total application.
                    return Err(HolError::Stuck(
                        "variadic closures need a proper-list application semantics".into(),
                    ));
                }
                let mut lambda = self.compile_core(body)?;
                for parameter in parameters.iter().rev() {
                    let closed = covalence_core::subst::close(&lambda, &parameter.name);
                    lambda = Term::abs(self.cs.tau.clone(), closed);
                }
                Ok(lambda)
            }
            CoreExpr::Apply {
                operator,
                arguments,
            } => {
                let mut term = match operator.as_ref() {
                    CoreExpr::Variable(name) => match self.defs.get(name) {
                        Some(definition) => definition.head.clone(),
                        None => Term::free(name, self.forward_head_ty(arguments.len())),
                    },
                    operator => self.compile_core(operator)?,
                };
                for argument in arguments {
                    term = Term::app(term, self.compile_core(argument)?);
                }
                Ok(term)
            }
            CoreExpr::ApplyList { .. } => {
                // TODO(cov:lisp.hol.apply-list, major): Give the partial HOL Lisp semantics higher-order closures and inductive proper-list argument splicing, then share apply conformance with the host backend.
                Err(HolError::Stuck(
                    "runtime-list application needs the partial higher-order HOL semantics".into(),
                ))
            }
            CoreExpr::Let { bindings, body } => {
                let lambda = CoreExpr::Lambda {
                    name: None,
                    parameters: bindings
                        .iter()
                        .map(|binding| covalence_kernel_lisp::Parameter::new(binding.name.clone()))
                        .collect(),
                    rest: None,
                    body: body.clone(),
                };
                self.compile_core(&CoreExpr::Apply {
                    operator: Box::new(lambda),
                    arguments: bindings
                        .iter()
                        .map(|binding| binding.value.clone())
                        .collect(),
                })
            }
            CoreExpr::LetRec { .. } => {
                // TODO(cov:lisp.scheme.letrec-hol, major): Give the equational HOL backend a conservative mutually recursive binding construction and share letrec conformance tests with the partial host semantics.
                Err(HolError::Stuck(
                    "mutually recursive lexical bindings are implemented by the common partial \
                     semantics but not yet by the equational HOL compiler"
                        .into(),
                ))
            }
            CoreExpr::Primitive {
                operator,
                arguments,
            } => self.compile_core_primitive(*operator, arguments),
        }
    }

    fn compile_core_datum(
        &self,
        datum: &covalence_kernel_lisp::Datum<CoreAtom>,
        hint: Hint,
    ) -> Result<Term, HolError> {
        use covalence_kernel_lisp::Datum;
        match datum {
            Datum::Nil => Ok(match hint {
                Hint::Bool => covalence_hol_eval::mk_bool(false),
                Hint::Data => self.cs.snil.clone(),
            }),
            Datum::Atom(CoreAtom::Symbol(symbol)) if symbol == b"t" && hint == Hint::Bool => {
                Ok(covalence_hol_eval::mk_bool(true))
            }
            Datum::Atom(CoreAtom::Symbol(symbol)) => self.carrier.atom(PayloadLit::Sym(symbol)),
            Datum::Atom(CoreAtom::String { bytes, .. }) => {
                self.carrier.atom(PayloadLit::Sym(bytes))
            }
            Datum::Atom(CoreAtom::Integer(integer)) => {
                if hint == Hint::Bool {
                    return Err(HolError::Stuck(
                        "integer used where a boolean condition is required".into(),
                    ));
                }
                Ok(covalence_hol_eval::mk_int(integer.clone()))
            }
            Datum::Cons(head, tail) => {
                let head = self.compile_core_datum(head, Hint::Data)?;
                let tail = self.compile_core_datum(tail, Hint::Data)?;
                Ok(Term::app(Term::app(self.cs.scons.clone(), head), tail))
            }
        }
    }

    fn compile_core_branches(
        &self,
        condition: Term,
        consequent: &FrontendExpr,
        alternative: &FrontendExpr,
    ) -> Result<Term, HolError> {
        let consequent_data = self.compile_core_h(consequent, Hint::Data)?;
        let alternative_data = self.compile_core_h(alternative, Hint::Data)?;
        let consequent_ty = consequent_data.type_of().map_err(kernel_err)?;
        let alternative_ty = alternative_data.type_of().map_err(kernel_err)?;
        let (consequent, alternative, alpha) = if consequent_ty == alternative_ty {
            (consequent_data, alternative_data, consequent_ty)
        } else {
            let consequent_bool = self.compile_core_h(consequent, Hint::Bool)?;
            let alternative_bool = self.compile_core_h(alternative, Hint::Bool)?;
            if consequent_bool.type_of().map_err(kernel_err)? != Type::bool()
                || alternative_bool.type_of().map_err(kernel_err)? != Type::bool()
            {
                return Err(HolError::Stuck(
                    "conditional branches have incompatible types".into(),
                ));
            }
            (consequent_bool, alternative_bool, Type::bool())
        };
        let default = if alpha == Type::bool() {
            covalence_hol_eval::mk_bool(false)
        } else if alpha == Type::int() {
            covalence_hol_eval::mk_int(Int::zero())
        } else {
            self.cs.snil.clone()
        };
        let fallback = self.mk_cond(
            &alpha,
            covalence_hol_eval::mk_bool(true),
            alternative,
            default,
        )?;
        self.mk_cond(&alpha, condition, consequent, fallback)
    }

    fn compile_core_cond(
        &self,
        clauses: &[(FrontendExpr, FrontendExpr)],
    ) -> Result<Term, HolError> {
        let alpha = clauses
            .iter()
            .filter(|(_, branch)| !matches!(branch, covalence_kernel_lisp::CoreExpr::Truth(_)))
            .map(|(_, branch)| {
                self.compile_core_h(branch, Hint::Data)
                    .and_then(|term| term.type_of().map_err(kernel_err))
            })
            .next()
            .transpose()?
            .unwrap_or_else(|| self.cs.tau.clone());
        let hint = if alpha == Type::bool() {
            Hint::Bool
        } else {
            Hint::Data
        };
        let mut result = if alpha == Type::bool() {
            covalence_hol_eval::mk_bool(false)
        } else if alpha == Type::int() {
            covalence_hol_eval::mk_int(Int::zero())
        } else {
            self.cs.snil.clone()
        };
        for (condition, branch) in clauses.iter().rev() {
            let condition = self.compile_core_h(condition, Hint::Bool)?;
            let branch = self.compile_core_h(branch, hint)?;
            if branch.type_of().map_err(kernel_err)? != alpha {
                return Err(HolError::Stuck(
                    "cond branches have incompatible types".into(),
                ));
            }
            result = self.mk_cond(&alpha, condition, branch, result)?;
        }
        Ok(result)
    }

    fn compile_core_primitive(
        &self,
        primitive: Primitive,
        arguments: &[FrontendExpr],
    ) -> Result<Term, HolError> {
        let require_arity = |expected: usize| {
            if arguments.len() == expected {
                Ok(())
            } else {
                Err(HolError::Stuck(format!(
                    "{primitive:?} expects {expected} arguments (got {})",
                    arguments.len()
                )))
            }
        };
        match primitive {
            Primitive::Cons => {
                require_arity(2)?;
                Ok(Term::app(
                    Term::app(self.cs.scons.clone(), self.compile_core(&arguments[0])?),
                    self.compile_core(&arguments[1])?,
                ))
            }
            Primitive::Car | Primitive::Cdr => {
                require_arity(1)?;
                let operator = if primitive == Primitive::Car {
                    self.cs.car.clone()
                } else {
                    self.cs.cdr.clone()
                };
                Ok(Term::app(operator, self.compile_core(&arguments[0])?))
            }
            Primitive::Atom | Primitive::Consp | Primitive::Null => {
                require_arity(1)?;
                let argument = self.compile_core(&arguments[0])?;
                if primitive == Primitive::Null {
                    Ok(hol_not(Term::app(self.l.consp.clone(), argument)))
                } else {
                    let operator = if primitive == Primitive::Atom {
                        self.l.atom_p.clone()
                    } else {
                        self.l.consp.clone()
                    };
                    Ok(Term::app(operator, argument))
                }
            }
            Primitive::Integer => {
                // TODO(cov:lisp.hol.numeric-datum-sum, major): Give the proof-producing S-expression carrier a payload sum containing exact integers, then implement `integer?` uniformly for open terms and nested quoted data.
                let [argument] = arguments else {
                    return Err(HolError::Stuck(format!(
                        "{primitive:?} expects 1 argument (got {})",
                        arguments.len()
                    )));
                };
                match argument {
                    CoreExpr::Literal(Datum::Atom(CoreAtom::Integer(_)))
                    | CoreExpr::Quote(Datum::Atom(CoreAtom::Integer(_))) => {
                        Ok(covalence_hol_eval::mk_bool(true))
                    }
                    CoreExpr::Literal(_) | CoreExpr::Quote(_) | CoreExpr::Truth(_) => {
                        Ok(covalence_hol_eval::mk_bool(false))
                    }
                    _ => Err(HolError::Stuck(
                        "`integer?` over an open value requires the numeric S-expression payload \
                         sum backend"
                            .into(),
                    )),
                }
            }
            Primitive::Equal => {
                require_arity(2)?;
                let left = self.compile_core(&arguments[0])?;
                let right = self.compile_core(&arguments[1])?;
                let ty = left.type_of().map_err(kernel_err)?;
                if right.type_of().map_err(kernel_err)? != ty {
                    return Err(HolError::Stuck(
                        "equality operands have incompatible types".into(),
                    ));
                }
                Ok(Term::app(Term::app(Term::eq_op(ty), left), right))
            }
            Primitive::Append => {
                require_arity(2)?;
                let left = self.compile_core(&arguments[0])?;
                let right = self.compile_core(&arguments[1])?;
                self.l
                    .append
                    .clone()
                    .apply(left)
                    .map_err(kernel_err)?
                    .apply(right)
                    .map_err(kernel_err)
            }
            Primitive::Add | Primitive::Subtract | Primitive::Multiply | Primitive::LessEqual => {
                require_arity(2)?;
                let operation = match primitive {
                    Primitive::Add => IntOp::Add,
                    Primitive::Subtract => IntOp::Sub,
                    Primitive::Multiply => IntOp::Mul,
                    Primitive::LessEqual => IntOp::Le,
                    _ => unreachable!(),
                };
                let left = self.compile_core(&arguments[0])?;
                let right = self.compile_core(&arguments[1])?;
                int_backend::kernel_redex(operation, &left, &right)
                    .map_err(|_| HolError::Stuck(format!("{primitive:?} expects integer operands")))
            }
        }
    }

    fn compile_h(&self, e: &SExpr, hint: Hint) -> Result<Term, HolError> {
        match e {
            SExpr::Atom(a) => self.atom_or_var(a, hint),
            SExpr::List(items) => self.compile_form(items),
        }
    }

    /// An atom in operand position: a `t`/`nil` literal (per `hint`), an
    /// in-scope user variable / function-as-value (a free var from a `defun`),
    /// or a bare symbol datum.
    fn atom_or_var(&self, a: &Atom, hint: Hint) -> Result<Term, HolError> {
        if let Atom::Symbol(s) = a {
            match s.as_str() {
                "t" => {
                    return Ok(match hint {
                        Hint::Bool => covalence_hol_eval::mk_bool(true),
                        Hint::Data => self.symbol_atom("t"),
                    });
                }
                "nil" => {
                    return Ok(match hint {
                        Hint::Bool => covalence_hol_eval::mk_bool(false),
                        Hint::Data => self.cs.snil.clone(),
                    });
                }
                // A numeral (integers on) compiles to a kernel `int` literal —
                // in *expression* position only (`quote`d numerals stay atoms).
                other => {
                    if self.int.is_some()
                        && let Ok(n) = other.parse::<Int>()
                    {
                        return Ok(covalence_hol_eval::mk_int(n));
                    }
                    // A parameter / bound variable of a surrounding `defun` /
                    // `lambda` compiles to a `sexpr`-typed free variable.
                    return Ok(Term::free(other, self.cs.tau.clone()));
                }
            }
        }
        self.atom_data(a)
    }

    fn symbol_atom(&self, s: &str) -> Term {
        Term::app(self.cs.atom.clone(), mk_blob(s.as_bytes().to_vec()))
    }

    /// A `sexpr` atom datum for the symbol `s` — the public [`symbol_atom`]
    /// (used by the session to build definition-ack values).
    ///
    /// [`symbol_atom`]: Self::symbol_atom
    pub fn symbol_value(&self, s: &str) -> Term {
        self.symbol_atom(s)
    }

    /// The empty-list datum `snil : sexpr`.
    pub fn tau_nil(&self) -> Term {
        self.cs.snil.clone()
    }

    fn compile_form(&self, items: &[SExpr]) -> Result<Term, HolError> {
        let (head, args) = items
            .split_first()
            .ok_or_else(|| HolError::Stuck("cannot evaluate the empty form `()`".into()))?;
        // A `((lambda …) …)` application: the head is itself a form.
        if let SExpr::List(_) = head {
            return self.compile_app(head, args);
        }
        let op = head
            .as_symbol()
            .ok_or_else(|| HolError::Stuck("application head is not a symbol".into()))?;
        match (op, args.len()) {
            // `quote` is the special form: its argument is *data*.
            ("quote", 1) => self.data(&args[0]),
            ("car", 1) => Ok(Term::app(self.cs.car.clone(), self.compile(&args[0])?)),
            ("cdr", 1) => Ok(Term::app(self.cs.cdr.clone(), self.compile(&args[0])?)),
            ("cons", 2) => {
                let h = self.compile(&args[0])?;
                let t = self.compile(&args[1])?;
                Ok(Term::app(Term::app(self.cs.scons.clone(), h), t))
            }
            ("atom?" | "atom", 1) => Ok(Term::app(self.l.atom_p.clone(), self.compile(&args[0])?)),
            ("consp" | "pair?", 1) => Ok(Term::app(self.l.consp.clone(), self.compile(&args[0])?)),
            // `null? E` compiles to `¬ (consp E)` — congruential: `consp v`
            // fires to a literal, then `¬ literal` folds via `simp`.
            ("null?" | "null", 1) => Ok(hol_not(Term::app(
                self.l.consp.clone(),
                self.compile(&args[0])?,
            ))),
            // `eq?` compiles to the **real HOL equation** `a = b : bool` at
            // element type `sexpr`. It is congruential (operands reduce to atom
            // values first); once both are atoms, the leaf step
            // ([`eval_eq_leaf`]) decides it to `T`/`F`.
            ("eq?" | "eq", 2) => {
                let a = self.compile(&args[0])?;
                let b = self.compile(&args[1])?;
                Ok(Term::app(Term::app(Term::eq_op(self.cs.tau.clone()), a), b))
            }
            // `if` — sugar for a two-clause `cond`.
            ("if", 3) => self.compile_cond_clauses(&[
                (self.compile_h(&args[0], Hint::Bool)?, &args[1]),
                (covalence_hol_eval::mk_bool(true), &args[2]),
            ]),
            // `cond` — a chain of `(test branch)` clauses.
            ("cond", _) => self.compile_cond(args),
            // `lambda` — an anonymous abstraction (β-reducible when applied).
            ("lambda", 2) => self.compile_lambda(&args[0], &args[1]),
            // The integer operators `+ - * <= =` (integers on) compile to the
            // **kernel** int operators applied to the compiled operands —
            // `int.add a b` etc., a typed kernel redex whose reduction is the
            // kernel-proved computation equation (see `step_int`).
            (sym, n) if self.int.is_some() && IntOp::from_symbol(sym).is_some() => {
                let op = IntOp::from_symbol(sym).expect("guard");
                if n != 2 {
                    return Err(HolError::Stuck(format!(
                        "`{sym}` expects 2 arguments (got {n})"
                    )));
                }
                let a = self.compile(&args[0])?;
                let b = self.compile(&args[1])?;
                // `kernel_redex` type-checks the application, so a non-`int`
                // operand (e.g. `(+ (car '(a)) 1)`) fails HERE — surface the
                // *surface* form, not the kernel's type-mismatch jargon.
                int_backend::kernel_redex(op, &a, &b).map_err(|_| {
                    HolError::Stuck(format!(
                        "`{sym}` expects integer operands in `({sym} {} {})`",
                        surface(&args[0]),
                        surface(&args[1])
                    ))
                })
            }
            // A call to a user-defined function `f` (an assumed `defun`), or a
            // **forward reference** to one not yet defined — mutual recursion in
            // the metacircular interpreter needs this. Either way it compiles to
            // a free-variable head (the def's, if present; else a fresh
            // `sexpr… → sexpr` head that a later `defun` will match by
            // name+type). Reserved special-form / builtin names are excluded so
            // a misspelled primitive is still an error.
            (name, n) if !is_reserved(name) => self.compile_user_call(name, args, n),
            (other, n) => Err(HolError::Stuck(format!(
                "unknown or misapplied operator `{other}` (arity {n})"
            ))),
        }
    }

    /// Compile a `lambda` `(lambda (p₁ … pₙ) body)` into `λp₁ … pₙ. body`.
    fn compile_lambda(&self, params: &SExpr, body: &SExpr) -> Result<Term, HolError> {
        let ps = self.param_names(params)?;
        let mut lam = self.compile(body)?;
        for p in ps.iter().rev() {
            let closed = covalence_core::subst::close(&lam, p);
            lam = Term::abs(self.cs.tau.clone(), closed);
        }
        Ok(lam)
    }

    /// Compile an application whose head is itself a form (e.g. a `lambda`):
    /// `(head a₁ … aₙ)` → `App(… App(head, a₁) …, aₙ)`.
    fn compile_app(&self, head: &SExpr, args: &[SExpr]) -> Result<Term, HolError> {
        let mut t = self.compile(head)?;
        for a in args {
            t = Term::app(t, self.compile(a)?);
        }
        Ok(t)
    }

    /// Compile a call to a user-defined function `name` applied to `args`. Uses
    /// the def's stored head if present; otherwise (a forward reference)
    /// synthesizes a `sexpr… → sexpr` free-variable head — a later `defun` of
    /// `name` with the same signature installs the matching assumption, and the
    /// unfold then fires by name+type.
    fn compile_user_call(
        &self,
        name: &str,
        args: &[SExpr],
        arity: usize,
    ) -> Result<Term, HolError> {
        let head = match self.defs.get(name) {
            Some(def) => def.head.clone(),
            None => Term::free(name, self.forward_head_ty(arity)),
        };
        let mut t = head;
        for a in args {
            t = Term::app(t, self.compile(a)?);
        }
        Ok(t)
    }

    /// `sexpr → … → sexpr` (`arity` arrows) — the default type of a
    /// forward-referenced function's head.
    fn forward_head_ty(&self, arity: usize) -> Type {
        let mut ty = self.cs.tau.clone();
        for _ in 0..arity {
            ty = Type::fun(self.cs.tau.clone(), ty);
        }
        ty
    }

    /// Compile a `cond` from its `(test branch)` clause list.
    fn compile_cond(&self, clauses: &[SExpr]) -> Result<Term, HolError> {
        let mut parsed: Vec<(Term, &SExpr)> = Vec::with_capacity(clauses.len());
        for c in clauses {
            let SExpr::List(items) = c else {
                return Err(HolError::Stuck("cond clause is not a list".into()));
            };
            if items.len() != 2 {
                return Err(HolError::Stuck("cond clause must be (test branch)".into()));
            }
            let test = self.compile_h(&items[0], Hint::Bool)?;
            parsed.push((test, &items[1]));
        }
        self.compile_cond_clauses(&parsed)
    }

    /// Build the nested `cond τ` term from compiled `(test, branch-expr)`
    /// clauses. The branch element type `α` is inferred from the first branch
    /// that is not a bare `t`/`nil`; bare `t`/`nil` branches then compile to
    /// that type (bool → `T`/`F`, data → `atom t`/`snil`).
    fn compile_cond_clauses(&self, clauses: &[(Term, &SExpr)]) -> Result<Term, HolError> {
        // Infer α from the first non-`t`/`nil` branch (default: data).
        let mut alpha: Option<Type> = None;
        for (_, e) in clauses {
            if !is_bare_bool_lit(e) {
                let probe = self.compile_h(e, Hint::Data)?;
                alpha = Some(probe.type_of().map_err(kernel_err)?);
                break;
            }
        }
        let alpha = alpha.unwrap_or_else(|| self.cs.tau.clone());
        let hint = if alpha == Type::bool() {
            Hint::Bool
        } else {
            Hint::Data
        };
        // Default (no clause matched): `nil` in the inferred type — `F` at
        // `bool`, the literal `0` at `int`, `snil` at `sexpr`.
        let mut acc = if alpha == Type::bool() {
            covalence_hol_eval::mk_bool(false)
        } else if alpha == Type::int() {
            covalence_hol_eval::mk_int(Int::from(0i128))
        } else {
            self.cs.snil.clone()
        };
        for (test, e) in clauses.iter().rev() {
            let branch = self.compile_h(e, hint)?;
            acc = self.mk_cond(&alpha, test.clone(), branch, acc)?;
        }
        Ok(acc)
    }

    /// `cond α c x y` from the kernel `cond` operator at element type `α`.
    fn mk_cond(&self, alpha: &Type, c: Term, x: Term, y: Term) -> Result<Term, HolError> {
        let op = covalence_hol_eval::defs::cond(alpha.clone());
        Ok(Term::app(Term::app(Term::app(op, c), x), y))
    }

    /// The parameter names of a `(p₁ … pₙ)` formal list.
    fn param_names(&self, params: &SExpr) -> Result<Vec<String>, HolError> {
        let SExpr::List(items) = params else {
            return Err(HolError::Stuck("parameter list is not a list".into()));
        };
        items
            .iter()
            .map(|p| {
                p.as_symbol()
                    .map(str::to_string)
                    .ok_or_else(|| HolError::Stuck("parameter is not a symbol".into()))
            })
            .collect()
    }

    // ---- data compilation (the `quote` payload) -------------------------

    fn data(&self, e: &SExpr) -> Result<Term, HolError> {
        // The carrier's `quote` fold (numerals-in-data stay symbol atoms —
        // the quote policy is `Sym` regardless of the integer backend).
        self.carrier.quote(e)
    }

    fn atom_data(&self, a: &Atom) -> Result<Term, HolError> {
        let bytes: &[u8] = match a {
            Atom::Symbol(s) => s.as_bytes(),
            Atom::Str { bytes, .. } => bytes,
        };
        self.carrier.atom(PayloadLit::Sym(bytes))
    }

    // ---- value classification -------------------------------------------

    /// The value-kind of a normal form, or `None` if `t` is not a value.
    pub fn value_kind(&self, t: &Term) -> Option<ValueKind> {
        if self.is_data_value(t) {
            Some(ValueKind::Data)
        } else if t.as_bool().is_some() {
            Some(ValueKind::Bool)
        } else if covalence_hol_eval::as_int(t).is_some() {
            Some(ValueKind::Int)
        } else {
            None
        }
    }

    /// Is `t` a fully-evaluated `sexpr` datum (`atom` / `snil` / `scons` chain)?
    fn is_data_value(&self, t: &Term) -> bool {
        if *t == self.cs.snil {
            return true;
        }
        if self.as_atom(t).is_some() {
            return true;
        }
        if let Some((h, tl)) = self.as_scons(t) {
            return self.is_data_value(&h) && self.is_data_value(&tl);
        }
        false
    }

    // ---- the redex reducer (one leftmost-innermost step) ----------------

    /// Reduce the leftmost-innermost redex of `t` by **one** law, returning
    /// `⊢ t = t'` congruence-lifted, or `None` if `t` is a value.
    fn step_term(&self, t: &Term) -> Result<Option<LispStep>, HolError> {
        if self.value_kind(t).is_some() {
            return Ok(None);
        }
        // A `cond α c x y` — reduce ONLY the condition, then select a branch.
        // Handled before the generic congruence so the *unselected* branch is
        // never reduced (call-by-name on the branches; the divergence guard for
        // recursive definitions).
        if let Some((alpha, c, x, y)) = self.as_cond(t) {
            return self.step_cond(&alpha, &c, &x, &y).map(Some);
        }
        // An `eq?` redex `a = b : sexpr` whose operands are **both atom
        // values** — decide it to `T`/`F` (a self-contained leaf step). If the
        // operands are not yet values, fall through to the generic congruence,
        // which reduces them first.
        if let Some((a, b)) = self.as_eq_redex(t)
            && self.as_atom(&a).is_some()
            && self.as_atom(&b).is_some()
        {
            return self.eval_eq_leaf(&a, &b).map(Some);
        }
        if let Some((left, right)) = self.as_append_redex(t) {
            return self.step_append(t, &left, &right).map(Some);
        }
        // `not p` — a unary spine on the `not` head.
        if let Some(p) = self.as_not(t) {
            return self.step_not(t, &p);
        }
        // An integer-op redex `int.<op> a b` (integers on) — reduce the
        // operands to `int` literals (congruence), then fire the
        // kernel-proved computation. Handled before the generic congruence:
        // the partial spine `int.<op> a` is not itself reducible, so the
        // whole redex steps at once (like a user-call spine).
        if let Some((op, a, b)) = self.as_int_redex(t) {
            return self.step_int(t, op, &a, &b).map(Some);
        }
        // General application: `App(f, arg)`.
        let Some((f, arg)) = t.as_app() else {
            if let Some(v) = t.as_free() {
                return Err(HolError::Stuck(format!("unbound variable `{}`", v.name())));
            }
            return Err(HolError::Stuck(format!("no reduction for `{t}`")));
        };
        // 1. Reduce inside the argument (innermost).
        if let Some(inner) = self.step_term(arg)? {
            let lifted = inner.thm.clone().cong_arg(f.clone()).map_err(kernel_err)?;
            let to = Term::app(f.clone(), inner.to.clone());
            return Ok(Some(LispStep { to, thm: lifted }));
        }
        // 2. Reduce inside the function position ONLY when it is itself an
        //    application (a curried spine, e.g. `App(scons, h)` in a `cons`); a
        //    bare operator head (`car`/`cdr`/`consp`/`atom_p`) is irreducible
        //    and is handled by `fire` below. A **partial user-call spine**
        //    (`App(f, a)` with `f` a `defun` head) is NOT reduced here — it is
        //    fired whole by `fire` once the outer application supplies the last
        //    argument, so recursing would strand it at the wrong arity.
        if f.as_app().is_some()
            && !self.is_user_spine(f)
            && let Some(inner) = self.step_term(f)?
        {
            let lifted = inner.thm.clone().cong_fn(arg.clone()).map_err(kernel_err)?;
            let to = Term::app(inner.to.clone(), arg.clone());
            return Ok(Some(LispStep { to, thm: lifted }));
        }
        // 3. Redex head with value sub-terms — fire the law.
        self.fire(t, f, arg)
    }

    /// Is `t`'s application-spine head a user `defun` free variable? Such a
    /// spine must be fired whole (at full arity) by [`fire`], not reduced
    /// piecewise in the function position.
    fn is_user_spine(&self, t: &Term) -> bool {
        let (head, _) = unwind_app(t);
        head.as_free()
            .map(|v| self.defs.contains(v.name()))
            .unwrap_or(false)
    }

    /// Fire the head computation law of a redex `t = App(f, v)` whose argument
    /// `v` is a value and whose head `f` is a value/operator.
    fn fire(&self, t: &Term, f: &Term, v: &Term) -> Result<Option<LispStep>, HolError> {
        if *f == self.cs.car {
            return self.fire_proj(t, false, v).map(Some);
        }
        if *f == self.cs.cdr {
            return self.fire_proj(t, true, v).map(Some);
        }
        if *f == self.l.atom_p {
            return self.fire_pred(t, Pred::Atom, v).map(Some);
        }
        if *f == self.l.consp {
            return self.fire_pred(t, Pred::Consp, v).map(Some);
        }
        // A β-redex `(λ. body) v` — fire one β step.
        if f.as_abs().is_some() {
            return self.fire_beta(t).map(Some);
        }
        // A fully-applied user-defined function `(g a₁ … aₙ)` whose spine head
        // is a `defun` free variable — unfold against its assumed equation,
        // then β-reduce the arguments in.
        if let Some(step) = self.try_unfold_user_call(t)? {
            return Ok(Some(step));
        }
        Err(HolError::Stuck(format!("no reduction for `{t}`")))
    }

    /// One β-contraction of a redex `(λ:τ. body) v` — the kernel
    /// [`Thm::beta_conv`] equation, packaged as a step.
    fn fire_beta(&self, redex: &Term) -> Result<LispStep, HolError> {
        let thm = Thm::beta_conv(redex.clone()).map_err(kernel_err)?;
        let to = self.rhs(&thm)?;
        Ok(LispStep { to, thm })
    }

    /// If `t`'s application spine head is a user `defun` free variable applied
    /// to exactly its arity of (value) arguments, unfold it: rewrite the head
    /// against the assumed equation `f = λparams. body` (congruence), then
    /// β-reduce each argument. Returns the composite `{f=λ} ⊢ (f a…) = body[a…]`.
    fn try_unfold_user_call(&self, t: &Term) -> Result<Option<LispStep>, HolError> {
        // Unwind the spine `((f a₁) a₂) … aₙ`.
        let (head, args) = unwind_app(t);
        let Some(var) = head.as_free() else {
            return Ok(None);
        };
        let Some(def) = self.defs.get(var.name()) else {
            return Ok(None);
        };
        if args.len() != def.params.len() || def.params.is_empty() {
            // Partial application / arity mismatch — not a redex here.
            return Ok(None);
        }
        // Step A: rewrite the head `f` to `λparams. body` under the argument
        // spine, carrying the `{f=λ}` hypothesis: `⊢ (f a…) = ((λ…) a…)`.
        let mut thm = def.assumption.clone(); // {f=λ} ⊢ f = λ…
        for a in &args {
            thm = thm.cong_fn(a.clone()).map_err(kernel_err)?;
        }
        // Step B: β-reduce the spine `((λparams. body) a₁ … aₙ)` argument by
        // argument (outermost binder first), firing the leftmost redex each
        // time and composing via trans.
        for _ in 0..args.len() {
            let cur = self.rhs(&thm)?;
            let beta = self.beta_leftmost(&cur)?;
            thm = thm.trans(beta).map_err(kernel_err)?;
        }
        let to = self.rhs(&thm)?;
        Ok(Some(LispStep { to, thm }))
    }

    /// `⊢ spine = spine'` firing the **leftmost** β-redex of an
    /// application spine `((λ. body) a₁) … aₙ` — congruence-lifted over the
    /// trailing arguments.
    fn beta_leftmost(&self, t: &Term) -> Result<Thm, HolError> {
        // Descend the function spine to the innermost `App(Abs, arg)`.
        let (f, arg) = t
            .as_app()
            .ok_or_else(|| HolError::Kernel("beta_leftmost: not an application".into()))?;
        if f.as_abs().is_some() {
            // `t = (λ. body) arg` — fire it directly.
            return Thm::beta_conv(t.clone()).map_err(kernel_err);
        }
        // Otherwise the redex is deeper in the function position; recurse and
        // lift under the trailing argument.
        let inner = self.beta_leftmost(f)?;
        inner.cong_fn(arg.clone()).map_err(kernel_err)
    }

    /// `⊢ car v = h` (or `cdr v = t`) for a value `v`.
    fn fire_proj(&self, redex: &Term, take_cdr: bool, v: &Term) -> Result<LispStep, HolError> {
        let law = if let Some((h, tl)) = self.as_scons(v) {
            self.cs.proj_scons(take_cdr, &h, &tl).map_err(kernel_err)?
        } else if let Some(b) = self.as_atom(v) {
            self.cs
                .proj_leaf(take_cdr, LeafKind::Atom(&b))
                .map_err(kernel_err)?
        } else if *v == self.cs.snil {
            self.cs
                .proj_leaf(take_cdr, LeafKind::Nil)
                .map_err(kernel_err)?
        } else {
            return Err(HolError::Stuck(format!("car/cdr of non-`sexpr` `{v}`")));
        };
        self.package(redex, law)
    }

    /// `⊢ pred v = T/F` for a value `v`.
    fn fire_pred(&self, redex: &Term, pred: Pred, v: &Term) -> Result<LispStep, HolError> {
        let law = match pred {
            Pred::Atom => {
                if let Some((h, t)) = self.as_scons(v) {
                    self.l.atom_scons(&h, &t).map_err(kernel_err)?
                } else if let Some(b) = self.as_atom(v) {
                    self.l.atom_atom(&b).map_err(kernel_err)?
                } else if *v == self.cs.snil {
                    self.l.atom_nil().map_err(kernel_err)?
                } else {
                    return Err(HolError::Stuck(format!("atom? of non-`sexpr` `{v}`")));
                }
            }
            Pred::Consp => {
                if let Some((h, t)) = self.as_scons(v) {
                    self.l.consp_scons(&h, &t).map_err(kernel_err)?
                } else if let Some(b) = self.as_atom(v) {
                    self.l.consp_atom(&b).map_err(kernel_err)?
                } else if *v == self.cs.snil {
                    self.l.consp_nil().map_err(kernel_err)?
                } else {
                    return Err(HolError::Stuck(format!("consp of non-`sexpr` `{v}`")));
                }
            }
        };
        self.package(redex, law)
    }

    /// `¬ p`: if `p` is a bool literal, fold `¬ literal` to a literal via
    /// `simp`; otherwise step inside `p`.
    fn step_not(&self, t: &Term, p: &Term) -> Result<Option<LispStep>, HolError> {
        if p.as_bool().is_some() {
            // ⊢ ¬ p = T/F  (a single fold).
            let thm = Thm::refl(t.clone())
                .map_err(kernel_err)?
                .rhs_conv(simp)
                .map_err(kernel_err)?;
            let to = self.rhs(&thm)?;
            return Ok(Some(LispStep { to, thm }));
        }
        // Step inside `p`, lift under `not`.
        if let Some(inner) = self.step_term(p)? {
            let lifted = inner
                .thm
                .clone()
                .cong_arg(self.not_head())
                .map_err(kernel_err)?;
            let to = hol_not(inner.to.clone());
            return Ok(Some(LispStep { to, thm: lifted }));
        }
        Err(HolError::Stuck(format!("no reduction for `{t}`")))
    }

    /// A `cond α c x y` step: reduce the condition `c` to a `bool` literal
    /// (congruence-lifting the step under `cond α · x y`); once `c` is a
    /// literal, fire the [`cond_true`] / [`cond_false`] clause to select a
    /// branch (the unselected branch is discarded, never reduced).
    fn step_cond(&self, alpha: &Type, c: &Term, x: &Term, y: &Term) -> Result<LispStep, HolError> {
        if let Some(b) = c.as_bool() {
            // ⊢ cond α (T|F) x y = (x|y).
            let clause = if b {
                cond_true(alpha, x, y).map_err(kernel_err)?
            } else {
                cond_false(alpha, x, y).map_err(kernel_err)?
            };
            let to = self.rhs(&clause)?;
            return Ok(LispStep { to, thm: clause });
        }
        // Step inside the condition, lifting under `cond α · x y`.
        let inner = self
            .step_term(c)?
            .ok_or_else(|| HolError::Stuck(format!("cond condition is stuck: `{c}`")))?;
        // `cond α c x y = App(App(App(cond α, c), x), y)`; the step is on `c`,
        // so lift it under the head `cond α` then over the trailing `x`, `y`.
        let cond_head = covalence_hol_eval::defs::cond(alpha.clone());
        let lifted = inner
            .thm
            .clone()
            .cong_arg(cond_head) // ⊢ (cond α) c = (cond α) c'
            .map_err(kernel_err)?
            .cong_fn(x.clone()) // ⊢ (cond α c) x = (cond α c') x
            .map_err(kernel_err)?
            .cong_fn(y.clone()) // ⊢ (cond α c x) y = (cond α c' x) y
            .map_err(kernel_err)?;
        let to = self.mk_cond(alpha, inner.to.clone(), x.clone(), y.clone())?;
        Ok(LispStep { to, thm: lifted })
    }

    /// `eq?` on two atom-value operands `atom b₁`, `atom b₂` — decide the HOL
    /// equation `(atom b₁ = atom b₂)` to `T`/`F`, as the self-contained step
    /// `⊢ (atom b₁ = atom b₂) = ⌜b₁ == b₂⌝`. Composes into the reduction chain
    /// (the step's LHS is the actual redex term).
    ///
    /// Both the equal and distinct cases use only sound, hypothesis-free
    /// derived facts: `⊢ (atom b₁ = atom b₂) = (b₁ = b₂)` (the carved `atom`
    /// injectivity `(atom b₁ = atom b₂) ⟹ (b₁ = b₂)` and the congruence
    /// converse, combined by `deduct_antisym`), chained with the decided blob
    /// equality `⊢ (b₁ = b₂) = T|F` (from `reduce_consts`).
    fn eval_eq_leaf(&self, a: &Term, b: &Term) -> Result<LispStep, HolError> {
        let b1 = self
            .as_atom(a)
            .ok_or_else(|| HolError::Stuck("eq? left operand is not an atom".into()))?;
        let b2 = self
            .as_atom(b)
            .ok_or_else(|| HolError::Stuck("eq? right operand is not an atom".into()))?;
        // Decide the underlying blob equality `⊢ (b₁ = b₂) = T|F`.
        let blob_eq = b1.clone().equals(b2.clone()).map_err(kernel_err)?;
        let blob_thm = blob_eq.reduce_consts().map_err(kernel_err)?;
        let decided = self.rhs(&blob_thm)?;
        let thm = match decided.as_bool() {
            // Equal atoms: `⊢ atom b = atom b` (refl), then `⊢ (…) = T`
            // (`eqt_intro`). (Injectivity self-simplifies `b = b` to `T`, so the
            // general iff route degenerates here — this direct form is cleaner.)
            Some(true) => Thm::refl(a.clone())
                .map_err(kernel_err)?
                .eqt_intro()
                .map_err(kernel_err)?,
            // Distinct atoms: `⊢ (atom b₁ = atom b₂) = (b₁ = b₂)` via injectivity
            // + congruence, then chain the decided disequality `= F`.
            Some(false) => self
                .atom_eq_iff_blob(a, b, &b1, &b2)?
                .trans(blob_thm)
                .map_err(kernel_err)?,
            None => {
                return Err(HolError::Kernel(
                    "eq?: blob equality did not decide to a literal".into(),
                ));
            }
        };
        let to = self.rhs(&thm)?;
        Ok(LispStep { to, thm })
    }

    /// `⊢ (atom b₁ = atom b₂) = (b₁ = b₂)` — `atom` injectivity (forward) and
    /// congruence (backward) combined by [`Thm::deduct_antisym`]. Genuine
    /// (hypothesis-free): both directions discharge their assumptions.
    fn atom_eq_iff_blob(&self, a: &Term, b: &Term, b1: &Term, b2: &Term) -> Result<Thm, HolError> {
        let atom_eq = a.clone().equals(b.clone()).map_err(kernel_err)?;
        let blob_eq = b1.clone().equals(b2.clone()).map_err(kernel_err)?;
        // Forward: {atom b₁ = atom b₂} ⊢ (b₁ = b₂) — injectivity + MP.
        let inj = self.cs.inj_atom(b1, b2).map_err(kernel_err)?;
        let fwd = inj
            .imp_elim(Thm::assume(atom_eq.clone()).map_err(kernel_err)?)
            .map_err(kernel_err)?;
        // Backward: {b₁ = b₂} ⊢ (atom b₁ = atom b₂) — congruence under `atom`.
        let bwd = Thm::assume(blob_eq)
            .map_err(kernel_err)?
            .cong_arg(self.cs.atom.clone())
            .map_err(kernel_err)?;
        // deduct_antisym(fwd, bwd) : ⊢ (b₁ = b₂) = (atom b₁ = atom b₂); flip.
        fwd.deduct_antisym(bwd)
            .map_err(kernel_err)?
            .sym()
            .map_err(kernel_err)
    }

    /// Match an integer-op redex `int.<op> a b` (the compiled `(+ a b)` /
    /// `(- …)` / `(* …)` / `(<= …)` / `(= …)` form), returning `(op, a, b)`.
    /// Only fires when an [`IntBackend`] is wired. Note the compiled `=` is
    /// HOL equality at `int`, disjoint from the `eq?` redex (equality at
    /// `sexpr`, handled earlier).
    fn as_int_redex(&self, t: &Term) -> Option<(IntOp, Term, Term)> {
        self.int.as_ref()?;
        let (inner, b) = t.as_app()?;
        let (head, a) = inner.as_app()?;
        let op = IntOp::ALL
            .into_iter()
            .find(|op| *head == int_backend::kernel_op_term(*op))?;
        Some((op, a.clone(), b.clone()))
    }

    fn as_append_redex(&self, t: &Term) -> Option<(Term, Term)> {
        let (inner, right) = t.as_app()?;
        let (head, left) = inner.as_app()?;
        (*head == self.l.append).then(|| (left.clone(), right.clone()))
    }

    fn step_append(&self, redex: &Term, left: &Term, right: &Term) -> Result<LispStep, HolError> {
        if !self.is_data_value(left) {
            let inner = self.step_term(left)?.ok_or_else(|| {
                HolError::Stuck(format!("append left operand is stuck: `{left}`"))
            })?;
            let thm = inner
                .thm
                .clone()
                .cong_arg(self.l.append.clone())
                .map_err(kernel_err)?
                .cong_fn(right.clone())
                .map_err(kernel_err)?;
            let to = self
                .l
                .append
                .clone()
                .apply(inner.to)
                .map_err(kernel_err)?
                .apply(right.clone())
                .map_err(kernel_err)?;
            return Ok(LispStep { to, thm });
        }
        if !self.is_data_value(right) {
            let inner = self.step_term(right)?.ok_or_else(|| {
                HolError::Stuck(format!("append right operand is stuck: `{right}`"))
            })?;
            let spine = self
                .l
                .append
                .clone()
                .apply(left.clone())
                .map_err(kernel_err)?;
            let thm = inner
                .thm
                .clone()
                .cong_arg(spine.clone())
                .map_err(kernel_err)?;
            let to = spine.apply(inner.to).map_err(kernel_err)?;
            return Ok(LispStep { to, thm });
        }
        let law = if *left == self.cs.snil {
            self.l
                .append_leaf(LeafArg::Nil, right)
                .map_err(kernel_err)?
        } else if let Some(blob) = self.as_atom(left) {
            self.l
                .append_leaf(LeafArg::Atom(&blob), right)
                .map_err(kernel_err)?
        } else if let Some((head, tail)) = self.as_scons(left) {
            self.l
                .append_scons(&head, &tail, right)
                .map_err(kernel_err)?
        } else {
            return Err(HolError::Stuck(format!(
                "append expected S-expression data, got `{left}`"
            )));
        };
        let (lhs, _) = law
            .concl()
            .as_eq()
            .ok_or_else(|| HolError::Kernel("append law is not an equation".into()))?;
        if lhs != redex {
            return Err(HolError::Kernel(format!(
                "append law `{}` does not match redex `{redex}`",
                law.concl()
            )));
        }
        self.package(redex, law)
    }

    /// One step of an integer-op redex `int.<op> a b`:
    ///
    /// 1. If `a` (then `b`) is not yet an `int` literal, step inside it and
    ///    congruence-lift the step over the redex (leftmost-innermost, like
    ///    the generic congruence).
    /// 2. Both literals: fire the **kernel-proved** computation — the
    ///    [`IntBackend::prove_reduce`] equation `⊢ int.<op> a b = r`
    ///    (`TermExt::reduce` underneath), with the backend's guards applied
    ///    (the nat variant rejects a negative result here). The step theorem
    ///    *is* that kernel equation; nothing is asserted.
    fn step_int(&self, t: &Term, op: IntOp, a: &Term, b: &Term) -> Result<LispStep, HolError> {
        let backend = self
            .int
            .as_ref()
            .ok_or_else(|| HolError::Theory("no integer backend".into()))?;
        let head = int_backend::kernel_op_term(op);
        // Left operand first.
        if covalence_hol_eval::as_int(a).is_none() {
            let inner = self.step_term(a)?.ok_or_else(|| {
                HolError::Stuck(format!(
                    "`{}` expects integer operands, got `{a}`",
                    op.symbol()
                ))
            })?;
            let thm = inner
                .thm
                .clone()
                .cong_arg(head.clone()) // ⊢ op a = op a'
                .map_err(kernel_err)?
                .cong_fn(b.clone()) // ⊢ (op a) b = (op a') b
                .map_err(kernel_err)?;
            let to = Term::app(Term::app(head, inner.to.clone()), b.clone());
            return Ok(LispStep { to, thm });
        }
        // Then the right operand.
        if covalence_hol_eval::as_int(b).is_none() {
            let inner = self.step_term(b)?.ok_or_else(|| {
                HolError::Stuck(format!(
                    "`{}` expects integer operands, got `{b}`",
                    op.symbol()
                ))
            })?;
            let spine = Term::app(head, a.clone());
            let thm = inner
                .thm
                .clone()
                .cong_arg(spine.clone()) // ⊢ (op a) b = (op a) b'
                .map_err(kernel_err)?;
            let to = Term::app(spine, inner.to.clone());
            return Ok(LispStep { to, thm });
        }
        // Both operands are literals: the kernel-proved computation.
        let va = covalence_hol_eval::as_int(a).expect("checked above");
        let vb = covalence_hol_eval::as_int(b).expect("checked above");
        let proof = backend.prove_reduce(op, &va, &vb)?;
        let thm = proof
            .eqs
            .into_iter()
            .next()
            .ok_or_else(|| HolError::Kernel("integer backend returned no equation".into()))?;
        let (lhs, rhs) = thm
            .concl()
            .as_eq()
            .ok_or_else(|| HolError::Kernel("integer equation is not an equation".into()))?;
        if lhs != t {
            return Err(HolError::Kernel(format!(
                "integer equation `{}` does not match the redex `{t}`",
                thm.concl()
            )));
        }
        let to = rhs.clone();
        Ok(LispStep { to, thm })
    }

    /// Wrap a head law `⊢ redex = rhs` into a [`LispStep`].
    fn package(&self, _redex: &Term, law: Thm) -> Result<LispStep, HolError> {
        let to = self.rhs(&law)?;
        Ok(LispStep { to, thm: law })
    }

    fn rhs(&self, thm: &Thm) -> Result<Term, HolError> {
        thm.concl()
            .as_eq()
            .map(|(_, r)| r.clone())
            .ok_or_else(|| HolError::Kernel("theorem conclusion is not an equation".into()))
    }

    // ---- term inspection ------------------------------------------------

    fn not_head(&self) -> Term {
        // `¬ p = App(not, p)`; recover the `not` head from a fresh `¬ p`.
        // Build `¬ <snil>` once and take its function side.
        let sample = hol_not(self.cs.snil.clone());
        sample.as_app().map(|(f, _)| f.clone()).unwrap_or(sample)
    }

    fn as_not(&self, t: &Term) -> Option<Term> {
        let (f, p) = t.as_app()?;
        (*f == self.not_head()).then(|| p.clone())
    }

    /// Match a HOL equation `a = b : sexpr` (the compiled `eq?` redex),
    /// returning `(a, b)`. Only `sexpr`-typed equations qualify (so an internal
    /// `bool` equation, e.g. inside a decided `cond`, is not treated as `eq?`).
    fn as_eq_redex(&self, t: &Term) -> Option<(Term, Term)> {
        use covalence_core::TermKind;
        let (inner, b) = t.as_app()?;
        let (head, a) = inner.as_app()?;
        match head.kind() {
            TermKind::Eq(alpha) if *alpha == self.cs.tau => Some((a.clone(), b.clone())),
            _ => None,
        }
    }

    /// Match `cond α c x y`, returning `(α, c, x, y)`.
    fn as_cond(&self, t: &Term) -> Option<(Type, Term, Term, Term)> {
        use covalence_core::TypeKind;
        let (cxy, y) = t.as_app()?;
        let (cx, x) = cxy.as_app()?;
        let (head, c) = cx.as_app()?;
        let (spec, _args) = head.as_spec()?;
        if spec.symbol().label() != covalence_hol_eval::defs::cond_spec().symbol().label() {
            return None;
        }
        // Recover α from the head `cond α : bool → α → α → α`.
        let alpha = match head.type_of().ok()?.kind() {
            // `bool → (α → α → α)` — descend one arrow to get `α`.
            TypeKind::Fun(_, rest) => match rest.kind() {
                TypeKind::Fun(a, _) => a.clone(),
                _ => return None,
            },
            _ => return None,
        };
        Some((alpha, c.clone(), x.clone(), y.clone()))
    }

    pub(crate) fn as_scons(&self, v: &Term) -> Option<(Term, Term)> {
        self.carrier.as_cons(v)
    }

    pub(crate) fn as_atom(&self, v: &Term) -> Option<Term> {
        self.carrier.as_atom_term(v)
    }

    pub(crate) fn is_snil(&self, v: &Term) -> bool {
        self.carrier.is_nil(v)
    }

    pub(crate) fn atom_bytes(&self, v: &Term) -> Option<Vec<u8>> {
        self.carrier.atom_bytes(v)
    }
}

impl Semantics<LispRepr> for LispSemantics {
    type StepCert = LispStep;
    type Thm = Thm;
    type Error = HolError;

    fn step(&self, term: &Term) -> Result<Option<LispStep>, HolError> {
        self.step_term(term)
    }

    fn compose(&self, prev: Option<Thm>, step_thm: Thm) -> Result<Thm, HolError> {
        match prev {
            None => Ok(step_thm),
            Some(p) => p.trans(step_thm).map_err(kernel_err),
        }
    }
}

#[derive(Clone, Copy, Debug)]
enum Pred {
    Atom,
    Consp,
}

/// Unwind an application spine `((f a₁) a₂) … aₙ ↦ (f, [a₁, …, aₙ])`.
fn unwind_app(t: &Term) -> (Term, Vec<Term>) {
    let mut args = Vec::new();
    let mut cur = t.clone();
    while let Some((f, a)) = cur.as_app() {
        args.push(a.clone());
        cur = f.clone();
    }
    args.reverse();
    (cur, args)
}

/// Re-render a surface [`SExpr`] as source text (for error messages — the
/// user sees the form they typed, not internal kernel syntax).
fn surface(e: &SExpr) -> String {
    match e {
        SExpr::Atom(Atom::Symbol(s)) => s.to_string(),
        SExpr::Atom(Atom::Str { bytes, .. }) => {
            format!("\"{}\"", String::from_utf8_lossy(bytes))
        }
        SExpr::List(items) => {
            let inner: Vec<String> = items.iter().map(surface).collect();
            format!("({})", inner.join(" "))
        }
    }
}

/// A bare `t` / `nil` symbol — the ambiguous atom that compiles to either a
/// `bool` literal or a `sexpr` datum depending on the surrounding `cond`'s
/// inferred branch type.
fn is_bare_bool_lit(e: &SExpr) -> bool {
    matches!(e.as_symbol(), Some("t") | Some("nil"))
}

/// The reserved special-form / builtin operator names — a symbol head that is
/// **not** one of these is a user function call (a `defun` or a forward
/// reference), never an "unknown operator" error.
fn is_reserved(name: &str) -> bool {
    matches!(
        name,
        "quote"
            | "car"
            | "cdr"
            | "cons"
            | "atom?"
            | "atom"
            | "consp"
            | "pair?"
            | "null?"
            | "null"
            | "eq?"
            | "eq"
            | "if"
            | "cond"
            | "lambda"
            | "defun"
            | "define"
            | "label"
    )
}

#[cfg(test)]
mod core_backend_tests {
    use super::*;
    use crate::frontend::{Frontend, SurfaceDialect};

    fn one(source: &str) -> SExpr {
        crate::reader::read(source).unwrap().pop().unwrap()
    }

    #[test]
    fn shared_core_and_legacy_surface_compile_to_identical_hol_terms() {
        let semantics = LispSemantics::new().unwrap();
        let frontend = Frontend::new(SurfaceDialect::Scheme);
        for source in [
            "(car (cons (quote a) (quote ())))",
            "(+ 2 (* 3 4))",
            "((lambda (x) (cons x (quote ()))) (quote a))",
            "(if (null? (quote ())) (quote yes) (quote no))",
        ] {
            let surface = one(source);
            let core = frontend.lower(&surface).unwrap();
            assert_eq!(
                semantics.compile_core(&core).unwrap(),
                semantics.compile(&surface).unwrap(),
                "{source}"
            );
        }
    }

    #[test]
    fn scheme_quote_preserves_exact_integer_data() {
        let semantics = LispSemantics::new().unwrap();
        let surface = one("(quote 42)");
        let core = Frontend::new(SurfaceDialect::Scheme)
            .lower(&surface)
            .unwrap();
        assert!(matches!(
            core,
            CoreExpr::Quote(Datum::Atom(CoreAtom::Integer(ref value)))
                if value == &Int::from(42)
        ));
        assert_eq!(
            semantics.compile_core(&core).unwrap(),
            covalence_hol_eval::mk_int(Int::from(42))
        );
    }
}
