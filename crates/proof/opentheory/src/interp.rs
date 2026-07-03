//! Generic OpenTheory article interpreter.
//!
//! `ArticleInterp<K>` implements `ArticleMachine` for any `K: HolLightKernel`,
//! translating OpenTheory stack-machine commands into kernel trait calls.

use std::collections::HashMap;

use covalence_hol::traits::HolLightKernel;
use covalence_hol::types::{HolError, NameId};

use crate::error::OtError;
use crate::machine::{ArticleMachine, ArticleResult};
use crate::name::{NameTable, OtName};
use crate::object::{OtObject, obj_type_name};
use crate::reader::read_article;

/// OpenTheory article interpreter, generic over the kernel.
pub struct ArticleInterp<'a, K: HolLightKernel> {
    kernel: &'a mut K,
    names: &'a mut NameTable,
    stack: Vec<OtObject<K>>,
    dict: HashMap<u32, OtObject<K>>,
    assumptions: Vec<K::Thm>,
    theorems: Vec<K::Thm>,
    version: u32,
}

impl<'a, K: HolLightKernel> ArticleInterp<'a, K> {
    pub fn new(kernel: &'a mut K, names: &'a mut NameTable) -> Self {
        ArticleInterp {
            kernel,
            names,
            stack: Vec::new(),
            dict: HashMap::new(),
            assumptions: Vec::new(),
            theorems: Vec::new(),
            version: 5,
        }
    }

    /// Convenience: interpret an article string, consuming the interpreter.
    pub fn interpret(mut self, input: &str) -> Result<ArticleResult<K>, OtError> {
        read_article(&mut self, input)?;
        Ok(self.finish())
    }

    // -------------------------------------------------------------------
    // Stack helpers
    // -------------------------------------------------------------------

    fn pop(&mut self) -> Result<OtObject<K>, OtError> {
        self.stack.pop().ok_or(OtError::StackUnderflow)
    }

    fn pop_num(&mut self) -> Result<i64, OtError> {
        match self.pop()? {
            OtObject::Num(n) => Ok(n),
            other => Err(OtError::TypeError {
                expected: "Num".into(),
                got: obj_type_name(&other),
            }),
        }
    }

    fn pop_name(&mut self) -> Result<OtName, OtError> {
        match self.pop()? {
            OtObject::Name(n) => Ok(n),
            other => Err(OtError::TypeError {
                expected: "Name".into(),
                got: obj_type_name(&other),
            }),
        }
    }

    fn pop_list(&mut self) -> Result<Vec<OtObject<K>>, OtError> {
        match self.pop()? {
            OtObject::List(l) => Ok(l),
            other => Err(OtError::TypeError {
                expected: "List".into(),
                got: obj_type_name(&other),
            }),
        }
    }

    fn pop_type(&mut self) -> Result<K::Type, OtError> {
        match self.pop()? {
            OtObject::Type(t) => Ok(t),
            other => Err(OtError::TypeError {
                expected: "Type".into(),
                got: obj_type_name(&other),
            }),
        }
    }

    fn pop_term(&mut self) -> Result<K::Term, OtError> {
        match self.pop()? {
            OtObject::Term(t) => Ok(t),
            other => Err(OtError::TypeError {
                expected: "Term".into(),
                got: obj_type_name(&other),
            }),
        }
    }

    fn pop_thm(&mut self) -> Result<K::Thm, OtError> {
        match self.pop()? {
            OtObject::Thm(t) => Ok(t),
            other => Err(OtError::TypeError {
                expected: "Thm".into(),
                got: obj_type_name(&other),
            }),
        }
    }

    fn pop_var(&mut self) -> Result<(NameId, K::Type), OtError> {
        match self.pop()? {
            OtObject::Var(n, ty) => Ok((n, ty)),
            other => Err(OtError::TypeError {
                expected: "Var".into(),
                got: obj_type_name(&other),
            }),
        }
    }

    fn pop_const(&mut self) -> Result<NameId, OtError> {
        match self.pop()? {
            OtObject::Const(n) => Ok(n),
            other => Err(OtError::TypeError {
                expected: "Const".into(),
                got: obj_type_name(&other),
            }),
        }
    }

    fn pop_type_op(&mut self) -> Result<NameId, OtError> {
        match self.pop()? {
            OtObject::TypeOp(n) => Ok(n),
            other => Err(OtError::TypeError {
                expected: "TypeOp".into(),
                got: obj_type_name(&other),
            }),
        }
    }

    fn peek(&self) -> Result<&OtObject<K>, OtError> {
        self.stack.last().ok_or(OtError::StackUnderflow)
    }

    // -------------------------------------------------------------------
    // Name resolution helpers
    // -------------------------------------------------------------------

    fn intern_name(&mut self, name: &OtName) -> NameId {
        let qualified = name.qualified();
        let id = self.names.intern(qualified.clone());
        // Tell the backend what string this NameId refers to. The
        // backend uses this for symbol-keyed rewrites (e.g. folding
        // `Comb(Const "Data.Bool.!", _)` to `Forall(_)` in HolPrim).
        self.kernel.register_name(id, &qualified);
        id
    }
}

// -------------------------------------------------------------------
// ArticleMachine implementation
// -------------------------------------------------------------------

impl<K: HolLightKernel> ArticleMachine for ArticleInterp<'_, K> {
    type Kernel = K;

    fn push_num(&mut self, n: i64) -> Result<(), OtError> {
        self.stack.push(OtObject::Num(n));
        Ok(())
    }

    fn push_name(&mut self, s: &str) -> Result<(), OtError> {
        let name = OtName::parse(s);
        self.stack.push(OtObject::Name(name));
        Ok(())
    }

    // absTerm: Var v, Term b -> Term (λv. b)
    fn cmd_abs_term(&mut self) -> Result<(), OtError> {
        let body = self.pop_term()?;
        let (name, ty) = self.pop_var()?;
        let var = self.kernel.mk_var(name, ty);
        let abs = self.kernel.mk_abs(var, body);
        self.stack.push(OtObject::Term(abs));
        Ok(())
    }

    // absThm: Var v, Thm (Γ ⊦ t = u) -> Thm (Γ ⊦ (λv. t) = (λv. u))
    fn cmd_abs_thm(&mut self) -> Result<(), OtError> {
        let th = self.pop_thm()?;
        let (name, ty) = self.pop_var()?;
        let var = self.kernel.mk_var(name, ty);
        let result = self.kernel.abs_rule(var, th)?;
        self.stack.push(OtObject::Thm(result));
        Ok(())
    }

    // appTerm: Term f, Term x -> Term (f x)
    fn cmd_app_term(&mut self) -> Result<(), OtError> {
        let x = self.pop_term()?;
        let f = self.pop_term()?;
        let app = self.kernel.mk_comb(f, x);
        self.stack.push(OtObject::Term(app));
        Ok(())
    }

    // appThm: Thm (Γ ⊦ f = g), Thm (Δ ⊦ x = y) -> Thm (Γ ∪ Δ ⊦ f x = g y)
    fn cmd_app_thm(&mut self) -> Result<(), OtError> {
        let th2 = self.pop_thm()?;
        let th1 = self.pop_thm()?;
        let result = self.kernel.mk_comb_rule(th1, th2)?;
        self.stack.push(OtObject::Thm(result));
        Ok(())
    }

    // assume: Term φ -> Thm ({φ} ⊦ φ)
    fn cmd_assume(&mut self) -> Result<(), OtError> {
        let tm = self.pop_term()?;
        let result = self.kernel.assume_rule(tm)?;
        self.stack.push(OtObject::Thm(result));
        Ok(())
    }

    // axiom: List [t1,...,tn], Term φ -> Thm ({t1,...,tn} ⊦ φ)
    fn cmd_axiom(&mut self) -> Result<(), OtError> {
        let concl = self.pop_term()?;
        let hyps_list = self.pop_list()?;
        let mut _hyps = Vec::new();
        for obj in hyps_list {
            match obj {
                OtObject::Term(t) => _hyps.push(t),
                _ => {
                    return Err(OtError::TypeError {
                        expected: "Term".into(),
                        got: obj_type_name(&obj),
                    });
                }
            }
        }
        let thm = self.kernel.new_axiom(concl)?;
        self.assumptions.push(thm.clone());
        self.stack.push(OtObject::Thm(thm));
        Ok(())
    }

    // betaConv: Term ((λv. t) u) -> Thm (⊦ (λv. t) u = t[u/v])
    fn cmd_beta_conv(&mut self) -> Result<(), OtError> {
        let tm = self.pop_term()?;
        // Destruct: tm = Comb(Abs(var, body), arg)
        let (f, arg) = self
            .kernel
            .dest_comb(tm.clone())
            .ok_or(HolError::NotBetaRedex)?;
        let (var, _body) = self
            .kernel
            .dest_abs(f.clone())
            .ok_or(HolError::NotBetaRedex)?;

        if self.kernel.term_eq(var.clone(), arg.clone()) {
            // Simple case: (\x. body) x = body
            let result = self.kernel.beta_conv(tm)?;
            self.stack.push(OtObject::Thm(result));
        } else {
            // General case: (\x. body) t
            // Build exact beta redex (\x. body) x, then INST x -> t.
            let exact_redex = self.kernel.mk_comb(f, var.clone());
            let beta_thm = self.kernel.beta_conv(exact_redex)?;
            let pairs = vec![(arg, var)];
            let result = self.kernel.inst_rule(&pairs, beta_thm)?;
            self.stack.push(OtObject::Thm(result));
        }
        Ok(())
    }

    // cons: h, List t -> List (h :: t)
    fn cmd_cons(&mut self) -> Result<(), OtError> {
        let tail = self.pop_list()?;
        let head = self.pop()?;
        let mut list = vec![head];
        list.extend(tail);
        self.stack.push(OtObject::List(list));
        Ok(())
    }

    // const: Name n -> Const c
    fn cmd_const(&mut self) -> Result<(), OtError> {
        let name = self.pop_name()?;
        let id = self.intern_name(&name);
        self.stack.push(OtObject::Const(id));
        Ok(())
    }

    // constTerm: Const c, Type ty -> Term t
    fn cmd_const_term(&mut self) -> Result<(), OtError> {
        let ty = self.pop_type()?;
        let c = self.pop_const()?;
        let tm = self.kernel.mk_const_validated(c, ty)?;
        self.stack.push(OtObject::Term(tm));
        Ok(())
    }

    // deductAntisym: Thm (Γ ⊦ φ), Thm (Δ ⊦ ψ) -> Thm ((Γ-{ψ}) ∪ (Δ-{φ}) ⊦ φ = ψ)
    fn cmd_deduct_antisym(&mut self) -> Result<(), OtError> {
        let th2 = self.pop_thm()?;
        let th1 = self.pop_thm()?;
        let result = self.kernel.deduct_antisym(th1, th2)?;
        self.stack.push(OtObject::Thm(result));
        Ok(())
    }

    // def: Num k, x -> x (dict[k] = x; x stays on stack)
    fn cmd_def(&mut self) -> Result<(), OtError> {
        let num = self.pop_num()?;
        let obj = self.peek()?.clone();
        self.dict.insert(num as u32, obj);
        Ok(())
    }

    // defineConst: Name n, Term t -> Const c, Thm (⊦ c = t)
    fn cmd_define_const(&mut self) -> Result<(), OtError> {
        let tm = self.pop_term()?;
        let name = self.pop_name()?;
        let name_id = self.intern_name(&name);
        let var_ty = self.kernel.type_of(tm.clone());
        let var_tm = self.kernel.mk_var(name_id, var_ty);
        let eq = self.kernel.mk_eq(var_tm, tm);
        let thm = self.kernel.new_basic_definition(eq)?;
        self.stack.push(OtObject::Const(name_id));
        self.stack.push(OtObject::Thm(thm));
        Ok(())
    }

    // defineTypeOp: Name n, Name abs, Name rep, List [tyvar_names], Thm (⊦ P t)
    //   -> TypeOp, Const abs, Const rep, Thm1, Thm2
    fn cmd_define_type_op(&mut self) -> Result<(), OtError> {
        let th = self.pop_thm()?;
        let tyvar_names = self.pop_list()?;
        let rep_name = self.pop_name()?;
        let abs_name = self.pop_name()?;
        let tyname = self.pop_name()?;

        let tyname_id = self.intern_name(&tyname);
        let abs_id = self.intern_name(&abs_name);
        let rep_id = self.intern_name(&rep_name);

        let _ = tyvar_names;

        // Variable names for the generated theorems (OpenTheory convention).
        let abs_var_name = self.names.intern_str("a");
        let rep_var_name = self.names.intern_str("r");

        let (thm1, thm2) = self.kernel.new_basic_type_definition(
            tyname_id,
            abs_id,
            rep_id,
            abs_var_name,
            rep_var_name,
            th,
        )?;

        self.stack.push(OtObject::TypeOp(tyname_id));
        self.stack.push(OtObject::Const(abs_id));
        self.stack.push(OtObject::Const(rep_id));
        self.stack.push(OtObject::Thm(thm1));
        self.stack.push(OtObject::Thm(thm2));
        Ok(())
    }

    // eqMp: Thm (Δ ⊦ φ = ψ), Thm (Γ ⊦ φ) -> Thm (Γ ∪ Δ ⊦ ψ)
    fn cmd_eq_mp(&mut self) -> Result<(), OtError> {
        let th2 = self.pop_thm()?;
        let th1 = self.pop_thm()?;
        let result = self.kernel.eq_mp(th1, th2)?;
        self.stack.push(OtObject::Thm(result));
        Ok(())
    }

    // nil: -> List []
    fn cmd_nil(&mut self) -> Result<(), OtError> {
        self.stack.push(OtObject::List(vec![]));
        Ok(())
    }

    // opType: TypeOp op, List [ty1,...,tyn] -> Type ((ty1,...,tyn) op)
    fn cmd_op_type(&mut self) -> Result<(), OtError> {
        let args_list = self.pop_list()?;
        let op = self.pop_type_op()?;
        let mut args = Vec::new();
        for obj in args_list {
            match obj {
                OtObject::Type(t) => args.push(t),
                _ => {
                    return Err(OtError::TypeError {
                        expected: "Type".into(),
                        got: obj_type_name(&obj),
                    });
                }
            }
        }
        let ty = self.kernel.mk_type_validated(op, args)?;
        self.stack.push(OtObject::Type(ty));
        Ok(())
    }

    // pop: x -> (discard)
    fn cmd_pop(&mut self) -> Result<(), OtError> {
        self.pop()?;
        Ok(())
    }

    // ref: Num k -> dict[k]
    fn cmd_ref(&mut self) -> Result<(), OtError> {
        let k = self.pop_num()?;
        let obj = self
            .dict
            .get(&(k as u32))
            .ok_or(OtError::DictKeyNotFound(k as u32))?
            .clone();
        self.stack.push(obj);
        Ok(())
    }

    // refl: Term t -> Thm (⊦ t = t)
    fn cmd_refl(&mut self) -> Result<(), OtError> {
        let tm = self.pop_term()?;
        let thm = self.kernel.refl(tm)?;
        self.stack.push(OtObject::Thm(thm));
        Ok(())
    }

    // remove: Num k -> dict[k] (and delete from dict)
    fn cmd_remove(&mut self) -> Result<(), OtError> {
        let k = self.pop_num()?;
        let obj = self
            .dict
            .remove(&(k as u32))
            .ok_or(OtError::DictKeyNotFound(k as u32))?;
        self.stack.push(obj);
        Ok(())
    }

    // subst: List [[type_pairs], [term_pairs]], Thm -> Thm
    fn cmd_subst(&mut self) -> Result<(), OtError> {
        let th = self.pop_thm()?;
        let subst_list = self.pop_list()?;
        if subst_list.len() != 2 {
            return Err(OtError::ParseError(format!(
                "subst expects list of [type_subst, term_subst], got {} elements: {:?}",
                subst_list.len(),
                subst_list
            )));
        }
        // Parse type substitutions: list of [Name, Type] pairs -> [(new_type, old_tyvar_name)]
        // Per OpenTheory spec: pair[0] = Name (old tyvar), pair[1] = Type (new type)
        let type_pairs_list = match &subst_list[0] {
            OtObject::List(l) => l.clone(),
            _ => {
                return Err(OtError::TypeError {
                    expected: "List".into(),
                    got: obj_type_name(&subst_list[0]),
                });
            }
        };
        let mut type_pairs: Vec<(K::Type, NameId)> = Vec::new();
        for pair_obj in type_pairs_list {
            match pair_obj {
                OtObject::List(pair) if pair.len() == 2 => {
                    let old_name = match &pair[0] {
                        OtObject::Name(n) => {
                            let qualified = n.qualified();
                            self.names.intern(qualified)
                        }
                        _ => {
                            return Err(OtError::TypeError {
                                expected: "Name".into(),
                                got: obj_type_name(&pair[0]),
                            });
                        }
                    };
                    let new_ty = match &pair[1] {
                        OtObject::Type(t) => t.clone(),
                        _ => {
                            return Err(OtError::TypeError {
                                expected: "Type".into(),
                                got: obj_type_name(&pair[1]),
                            });
                        }
                    };
                    type_pairs.push((new_ty, old_name));
                }
                _ => {
                    return Err(OtError::ParseError(
                        "type substitution must be list of [Name, Type] pairs".into(),
                    ));
                }
            }
        }

        // Parse term substitutions: list of [Var, Term] pairs -> [(new_term, old_var)]
        // Per OpenTheory spec: pair[0] = Var (old var), pair[1] = Term (new term)
        let term_pairs_list = match &subst_list[1] {
            OtObject::List(l) => l.clone(),
            _ => {
                return Err(OtError::TypeError {
                    expected: "List".into(),
                    got: obj_type_name(&subst_list[1]),
                });
            }
        };
        let mut term_pairs: Vec<(K::Term, K::Term)> = Vec::new();
        for pair_obj in term_pairs_list {
            match pair_obj {
                OtObject::List(pair) if pair.len() == 2 => {
                    let old_var = match &pair[0] {
                        OtObject::Var(n, ty) => self.kernel.mk_var(*n, ty.clone()),
                        _ => {
                            return Err(OtError::TypeError {
                                expected: "Var".into(),
                                got: obj_type_name(&pair[0]),
                            });
                        }
                    };
                    let new_term = match &pair[1] {
                        OtObject::Term(t) => t.clone(),
                        OtObject::Var(n, ty) => self.kernel.mk_var(*n, ty.clone()),
                        _ => {
                            return Err(OtError::TypeError {
                                expected: "Term".into(),
                                got: obj_type_name(&pair[1]),
                            });
                        }
                    };
                    term_pairs.push((new_term, old_var));
                }
                _ => {
                    return Err(OtError::ParseError(
                        "term substitution must be list of [Var, Term] pairs".into(),
                    ));
                }
            }
        }

        // Apply type substitution first, then term substitution.
        let th = if type_pairs.is_empty() {
            th
        } else {
            self.kernel.inst_type_rule(&type_pairs, th)?
        };
        let th = if term_pairs.is_empty() {
            th
        } else {
            self.kernel.inst_rule(&term_pairs, th)?
        };

        self.stack.push(OtObject::Thm(th));
        Ok(())
    }

    // thm: Thm (Γ ⊦ ψ), List [t1,...,tn], Term φ -> (exported)
    fn cmd_thm(&mut self) -> Result<(), OtError> {
        let concl = self.pop_term()?;
        let hyps_list = self.pop_list()?;
        let th = self.pop_thm()?;

        // Verify: th.concl is alpha-equivalent to concl.
        let th_concl = self.kernel.concl(th.clone());
        if !self.kernel.aconv(th_concl, concl) {
            return Err(OtError::ParseError("thm: conclusion doesn't match".into()));
        }

        // Verify: hyps match (alpha-equivalently).
        let mut expected_hyps = Vec::new();
        for obj in hyps_list {
            match obj {
                OtObject::Term(t) => expected_hyps.push(t),
                _ => {
                    return Err(OtError::TypeError {
                        expected: "Term".into(),
                        got: obj_type_name(&obj),
                    });
                }
            }
        }

        let th_hyps = self.kernel.hyps(th.clone());
        for hyp in &th_hyps {
            if !expected_hyps
                .iter()
                .any(|e| self.kernel.aconv(hyp.clone(), e.clone()))
            {
                return Err(OtError::ParseError(
                    "thm: unexpected hypothesis in theorem".into(),
                ));
            }
        }
        self.theorems.push(th);
        Ok(())
    }

    // trans: Thm (Γ ⊦ t1 = t2), Thm (Δ ⊦ t2' = t3) -> Thm (Γ ∪ Δ ⊦ t1 = t3)
    fn cmd_trans(&mut self) -> Result<(), OtError> {
        let th2 = self.pop_thm()?;
        let th1 = self.pop_thm()?;
        let result = self.kernel.trans(th1, th2)?;
        self.stack.push(OtObject::Thm(result));
        Ok(())
    }

    // typeOp: Name n -> TypeOp
    fn cmd_type_op(&mut self) -> Result<(), OtError> {
        let name = self.pop_name()?;
        let id = self.intern_name(&name);
        self.stack.push(OtObject::TypeOp(id));
        Ok(())
    }

    // var: Name n, Type ty -> Var v
    fn cmd_var(&mut self) -> Result<(), OtError> {
        let ty = self.pop_type()?;
        let name = self.pop_name()?;
        let id = self.intern_name(&name);
        self.stack.push(OtObject::Var(id, ty));
        Ok(())
    }

    // varTerm: Var v -> Term v
    fn cmd_var_term(&mut self) -> Result<(), OtError> {
        let (name, ty) = self.pop_var()?;
        let tm = self.kernel.mk_var(name, ty);
        self.stack.push(OtObject::Term(tm));
        Ok(())
    }

    // varType: Name n -> Type (tyvar n)
    fn cmd_var_type(&mut self) -> Result<(), OtError> {
        let name = self.pop_name()?;
        let id = self.intern_name(&name);
        let ty = self.kernel.mk_tyvar(id);
        self.stack.push(OtObject::Type(ty));
        Ok(())
    }

    // version: Num k -> ()
    fn cmd_version(&mut self) -> Result<(), OtError> {
        let k = self.pop_num()?;
        self.version = k as u32;
        Ok(())
    }

    // --- Version 6+ commands ---

    // hdTl: List (h :: t) -> h, List t
    fn cmd_hd_tl(&mut self) -> Result<(), OtError> {
        let mut list = self.pop_list()?;
        if list.is_empty() {
            return Err(OtError::EmptyList);
        }
        let head = list.remove(0);
        self.stack.push(OtObject::List(list));
        self.stack.push(head);
        Ok(())
    }

    // pragma: x -> ()
    fn cmd_pragma(&mut self) -> Result<(), OtError> {
        self.pop()?;
        Ok(())
    }

    // proveHyp: Thm (Γ ⊦ φ), Thm (Δ ⊦ ψ) -> Thm (Γ ∪ (Δ - {φ}) ⊦ ψ)
    fn cmd_prove_hyp(&mut self) -> Result<(), OtError> {
        let th2 = self.pop_thm()?;
        let th1 = self.pop_thm()?;
        let iff_thm = self.kernel.deduct_antisym(th1.clone(), th2)?;
        let result = self.kernel.eq_mp(iff_thm, th1)?;
        self.stack.push(OtObject::Thm(result));
        Ok(())
    }

    // sym: Thm (Γ ⊦ t = u) -> Thm (Γ ⊦ u = t)
    fn cmd_sym(&mut self) -> Result<(), OtError> {
        let th = self.pop_thm()?;
        let concl = self.kernel.concl(th.clone());
        let (lhs, _rhs) = self.kernel.dest_eq(concl).ok_or(HolError::NotAnEquation)?;

        let lhs_ty = self.kernel.type_of(lhs.clone());
        let bool_ty = self.kernel.bool_type();
        let fun_lhs_bool = self.kernel.fun_type(lhs_ty.clone(), bool_ty);
        let eq_full_ty = self.kernel.fun_type(lhs_ty, fun_lhs_bool);
        let eq_const = self.kernel.mk_const(self.kernel.eq_id(), eq_full_ty);

        let refl_eq = self.kernel.refl(eq_const)?;
        let th1 = self.kernel.mk_comb_rule(refl_eq, th)?;
        let refl_t = self.kernel.refl(lhs)?;
        let th2 = self.kernel.mk_comb_rule(th1, refl_t.clone())?;
        let result = self.kernel.eq_mp(th2, refl_t)?;
        self.stack.push(OtObject::Thm(result));
        Ok(())
    }

    fn finish(self) -> ArticleResult<K> {
        ArticleResult {
            assumptions: self.assumptions,
            theorems: self.theorems,
        }
    }
}
