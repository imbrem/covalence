//! Foundations for S7's well-founded recursive model construction.
//!
//! This module owns the kernel-checked W0 least graph, W1 monotone fold, and
//! W2/W3 well-founded totality and determinacy bridges. It is deliberately not
//! connected to defun admission: the body compiler must still construct the
//! exact closure proofs, then W4–W6 must select the function and derive its
//! defining equation without adding authority.

use covalence_core::{Error, Result, Term, Type};
use covalence_hol_eval::EvalThm as Thm;
use covalence_hol_eval::derived::DerivedRules;

use crate::init::acl2::ordinal::ordinals;
use crate::init::eq::{beta_nf, beta_nf_concl};
use crate::init::ext::{TermExt, ThmExt};
use crate::init::logic::exists_elim;

fn bad(msg: impl Into<String>) -> Error {
    Error::ConnectiveRule(format!("acl2 wfrec: {}", msg.into()))
}

fn relation_at(relation: Term, xs: &[Term], result: Term) -> Result<Term> {
    let mut out = relation;
    for x in xs {
        out = out.apply(x.clone())?;
    }
    out.apply(result)
}

fn pointwise_imp(
    carrier: &Type,
    arity: usize,
    left: Term,
    right: Term,
    stem: &str,
) -> Result<Term> {
    let xs: Vec<_> = (0..arity)
        .map(|i| Term::free(format!("__{stem}x{i}"), carrier.clone()))
        .collect();
    let result = Term::free(format!("__{stem}a"), carrier.clone());
    let mut out =
        relation_at(left, &xs, result.clone())?.imp(relation_at(right, &xs, result.clone())?)?;
    out = out.forall(&format!("__{stem}a"), carrier.clone())?;
    for i in (0..arity).rev() {
        out = out.forall(&format!("__{stem}x{i}"), carrier.clone())?;
    }
    Ok(out)
}

/// A compiled collection of guarded, measured recursive call sites.
///
/// `step R x⃗ a` says that one evaluation of the recursive body at `x⃗`
/// returns `a` when recursive calls may use graph `R`.  Call-site compilation
/// must prove the transformer monotone.  That theorem is the exact property
/// needed to fold one body step into the impredicative least graph; neither
/// this wrapper nor monotonicity claims that the graph is total.
pub struct MeasuredCallSites {
    pub step: Term,
    pub closure: Term,
    pub monotone: Thm,
    relation_ty: Type,
    carrier: Type,
    arity: usize,
}

impl MeasuredCallSites {
    /// Validate a call-site transformer and its kernel theorem
    ///
    /// `⊢ ∀R S. (R ⊆ S) ⟹ (step R ⊆ step S)`.
    ///
    /// The future syntax compiler supplies this theorem by structural
    /// composition of guarded call sites, including their decrease evidence.
    pub fn new(carrier: &Type, arity: usize, step: Term, monotone: Thm) -> Result<Self> {
        let relation_ty = relation_type(carrier, arity)?;
        let want_step_ty = Type::fun(relation_ty.clone(), relation_ty.clone());
        if step.ty().ok() != Some(&want_step_ty) {
            return Err(bad(format!(
                "call-site step has type {}, expected {want_step_ty}",
                step.ty().map_err(|e| bad(format!("{e:?}")))?
            )));
        }

        let r = Term::free("__cmR", relation_ty.clone());
        let s = Term::free("__cmS", relation_ty.clone());
        let subset = pointwise_imp(carrier, arity, r.clone(), s.clone(), "cmsub")?;
        let step_subset = pointwise_imp(
            carrier,
            arity,
            step.clone().apply(r.clone())?,
            step.clone().apply(s.clone())?,
            "cmstep",
        )?;
        let expected = subset
            .imp(step_subset)?
            .forall("__cmS", relation_ty.clone())?
            .forall("__cmR", relation_ty.clone())?;
        if !monotone.hyps().is_empty() || monotone.concl() != &expected {
            return Err(bad(
                "call-site monotonicity theorem has hypotheses or the wrong statement",
            ));
        }

        let q = Term::free("__ccR", relation_ty.clone());
        let closed = pointwise_imp(
            carrier,
            arity,
            step.clone().apply(q.clone())?,
            q,
            "cmclosed",
        )?;
        let closure = Term::abs(
            relation_ty.clone(),
            covalence_core::subst::close(&closed, "__ccR"),
        );
        Ok(Self {
            step,
            closure,
            monotone,
            relation_ty,
            carrier: carrier.clone(),
            arity,
        })
    }

    /// Define the W0 least graph for these call sites.
    pub fn define_graph(&self, name: &str) -> Result<LeastGraph> {
        define_least_graph(name, &self.carrier, self.arity, self.closure.clone())
    }

    /// The closure proposition instantiated at `relation`.
    pub fn closed_at(&self, relation: Term) -> Result<Term> {
        if relation.ty().ok() != Some(&self.relation_ty) {
            return Err(bad("closure relation has the wrong type"));
        }
        let normalized = beta_nf(self.closure.clone().apply(relation)?);
        Ok(normalized
            .concl()
            .as_eq()
            .ok_or(Error::NotAnEquation)?
            .1
            .clone())
    }

    /// W1 fold/closure: `step G x⃗ a ⟹ G x⃗ a`.
    ///
    /// This is derived solely from W0 elimination and the supplied monotonicity
    /// theorem.  In particular it does not use choice or assume existence.
    pub fn fold_at(
        &self,
        graph: &LeastGraph,
        xs: &[Term],
        result: Term,
        body_step: Thm,
    ) -> Result<Thm> {
        if graph.relation_ty != self.relation_ty
            || graph.arity != self.arity
            || graph.carrier != self.carrier
            || graph.closure != self.closure
        {
            return Err(bad("least graph does not belong to these call sites"));
        }
        let expected_step = relation_at(
            self.step.clone().apply(graph.graph.clone())?,
            xs,
            result.clone(),
        )?;
        if body_step.concl() != &expected_step {
            return Err(bad("fold premise is not a body step at this graph point"));
        }

        // For arbitrary closed S, W0 elimination proves G ⊆ S.
        let s = Term::free("__foldS", self.relation_ty.clone());
        let closed_s = self.closed_at(s.clone())?;
        let hclosed = Thm::assume(closed_s.clone())?;
        let ys: Vec<_> = (0..self.arity)
            .map(|i| Term::free(format!("__foldy{i}"), self.carrier.clone()))
            .collect();
        let b = Term::free("__foldb", self.carrier.clone());
        let gyb = graph.at(&ys, b.clone())?;
        let subset_step = graph
            .elim(
                &ys,
                b.clone(),
                Thm::assume(gyb.clone())?,
                s.clone(),
                hclosed.clone(),
            )?
            .imp_intro(&gyb)?
            .all_intro("__foldb", self.carrier.clone())?;
        let mut g_subset_s = subset_step;
        for i in (0..self.arity).rev() {
            g_subset_s = g_subset_s.all_intro(&format!("__foldy{i}"), self.carrier.clone())?;
        }

        // Monotonicity transports the body step from G to S; closure of S
        // then yields S x⃗ a.
        let mut mono = beta_nf_concl(
            self.monotone
                .clone()
                .all_elim(graph.graph.clone())?
                .all_elim(s.clone())?
                .imp_elim(g_subset_s)?,
        )?;
        for x in xs {
            mono = mono.all_elim(x.clone())?;
        }
        mono = mono.all_elim(result.clone())?;
        let step_s = mono.imp_elim(beta_nf_concl(body_step.clone())?)?;

        let mut close_point = hclosed;
        for x in xs {
            close_point = close_point.all_elim(x.clone())?;
        }
        close_point = close_point.all_elim(result.clone())?;
        let sx = close_point.imp_elim(step_s)?;
        let rhs = sx
            .imp_intro(&closed_s)?
            .all_intro("__foldS", self.relation_ty.clone())?;
        graph.intro(xs, result, beta_nf_concl(rhs)?)
    }

    /// Closed W1 theorem:
    /// `⊢ ∀x⃗ a. step G x⃗ a ⟹ G x⃗ a`.
    pub fn fold(&self, graph: &LeastGraph) -> Result<Thm> {
        let xs: Vec<_> = (0..self.arity)
            .map(|i| Term::free(format!("__foldx{i}"), self.carrier.clone()))
            .collect();
        let result = Term::free("__folda", self.carrier.clone());
        let step_at = relation_at(
            self.step.clone().apply(graph.graph.clone())?,
            &xs,
            result.clone(),
        )?;
        let mut theorem = self
            .fold_at(graph, &xs, result, Thm::assume(step_at.clone())?)?
            .imp_intro(&step_at)?
            .all_intro("__folda", self.carrier.clone())?;
        for i in (0..self.arity).rev() {
            theorem = theorem.all_intro(&format!("__foldx{i}"), self.carrier.clone())?;
        }
        Ok(theorem)
    }
}

/// One concrete guarded recursive call after ACL2 ruler analysis.
///
/// The terms may contain the surrounding body's free formals.  `decrease`
/// must be a closed kernel theorem of
/// `guard ⟹ below (measure recursive_args) (measure current_args)`.
/// Keeping this evidence beside the call prevents a later body compiler from
/// silently treating an unmeasured occurrence as recursive.
pub struct GuardedMeasuredCall {
    pub guard: Term,
    pub arguments: Vec<Term>,
    pub decrease: Thm,
}

impl GuardedMeasuredCall {
    pub fn new(
        scaffold: &MeasuredTotality,
        current_args: &[Term],
        guard: Term,
        arguments: Vec<Term>,
        decrease: Thm,
    ) -> Result<Self> {
        scaffold.check_inputs(current_args)?;
        scaffold.check_inputs(&arguments)?;
        if guard.ty().ok() != Some(&Type::bool()) {
            return Err(bad("recursive-call guard is not boolean"));
        }
        let o = ordinals()?;
        let smaller = o
            .below
            .clone()
            .apply(scaffold.measure_at(&arguments)?)?
            .apply(scaffold.measure_at(current_args)?)?;
        let expected = guard.clone().imp(smaller)?;
        let decrease = beta_nf_concl(decrease)?;
        let expected = beta_nf(expected)
            .concl()
            .as_eq()
            .ok_or(Error::NotAnEquation)?
            .1
            .clone();
        if !decrease.hyps().is_empty() || decrease.concl() != &expected {
            return Err(bad(
                "recursive-call decrease theorem has hypotheses or the wrong statement",
            ));
        }
        Ok(Self {
            guard,
            arguments,
            decrease,
        })
    }
}

/// Kernel-checked totality bridge for a measured graph.
///
/// `measure_valid` proves every input's measure is an ordinal notation.  The
/// remaining caller obligation is exactly the `wf_induct` closure step for the
/// generated motive.  Concrete [`GuardedMeasuredCall`] values provide the
/// decrease facts used while proving that step.
pub struct MeasuredTotality {
    pub measure: Term,
    pub measure_valid: Thm,
    carrier: Type,
    arity: usize,
}

impl MeasuredTotality {
    pub fn new(carrier: &Type, arity: usize, measure: Term, measure_valid: Thm) -> Result<Self> {
        let o = ordinals()?;
        if carrier != &o.th.ty {
            return Err(bad("measured recursion carrier is not the ACL2 carrier"));
        }
        let mut want_measure_ty = carrier.clone();
        for _ in 0..arity {
            want_measure_ty = Type::fun(carrier.clone(), want_measure_ty);
        }
        if arity == 0 || measure.ty().ok() != Some(&want_measure_ty) {
            return Err(bad("measure has the wrong input shape"));
        }
        let xs: Vec<_> = (0..arity)
            .map(|i| Term::free(format!("__mvalidx{i}"), carrier.clone()))
            .collect();
        let measure_at = apply_inputs(measure.clone(), &xs)?;
        let mut expected =
            o.op.clone()
                .apply(measure_at)?
                .equals(o.th.nil.clone())?
                .not()?;
        for i in (0..arity).rev() {
            expected = expected.forall(&format!("__mvalidx{i}"), carrier.clone())?;
        }
        let measure_valid = beta_nf_concl(measure_valid)?;
        let expected = beta_nf(expected)
            .concl()
            .as_eq()
            .ok_or(Error::NotAnEquation)?
            .1
            .clone();
        if !measure_valid.hyps().is_empty() || measure_valid.concl() != &expected {
            return Err(bad(
                "measure-validity theorem has hypotheses or the wrong statement",
            ));
        }
        Ok(Self {
            measure,
            measure_valid,
            carrier: carrier.clone(),
            arity,
        })
    }

    fn check_inputs(&self, xs: &[Term]) -> Result<()> {
        if xs.len() != self.arity || xs.iter().any(|x| x.ty().ok() != Some(&self.carrier)) {
            return Err(bad("measured input tuple has the wrong shape"));
        }
        Ok(())
    }

    pub fn measure_at(&self, xs: &[Term]) -> Result<Term> {
        self.check_inputs(xs)?;
        apply_inputs(self.measure.clone(), xs)
    }

    fn motive(&self, graph: &LeastGraph) -> Result<Term> {
        if graph.carrier != self.carrier || graph.arity != self.arity {
            return Err(bad("totality graph has the wrong input shape"));
        }
        let z = Term::free("__mtz", self.carrier.clone());
        let xs: Vec<_> = (0..self.arity)
            .map(|i| Term::free(format!("__mtx{i}"), self.carrier.clone()))
            .collect();
        let result = Term::free("__mta", self.carrier.clone());
        let exists = graph
            .at(&xs, result.clone())?
            .exists("__mta", self.carrier.clone())?;
        let mut body = self.measure_at(&xs)?.equals(z.clone())?.imp(exists)?;
        for i in (0..self.arity).rev() {
            body = body.forall(&format!("__mtx{i}"), self.carrier.clone())?;
        }
        Ok(Term::abs(
            self.carrier.clone(),
            covalence_core::subst::close(&body, "__mtz"),
        ))
    }

    fn determinacy_motive(&self, graph: &LeastGraph) -> Result<Term> {
        if graph.carrier != self.carrier || graph.arity != self.arity {
            return Err(bad("determinacy graph has the wrong input shape"));
        }
        let z = Term::free("__mdz", self.carrier.clone());
        let xs: Vec<_> = (0..self.arity)
            .map(|i| Term::free(format!("__mdx{i}"), self.carrier.clone()))
            .collect();
        let a = Term::free("__mda", self.carrier.clone());
        let b = Term::free("__mdb", self.carrier.clone());
        let ga = graph.at(&xs, a.clone())?;
        let gb = graph.at(&xs, b.clone())?;
        let mut unique = ga.imp(gb.imp(a.equals(b)?)?)?;
        unique = unique.forall("__mdb", self.carrier.clone())?;
        unique = unique.forall("__mda", self.carrier.clone())?;
        let mut body = self.measure_at(&xs)?.equals(z.clone())?.imp(unique)?;
        for i in (0..self.arity).rev() {
            body = body.forall(&format!("__mdx{i}"), self.carrier.clone())?;
        }
        Ok(Term::abs(
            self.carrier.clone(),
            covalence_core::subst::close(&body, "__mdz"),
        ))
    }

    /// The exact theorem a body-totality compiler must prove:
    /// `∀z. (∀y. below y z ⟹ P y) ⟹ P z`, where
    /// `P z ≡ ∀x⃗. measure x⃗ = z ⟹ ∃a. G x⃗ a`.
    pub fn closure_goal(&self, graph: &LeastGraph) -> Result<Term> {
        let o = ordinals()?;
        let motive = self.motive(graph)?;
        let z = Term::free("__mtcz", self.carrier.clone());
        let y = Term::free("__mtcy", self.carrier.clone());
        let ih = o
            .below
            .clone()
            .apply(y.clone())?
            .apply(z.clone())?
            .imp(motive.clone().apply(y)?)?
            .forall("__mtcy", self.carrier.clone())?;
        ih.imp(motive.apply(z)?)?
            .forall("__mtcz", self.carrier.clone())
    }

    /// The exact W3 body-determinacy theorem:
    /// `∀z. (∀y. below y z ⟹ D y) ⟹ D z`, where `D z` says that every
    /// graph result at inputs whose measure is `z` is unique.
    ///
    /// A future recursive-body compiler proves this proposition structurally:
    /// guarded recursive calls obtain uniqueness from the induction
    /// hypothesis, while nonrecursive operators preserve equality.
    pub fn determinacy_closure_goal(&self, graph: &LeastGraph) -> Result<Term> {
        let o = ordinals()?;
        let motive = self.determinacy_motive(graph)?;
        let z = Term::free("__mdcz", self.carrier.clone());
        let y = Term::free("__mdcy", self.carrier.clone());
        let ih = o
            .below
            .clone()
            .apply(y.clone())?
            .apply(z.clone())?
            .imp(motive.clone().apply(y)?)?
            .forall("__mdcy", self.carrier.clone())?;
        ih.imp(motive.apply(z)?)?
            .forall("__mdcz", self.carrier.clone())
    }

    /// W2 totality scaffold.  Given the exact closure theorem above, derive
    /// `⊢ ∀x⃗. ∃a. G x⃗ a` through the existing full-ε₀ `wf_induct`.
    pub fn prove_totality(&self, graph: &LeastGraph, closure: Thm) -> Result<Thm> {
        let expected = self.closure_goal(graph)?;
        let expected_nf = beta_nf(expected.clone());
        let closure = beta_nf_concl(closure)?;
        if !closure.hyps().is_empty()
            || closure.concl() != expected_nf.concl().as_eq().ok_or(Error::NotAnEquation)?.1
        {
            return Err(bad(
                "body-totality theorem has hypotheses or the wrong wf closure statement",
            ));
        }
        let closure = expected_nf.sym()?.eq_mp(closure)?;
        let o = ordinals()?;
        let motive = self.motive(graph)?;
        let induction = beta_nf_concl(o.wf_induct()?.all_elim(motive)?.imp_elim(closure)?)?;

        let xs: Vec<_> = (0..self.arity)
            .map(|i| Term::free(format!("__totalx{i}"), self.carrier.clone()))
            .collect();
        let measure_at = self.measure_at(&xs)?;
        let mut valid = self.measure_valid.clone();
        for x in &xs {
            valid = valid.all_elim(x.clone())?;
        }
        let at_ordinal = beta_nf_concl(induction.all_elim(measure_at.clone())?)?;
        let mut at_measure = beta_nf_concl(at_ordinal.imp_elim(valid)?)?;
        for x in &xs {
            at_measure = at_measure.all_elim(x.clone())?;
        }
        let measure_nf = beta_nf(measure_at)
            .concl()
            .as_eq()
            .ok_or(Error::NotAnEquation)?
            .1
            .clone();
        let exists = at_measure.imp_elim(Thm::refl(measure_nf)?)?;
        let mut total = exists;
        for i in (0..self.arity).rev() {
            total = total.all_intro(&format!("__totalx{i}"), self.carrier.clone())?;
        }
        Ok(total)
    }

    /// W3 determinacy. Given precisely [`Self::determinacy_closure_goal`],
    /// derive
    /// `⊢ ∀x⃗ a b. G x⃗ a ⟹ G x⃗ b ⟹ a = b`
    /// through the existing full-ε₀ well-founded induction theorem.
    ///
    /// This method deliberately accepts neither a theorem with hypotheses nor
    /// a merely propositionally related statement. It creates no admission
    /// authority: the recursive body's generated closure remains an explicit
    /// kernel proof obligation.
    pub fn prove_determinacy(&self, graph: &LeastGraph, closure: Thm) -> Result<Thm> {
        let expected = self.determinacy_closure_goal(graph)?;
        let expected_nf = beta_nf(expected.clone());
        let closure = beta_nf_concl(closure)?;
        if !closure.hyps().is_empty()
            || closure.concl() != expected_nf.concl().as_eq().ok_or(Error::NotAnEquation)?.1
        {
            return Err(bad(
                "body-determinacy theorem has hypotheses or the wrong wf closure statement",
            ));
        }
        let closure = expected_nf.sym()?.eq_mp(closure)?;
        let o = ordinals()?;
        let motive = self.determinacy_motive(graph)?;
        let induction = beta_nf_concl(o.wf_induct()?.all_elim(motive)?.imp_elim(closure)?)?;

        let xs: Vec<_> = (0..self.arity)
            .map(|i| Term::free(format!("__detx{i}"), self.carrier.clone()))
            .collect();
        let measure_at = self.measure_at(&xs)?;
        let mut valid = self.measure_valid.clone();
        for x in &xs {
            valid = valid.all_elim(x.clone())?;
        }
        let at_ordinal = beta_nf_concl(induction.all_elim(measure_at.clone())?)?;
        let mut at_measure = beta_nf_concl(at_ordinal.imp_elim(valid)?)?;
        for x in &xs {
            at_measure = at_measure.all_elim(x.clone())?;
        }
        let measure_nf = beta_nf(measure_at)
            .concl()
            .as_eq()
            .ok_or(Error::NotAnEquation)?
            .1
            .clone();
        let mut deterministic = at_measure.imp_elim(Thm::refl(measure_nf)?)?;
        for i in (0..self.arity).rev() {
            deterministic = deterministic.all_intro(&format!("__detx{i}"), self.carrier.clone())?;
        }
        Ok(deterministic)
    }
}

fn apply_inputs(mut function: Term, xs: &[Term]) -> Result<Term> {
    for x in xs {
        function = function.apply(x.clone())?;
    }
    Ok(function)
}

/// The relation type `A → ... → A → bool` for `arity` inputs and one result.
pub fn relation_type(carrier: &Type, arity: usize) -> Result<Type> {
    if arity == 0 {
        return Err(bad("recursive functions must have at least one formal"));
    }
    let mut ty = Type::bool();
    for _ in 0..=arity {
        ty = Type::fun(carrier.clone(), ty);
    }
    Ok(ty)
}

/// W0's defined least graph and its conservative defining theorem.
pub struct LeastGraph {
    /// `G : A → ... → A → bool`.
    pub graph: Term,
    /// `⊢ G = λx⃗ a. ∀S. closure S ⟹ S x⃗ a`.
    pub def_eq: Thm,
    /// The relation carrier used by the quantified `S`.
    pub relation_ty: Type,
    carrier: Type,
    arity: usize,
    closure: Term,
}

impl LeastGraph {
    /// `G x⃗ a`.
    pub fn at(&self, xs: &[Term], a: Term) -> Result<Term> {
        if xs.len() != self.arity || xs.iter().any(|x| x.ty().ok() != Some(&self.carrier)) {
            return Err(bad("graph application has the wrong input shape"));
        }
        if a.ty().ok() != Some(&self.carrier) {
            return Err(bad("graph result has the wrong carrier type"));
        }
        let mut out = self.graph.clone();
        for x in xs {
            out = out.apply(x.clone())?;
        }
        out.apply(a)
    }

    /// The defining equation at one graph point:
    /// `⊢ G x⃗ a = (∀S. closure S ⟹ S x⃗ a)`.
    pub fn unfold_at(&self, xs: &[Term], a: Term) -> Result<Thm> {
        if xs.len() != self.arity {
            return Err(bad("graph unfold has the wrong arity"));
        }
        let mut eq = self.def_eq.clone();
        for x in xs {
            eq = eq.cong_fn(x.clone())?;
        }
        eq.cong_fn(a)?.rhs_conv(|t| Ok(beta_nf(t.clone())))
    }

    /// Fold a proof of the impredicative RHS into `G x⃗ a`.
    pub fn intro(&self, xs: &[Term], a: Term, rhs: Thm) -> Result<Thm> {
        let eq = self.unfold_at(xs, a)?;
        let (_, want) = eq.concl().as_eq().ok_or(Error::NotAnEquation)?;
        if rhs.concl() != want {
            return Err(bad(format!(
                "graph intro theorem does not state the unfolded RHS: got {}, want {want}",
                rhs.concl()
            )));
        }
        eq.sym()?.eq_mp(rhs)
    }

    /// W0 elimination: from `G x⃗ a` and `closure S`, derive `S x⃗ a`.
    pub fn elim(&self, xs: &[Term], a: Term, graph: Thm, s: Term, closed: Thm) -> Result<Thm> {
        if graph.concl() != &self.at(xs, a.clone())? {
            return Err(bad("graph elimination premise has the wrong graph point"));
        }
        if s.ty().ok() != Some(&self.relation_ty) {
            return Err(bad("graph elimination relation has the wrong type"));
        }
        let want_closed = beta_nf(self.closure.clone().apply(s.clone())?);
        let normalized = want_closed.concl().as_eq().ok_or(Error::NotAnEquation)?.1;
        if closed.concl() != normalized {
            return Err(bad(
                "graph elimination closure theorem has the wrong statement",
            ));
        }
        self.unfold_at(xs, a)?
            .eq_mp(graph)?
            .all_elim(s)?
            .imp_elim(closed)
    }

    /// Pointwise W6 choice: from `∃a. G x⃗ a`, derive
    /// `G x⃗ (εa. G x⃗ a)`. Choice only selects from the caller-proved
    /// nonempty graph; it creates no existence fact.
    pub fn choose_at(&self, xs: &[Term], total: Thm) -> Result<(Term, Thm)> {
        let w = Term::free("__gw", self.carrier.clone());
        let gw = self.at(xs, w.clone())?;
        let pred = Term::abs(
            self.carrier.clone(),
            covalence_core::subst::close(&gw, "__gw"),
        );
        let expected = gw.clone().exists("__gw", self.carrier.clone())?;
        if total.concl() != &expected {
            return Err(bad("choice premise is not existence at this graph point"));
        }
        let chosen = Term::app(Term::select_op(self.carrier.clone()), pred.clone());
        let goal = self.at(xs, chosen.clone())?;
        let goal_redex = pred.clone().apply(chosen.clone())?;
        let hyp = pred.clone().apply(w.clone())?;
        let step = Thm::select_ax(pred, w.clone())?
            .imp_elim(Thm::assume(hyp.clone())?)?
            .imp_intro(&hyp)?
            .all_intro("__gw", self.carrier.clone())?;
        let selected = exists_elim(total, goal_redex.clone(), step)?;
        let proved = Thm::beta_conv(goal_redex)?.eq_mp(selected)?;
        if proved.concl() != &goal {
            return Err(bad(
                "choice beta-normalization drifted from the graph point",
            ));
        }
        Ok((chosen, proved))
    }

    /// W4 pointwise unique choice. From totality at `x⃗` and the closed W3
    /// determinacy theorem, select `a₀ = εa. G x⃗ a` and derive both
    /// `G x⃗ a₀` and `∀a. G x⃗ a ⟹ a = a₀`.
    ///
    /// The returned term is not installed as a recursive definition; W5/W6
    /// must still assemble the selected function and prove its body equation.
    pub fn choose_unique_at(
        &self,
        xs: &[Term],
        total: Thm,
        determinacy: Thm,
    ) -> Result<(Term, Thm, Thm)> {
        if !determinacy.hyps().is_empty() {
            return Err(bad("determinacy theorem has hypotheses"));
        }
        let (chosen, selected) = self.choose_at(xs, total)?;
        let a = Term::free("__gua", self.carrier.clone());
        let ga = self.at(xs, a.clone())?;
        let mut point = determinacy;
        for x in xs {
            point = point.all_elim(x.clone())?;
        }
        point = point.all_elim(a.clone())?.all_elim(chosen.clone())?;
        let expected = ga.clone().imp(
            self.at(xs, chosen.clone())?
                .imp(a.clone().equals(chosen.clone())?)?,
        )?;
        if point.concl() != &expected {
            return Err(bad("determinacy theorem has the wrong statement"));
        }
        let unique = point
            .imp_elim(Thm::assume(ga.clone())?)?
            .imp_elim(selected.clone())?
            .imp_intro(&ga)?
            .all_intro("__gua", self.carrier.clone())?;
        Ok((chosen, selected, unique))
    }
}

/// Define W0:
/// `G x⃗ a ≜ ∀S. closure S ⟹ S x⃗ a`.
///
/// `closure` is supplied as a term of type `(A → ... → A → bool) → bool`;
/// later stages build it from the measured body's guarded call sites. All
/// validation occurs before `Thm::define`, so a rejected shape mints nothing.
pub fn define_least_graph(
    name: &str,
    carrier: &Type,
    arity: usize,
    closure: Term,
) -> Result<LeastGraph> {
    let relation_ty = relation_type(carrier, arity)?;
    let want = Type::fun(relation_ty.clone(), Type::bool());
    let got = closure.ty().map_err(|e| bad(format!("{e:?}")))?;
    if got != &want {
        return Err(bad(format!("closure has type {}, expected {want}", got)));
    }
    if name.is_empty() {
        return Err(bad("graph definition name is empty"));
    }

    let xs: Vec<Term> = (0..arity)
        .map(|i| Term::free(format!("__gx{i}"), carrier.clone()))
        .collect();
    let a = Term::free("__ga", carrier.clone());
    let s = Term::free("__gS", relation_ty.clone());
    let mut related = s.clone();
    for x in &xs {
        related = related.apply(x.clone())?;
    }
    related = related.apply(a.clone())?;
    let body = closure
        .clone()
        .apply(s.clone())?
        .imp(related)?
        .forall("__gS", relation_ty.clone())?;
    let mut rhs = Term::abs(carrier.clone(), covalence_core::subst::close(&body, "__ga"));
    for i in (0..arity).rev() {
        rhs = Term::abs(
            carrier.clone(),
            covalence_core::subst::close(&rhs, format!("__gx{i}").as_str()),
        );
    }
    let def_eq = Thm::define(name, rhs)?;
    let graph = def_eq
        .concl()
        .as_eq()
        .ok_or(Error::NotAnEquation)?
        .0
        .clone();
    Ok(LeastGraph {
        graph,
        def_eq,
        relation_ty,
        carrier: carrier.clone(),
        arity,
        closure,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::init::logic::exists_intro;
    use covalence_hol_eval::{fal_from_lit, mk_bool, mk_int};

    fn truth() -> Term {
        let n = Term::free("__truth_n", Type::nat());
        n.clone().equals(n).unwrap()
    }

    fn identity_call_sites(carrier: &Type, arity: usize) -> MeasuredCallSites {
        let rel = relation_type(carrier, arity).unwrap();
        let r_body = Term::free("__idR", rel.clone());
        let step = Term::abs(rel.clone(), covalence_core::subst::close(&r_body, "__idR"));

        let r = Term::free("__cmR", rel.clone());
        let s = Term::free("__cmS", rel.clone());
        let subset = pointwise_imp(carrier, arity, r.clone(), s.clone(), "cmsub").unwrap();
        let step_subset = pointwise_imp(
            carrier,
            arity,
            step.clone().apply(r.clone()).unwrap(),
            step.clone().apply(s.clone()).unwrap(),
            "cmstep",
        )
        .unwrap();
        let h = Thm::assume(subset.clone()).unwrap();
        let normalized = beta_nf(step_subset.clone());
        assert_eq!(normalized.concl().as_eq().unwrap().1, &subset);
        let lifted = normalized.sym().unwrap().eq_mp(h).unwrap();
        let monotone = lifted
            .imp_intro(&subset)
            .unwrap()
            .all_intro("__cmS", rel.clone())
            .unwrap()
            .all_intro("__cmR", rel)
            .unwrap();
        MeasuredCallSites::new(carrier, arity, step, monotone).unwrap()
    }

    fn constant_unary_call_sites(carrier: &Type) -> MeasuredCallSites {
        let rel = relation_type(carrier, 1).unwrap();
        let a = Term::free("__consta", carrier.clone());
        let body = a.clone().equals(a).unwrap();
        let body = Term::abs(
            carrier.clone(),
            covalence_core::subst::close(&body, "__consta"),
        );
        let body = Term::abs(carrier.clone(), body);
        let step = Term::abs(rel.clone(), body);

        let r = Term::free("__cmR", rel.clone());
        let s = Term::free("__cmS", rel.clone());
        let subset = pointwise_imp(carrier, 1, r.clone(), s.clone(), "cmsub").unwrap();
        let step_subset = pointwise_imp(
            carrier,
            1,
            step.clone().apply(r.clone()).unwrap(),
            step.clone().apply(s.clone()).unwrap(),
            "cmstep",
        )
        .unwrap();
        let a = Term::free("__cmstepa", carrier.clone());
        let lhs = a.clone().equals(a.clone()).unwrap();
        let normalized = Thm::refl(a)
            .unwrap()
            .imp_intro(&lhs)
            .unwrap()
            .all_intro("__cmstepa", carrier.clone())
            .unwrap()
            .all_intro("__cmstepx0", carrier.clone())
            .unwrap();
        let lifted = beta_nf(step_subset)
            .sym()
            .unwrap()
            .eq_mp(normalized)
            .unwrap();
        let monotone = lifted
            .imp_intro(&subset)
            .unwrap()
            .all_intro("__cmS", rel.clone())
            .unwrap()
            .all_intro("__cmR", rel)
            .unwrap();
        MeasuredCallSites::new(carrier, 1, step, monotone).unwrap()
    }

    fn constant_one_scaffold() -> MeasuredTotality {
        let o = ordinals().unwrap();
        let carrier = o.th.ty.clone();
        let one = o.th.aint_at(&mk_int(1i64)).unwrap();
        let measure = Term::abs(carrier.clone(), one.clone());
        let op_one = o.op.clone().apply(one).unwrap();
        let folded_op = o.ord_fold(&op_one).unwrap();
        let v = Term::free("__opv", carrier.clone());
        let nonnil_pred = Term::abs(
            carrier.clone(),
            covalence_core::subst::close(
                &v.equals(o.th.nil.clone()).unwrap().not().unwrap(),
                "__opv",
            ),
        );
        let pred_t = nonnil_pred.clone().apply(o.pr.t.clone()).unwrap();
        let t_ne_nil_redex = beta_nf(pred_t)
            .sym()
            .unwrap()
            .eq_mp(o.pr.t_ne_nil().unwrap())
            .unwrap();
        let valid_one = folded_op
            .cong_arg(nonnil_pred)
            .unwrap()
            .sym()
            .unwrap()
            .eq_mp(t_ne_nil_redex)
            .unwrap()
            .all_intro("__mvalidx0", carrier.clone())
            .unwrap();
        MeasuredTotality::new(&carrier, 1, measure, valid_one).unwrap()
    }

    #[test]
    fn w0_defines_exact_least_graph_without_hypotheses() {
        let a = Type::nat();
        let rel = relation_type(&a, 2).unwrap();
        let closure = Term::abs(rel.clone(), covalence_core::subst::close(&truth(), "S"));
        let g = define_least_graph("acl2.wfrec.test.graph", &a, 2, closure).unwrap();
        assert!(g.def_eq.hyps().is_empty());
        assert_eq!(g.relation_ty, rel);
        assert_eq!(
            g.graph.ty().unwrap(),
            &Type::fun(a.clone(), Type::fun(a.clone(), Type::fun(a, Type::bool())))
        );
    }

    #[test]
    fn w0_rejects_bad_shapes_before_defining() {
        let a = Type::nat();
        assert!(relation_type(&a, 0).is_err());
        assert!(define_least_graph("acl2.wfrec.bad.graph", &a, 1, truth(),).is_err());
        assert!(
            define_least_graph(
                "",
                &a,
                1,
                Term::abs(relation_type(&a, 1).unwrap(), truth(),),
            )
            .is_err()
        );
    }

    #[test]
    fn w0_intro_and_elimination_are_kernel_checked() {
        let a_ty = Type::nat();
        let rel = relation_type(&a_ty, 1).unwrap();
        let x0 = Term::free("x0", a_ty.clone());
        let a0 = Term::free("a0", a_ty.clone());
        let s = Term::free("S", rel.clone());
        let s_xa = s
            .clone()
            .apply(x0.clone())
            .unwrap()
            .apply(a0.clone())
            .unwrap();
        let closure = Term::abs(rel.clone(), covalence_core::subst::close(&s_xa, "S"));
        let g = define_least_graph("acl2.wfrec.test.intro", &a_ty, 1, closure.clone()).unwrap();

        // ∀S. closure S ⇒ S x0 a0 is the identity proof after β-reduction.
        let cs = s_xa.clone();
        let h = Thm::assume(cs.clone()).unwrap();
        let rhs = h
            .imp_intro(&cs)
            .unwrap()
            .all_intro("S", rel.clone())
            .unwrap();
        let hg = g.intro(std::slice::from_ref(&x0), a0.clone(), rhs).unwrap();
        assert!(hg.hyps().is_empty());
        assert_eq!(
            hg.concl(),
            &g.at(std::slice::from_ref(&x0), a0.clone()).unwrap()
        );

        let r = Term::free("R", rel);
        let cr_nf = beta_nf(closure.apply(r.clone()).unwrap());
        let cr = cr_nf.concl().as_eq().unwrap().1.clone();
        let got = g
            .elim(
                std::slice::from_ref(&x0),
                a0.clone(),
                hg.clone(),
                r.clone(),
                Thm::assume(cr.clone()).unwrap(),
            )
            .unwrap();
        assert_eq!(
            got.concl(),
            &r.clone()
                .apply(x0.clone())
                .unwrap()
                .apply(a0.clone())
                .unwrap()
        );
        assert_eq!(got.hyps().len(), 1);
        assert!(got.hyps().contains(&cr));

        let gw = g.at(std::slice::from_ref(&x0), a0.clone()).unwrap();
        let pred = Term::abs(a_ty.clone(), covalence_core::subst::close(&gw, "a0"));
        let redex = pred.clone().apply(a0.clone()).unwrap();
        let at_pred = Thm::beta_conv(redex)
            .unwrap()
            .sym()
            .unwrap()
            .eq_mp(hg)
            .unwrap();
        let total = exists_intro(pred, a0.clone(), at_pred).unwrap();
        let (chosen, selected) = g.choose_at(std::slice::from_ref(&x0), total).unwrap();
        assert!(selected.hyps().is_empty());
        assert_eq!(
            selected.concl(),
            &g.at(std::slice::from_ref(&x0), chosen).unwrap()
        );

        // Wrong graph points and wrong closure evidence fail closed.
        let other = Term::free("other", a_ty);
        let fake = Thm::assume(g.at(std::slice::from_ref(&other), a0.clone()).unwrap()).unwrap();
        assert!(
            g.elim(
                std::slice::from_ref(&x0),
                a0,
                fake,
                r,
                Thm::assume(cr).unwrap(),
            )
            .is_err()
        );
    }

    #[test]
    fn w1_monotone_call_sites_fold_into_the_least_graph() {
        let carrier = Type::nat();
        let calls = identity_call_sites(&carrier, 2);
        let graph = calls.define_graph("acl2.wfrec.test.monotone-fold").unwrap();
        let x = Term::free("fold_x", carrier.clone());
        let y = Term::free("fold_y", carrier.clone());
        let a = Term::free("fold_a", carrier);
        let xs = [x, y];
        let step_at = relation_at(
            calls.step.clone().apply(graph.graph.clone()).unwrap(),
            &xs,
            a.clone(),
        )
        .unwrap();
        let folded = calls
            .fold_at(
                &graph,
                &xs,
                a.clone(),
                Thm::assume(step_at.clone()).unwrap(),
            )
            .unwrap();
        assert_eq!(folded.concl(), &graph.at(&xs, a.clone()).unwrap());
        assert_eq!(folded.hyps().len(), 1);
        assert!(folded.hyps().contains(&step_at));

        let mut closed_fold = calls.fold(&graph).unwrap();
        assert!(closed_fold.hyps().is_empty());
        for x in &xs {
            closed_fold = closed_fold.all_elim(x.clone()).unwrap();
        }
        closed_fold = closed_fold.all_elim(a.clone()).unwrap();
        assert_eq!(
            closed_fold.concl(),
            &step_at.imp(graph.at(&xs, a).unwrap()).unwrap()
        );
    }

    #[test]
    fn call_site_boundary_rejects_unproved_monotonicity_and_foreign_graphs() {
        let carrier = Type::nat();
        let rel = relation_type(&carrier, 1).unwrap();
        let r = Term::free("__badR", rel.clone());
        let step = Term::abs(rel.clone(), covalence_core::subst::close(&r, "__badR"));
        assert!(MeasuredCallSites::new(&carrier, 1, step, Thm::assume(truth()).unwrap(),).is_err());

        let calls = identity_call_sites(&carrier, 1);
        let foreign_closure = Term::abs(rel, truth());
        let foreign =
            define_least_graph("acl2.wfrec.test.foreign", &carrier, 1, foreign_closure).unwrap();
        let x = Term::free("foreign_x", carrier.clone());
        let a = Term::free("foreign_a", carrier);
        let step_at = relation_at(
            calls.step.clone().apply(foreign.graph.clone()).unwrap(),
            std::slice::from_ref(&x),
            a.clone(),
        )
        .unwrap();
        assert!(
            calls
                .fold_at(
                    &foreign,
                    std::slice::from_ref(&x),
                    a,
                    Thm::assume(step_at).unwrap(),
                )
                .is_err()
        );
    }

    #[test]
    fn w2_measured_scaffold_derives_totality_only_from_wf_closure() {
        let o = ordinals().unwrap();
        let carrier = o.th.ty.clone();
        let calls = constant_unary_call_sites(&carrier);
        let graph = calls
            .define_graph("acl2.wfrec.test.measured-total")
            .unwrap();

        // Constant ordinal-one measure, with validity proved by ground ordinal
        // normalization and t/anil constructor distinctness.
        let one = o.th.aint_at(&mk_int(1i64)).unwrap();
        let mx = Term::free("__measurex", carrier.clone());
        let measure = Term::abs(carrier.clone(), one.clone());
        let op_one = o.op.clone().apply(one).unwrap();
        let folded_op = o.ord_fold(&op_one).unwrap();
        assert_eq!(folded_op.concl().as_eq().unwrap().1, &o.pr.t);
        let v = Term::free("__opv", carrier.clone());
        let nonnil_pred = Term::abs(
            carrier.clone(),
            covalence_core::subst::close(
                &v.equals(o.th.nil.clone()).unwrap().not().unwrap(),
                "__opv",
            ),
        );
        let pred_t = nonnil_pred.clone().apply(o.pr.t.clone()).unwrap();
        let t_ne_nil_redex = beta_nf(pred_t)
            .sym()
            .unwrap()
            .eq_mp(o.pr.t_ne_nil().unwrap())
            .unwrap();
        let valid_one = folded_op
            .cong_arg(nonnil_pred)
            .unwrap()
            .sym()
            .unwrap()
            .eq_mp(t_ne_nil_redex)
            .unwrap()
            .all_intro("__mvalidx0", carrier.clone())
            .unwrap();
        let scaffold = MeasuredTotality::new(&carrier, 1, measure, valid_one).unwrap();

        // A syntactically present but unreachable recursive call is accepted
        // only with an actual (vacuous) guarded decrease proof.
        let call_x = Term::free("__callx", carrier.clone());
        let guard = mk_bool(false);
        let smaller = o
            .below
            .clone()
            .apply(scaffold.measure_at(std::slice::from_ref(&call_x)).unwrap())
            .unwrap()
            .apply(scaffold.measure_at(std::slice::from_ref(&call_x)).unwrap())
            .unwrap();
        let decrease = fal_from_lit(Thm::assume(guard.clone()).unwrap())
            .unwrap()
            .false_elim(smaller)
            .unwrap()
            .imp_intro(&guard)
            .unwrap();
        assert!(
            GuardedMeasuredCall::new(
                &scaffold,
                std::slice::from_ref(&call_x),
                mk_bool(false),
                vec![call_x.clone()],
                decrease,
            )
            .is_ok()
        );
        assert!(
            GuardedMeasuredCall::new(
                &scaffold,
                std::slice::from_ref(&call_x),
                mk_bool(false),
                vec![call_x.clone()],
                Thm::refl(o.th.nil.clone()).unwrap(),
            )
            .is_err()
        );

        // The constant body takes one step at nil for every input, so W1
        // supplies direct graph existence.
        let x = Term::free("__directx", carrier.clone());
        let nil = o.th.nil.clone();
        let step_at = relation_at(
            calls.step.clone().apply(graph.graph.clone()).unwrap(),
            std::slice::from_ref(&x),
            nil.clone(),
        )
        .unwrap();
        let step_proof = beta_nf(step_at)
            .sym()
            .unwrap()
            .eq_mp(Thm::refl(nil.clone()).unwrap())
            .unwrap();
        let graph_nil = calls
            .fold_at(&graph, std::slice::from_ref(&x), nil.clone(), step_proof)
            .unwrap();
        let pred = Term::abs(
            carrier.clone(),
            covalence_core::subst::close(
                &graph
                    .at(
                        std::slice::from_ref(&x),
                        Term::free("__ew", carrier.clone()),
                    )
                    .unwrap(),
                "__ew",
            ),
        );
        let pred_nil = pred.clone().apply(nil.clone()).unwrap();
        let at_pred = beta_nf(pred_nil).sym().unwrap().eq_mp(graph_nil).unwrap();
        let direct_total = exists_intro(pred, nil, at_pred)
            .unwrap()
            .all_intro("__directx", carrier.clone())
            .unwrap();

        // Build the exact wf-induction closure.  It deliberately ignores the
        // IH because this test body is a base case.
        let motive = scaffold.motive(&graph).unwrap();
        let z = Term::free("__mtcz", carrier.clone());
        let y = Term::free("__mtcy", carrier.clone());
        let ih = o
            .below
            .clone()
            .apply(y.clone())
            .unwrap()
            .apply(z.clone())
            .unwrap()
            .imp(motive.clone().apply(y).unwrap())
            .unwrap()
            .forall("__mtcy", carrier.clone())
            .unwrap();
        let body_x = Term::free("__mtx0", carrier.clone());
        let measure_eq = scaffold
            .measure_at(std::slice::from_ref(&body_x))
            .unwrap()
            .equals(z.clone())
            .unwrap();
        let closure = direct_total
            .all_elim(body_x)
            .unwrap()
            .imp_intro(&measure_eq)
            .unwrap()
            .all_intro("__mtx0", carrier.clone())
            .unwrap()
            .imp_intro(&ih)
            .unwrap()
            .all_intro("__mtcz", carrier.clone())
            .unwrap();
        let closure_goal_nf = beta_nf(scaffold.closure_goal(&graph).unwrap());
        assert_eq!(
            beta_nf_concl(closure.clone()).unwrap().concl(),
            closure_goal_nf.concl().as_eq().unwrap().1
        );

        let total = scaffold.prove_totality(&graph, closure).unwrap();
        assert!(total.hyps().is_empty());
        let arbitrary = Term::free("total_input", carrier);
        let at = total.all_elim(arbitrary.clone()).unwrap();
        let witness = Term::free("__checkw", o.th.ty.clone());
        assert_eq!(
            at.concl(),
            &graph
                .at(std::slice::from_ref(&arbitrary), witness.clone())
                .unwrap()
                .exists("__checkw", o.th.ty.clone())
                .unwrap()
        );

        // A theorem about a different closure cannot unlock totality.
        assert!(
            scaffold
                .prove_totality(&graph, Thm::refl(mx).unwrap())
                .is_err()
        );
    }

    #[test]
    fn w3_measured_determinacy_is_exact_closed_and_fail_closed() {
        let o = ordinals().unwrap();
        let carrier = o.th.ty.clone();
        let scaffold = constant_one_scaffold();
        let rel = relation_type(&carrier, 1).unwrap();

        // A closure independent of its relation yields the empty least graph:
        // elimination may instantiate the quantified relation with false.
        let n = Term::free("__empty_truth", Type::nat());
        let closure = Term::abs(rel.clone(), n.clone().equals(n.clone()).unwrap());
        let graph =
            define_least_graph("acl2.wfrec.test.measured-determinacy", &carrier, 1, closure)
                .unwrap();
        let x = Term::free("__empty_x", carrier.clone());
        let a = Term::free("__empty_a", carrier.clone());
        let b = Term::free("__empty_b", carrier.clone());
        let ga = graph.at(std::slice::from_ref(&x), a.clone()).unwrap();
        let gb = graph.at(std::slice::from_ref(&x), b.clone()).unwrap();
        let empty = Term::abs(carrier.clone(), Term::abs(carrier.clone(), mk_bool(false)));
        let empty_at = graph
            .elim(
                std::slice::from_ref(&x),
                a.clone(),
                Thm::assume(ga.clone()).unwrap(),
                empty,
                Thm::refl(n).unwrap(),
            )
            .unwrap();
        let contradiction = fal_from_lit(beta_nf_concl(empty_at).unwrap()).unwrap();
        let direct = contradiction
            .false_elim(a.clone().equals(b.clone()).unwrap())
            .unwrap()
            .imp_intro(&gb)
            .unwrap()
            .imp_intro(&ga)
            .unwrap()
            .all_intro("__empty_b", carrier.clone())
            .unwrap()
            .all_intro("__empty_a", carrier.clone())
            .unwrap()
            .all_intro("__empty_x", carrier.clone())
            .unwrap();

        // Lift direct uniqueness into the exact well-founded closure. This
        // empty/base relation does not need its induction hypothesis.
        let z = Term::free("__mdcz", carrier.clone());
        let y = Term::free("__mdcy", carrier.clone());
        let motive = scaffold.determinacy_motive(&graph).unwrap();
        let ih = o
            .below
            .clone()
            .apply(y.clone())
            .unwrap()
            .apply(z.clone())
            .unwrap()
            .imp(motive.clone().apply(y).unwrap())
            .unwrap()
            .forall("__mdcy", carrier.clone())
            .unwrap();
        let body_x = Term::free("__mdx0", carrier.clone());
        let measure_eq = scaffold
            .measure_at(std::slice::from_ref(&body_x))
            .unwrap()
            .equals(z.clone())
            .unwrap();
        let closure = direct
            .all_elim(body_x)
            .unwrap()
            .imp_intro(&measure_eq)
            .unwrap()
            .all_intro("__mdx0", carrier.clone())
            .unwrap()
            .imp_intro(&ih)
            .unwrap()
            .all_intro("__mdcz", carrier.clone())
            .unwrap();
        let deterministic = scaffold.prove_determinacy(&graph, closure.clone()).unwrap();
        assert!(deterministic.hyps().is_empty());
        let got = deterministic
            .all_elim(x.clone())
            .unwrap()
            .all_elim(a.clone())
            .unwrap()
            .all_elim(b.clone())
            .unwrap();
        assert_eq!(got.hyps().len(), 0);
        assert_eq!(
            got.concl(),
            &ga.imp(gb.imp(a.equals(b).unwrap()).unwrap()).unwrap()
        );

        // Hypothesis-bearing and totality-shaped evidence both fail closed.
        assert!(
            scaffold
                .prove_determinacy(
                    &graph,
                    Thm::assume(scaffold.determinacy_closure_goal(&graph).unwrap()).unwrap(),
                )
                .is_err()
        );
        assert!(
            scaffold
                .prove_determinacy(
                    &graph,
                    Thm::assume(scaffold.closure_goal(&graph).unwrap()).unwrap(),
                )
                .is_err()
        );
    }
}
