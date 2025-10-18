/*!
SMT-lib implementation over `covalence`
*/

use covalence_kernel::{
    kernel::{Kernel, TermStore},
    store::CtxId,
};

/// State for SMT over a given kernel
///
/// Note we pass in the kernel as a mutable reference every time, rather than owning it; this allows
/// us to:
/// - Share a kernel between multiple SMT states
/// - Use the SMT state as a strategy, or inside a strategy
///
/// Our current design represents an SMT state in `covalence` as a stack of three contexts
/// - A _sort context_ in which sorts used by the problem are defined. If `sort_ctx == var_ctx`,
///   then the sorts are all built-in sorts (e.g. bool, nat, etc.) and `define-sort` will error.
/// - A _variable context_ in which variables, functions, predicates, and relations are stored.
/// - An _equation context_ storing equations about variables
///
/// In short, we represent an SMT state as essentially a generalized algebraic theory: a
/// multi-sorted algebraic theory which is also:
/// - Parametrized by a small set of base types (Nat, Int, Bool, Real, etc.)
/// - Allows higher-order functions and predicates
/// - Allows general axioms (e.g. relations `(r a b)`, implications `(=> (r a b) p)`, etc.), and in
///   particular quasi-equations like `(=> (distinct a 0) (= (/ (* a b) a) b)) `
///
/// For a concrete example
/// ```smt
/// (declare-sort S 0)              ; this gets put into the sort context
/// (declare-const z S)             ; this gets put into the variable context
/// (declare-const p Int)           ; also in the variable context
/// (declare-fun r (S Int) Bool)    ; ditto
/// (assert (r z p))                ; this gets put into the equation context
/// (assert (r z 0))                ; also in the equation context
/// (check-sat)                     ; sat
/// ```
/// will tell us this is `sat`. If we then `(get-model)`, we get
/// ```smt
/// (
/// ; cardinality of S is 1
/// ; rep: (as @S_0 S)
/// (define-fun z () S (as @S_0 S))
/// (define-fun p () Int 0)
/// (define-fun r ((_arg_1 S) (_arg_2 Int)) Bool true)
/// )
/// ```
/// Later, we should add in a way to load up this model in-theory and verify it's actually a model
/// (which might be harder in some more convoluted cases, like with quantifiers, but is usually the
/// easy part).
///
/// But more interestingly, if I do
/// ```smt
/// (assert (= 0 1))    ; this goes in the equation context
/// (check-sat)         ; unsat
/// ```
/// and set up our solver to produce Alethe proofs, we get
/// ```smt
/// (
/// (assume a0 (! (= 0 1) :named @p_1))
/// (step t0 (cl (not (! (= @p_1 false) :named @p_2)) (not @p_1) false) :rule equiv_pos2)
/// (step t1 (cl @p_2) :rule hole :args ("TRUST_THEORY_REWRITE" @p_2 3 7))
/// (step t2 (cl false) :rule resolution :premises (t0 t1 a0))
/// (step t3 (cl (not false)) :rule false)
/// (step t4 (cl) :rule resolution :premises (t2 t3))
/// )
/// ```
/// We can feed this to our SMT solver to prove our equational context contradictory, which we can
/// then use to extract implications et al using our derivation rules (we should add some for
/// that!).
///
/// Eventually, we want to generalize this to a nice way of representing a large variety of
/// algebraic structures, such as categories, by introducing _generalized relations_ like `Hom : Obj
/// -> Obj -> Type`, which will also live in the _variable context_.
///
/// Operations on `Hom` like `id` and `comp` then live in the equation context, looking essentially
/// like a _proof-relevant_ relation, and we introduce a higher-order equation context for equations
/// about these.
///
/// This probably generalizes from the 1-categorical setting (viewing regular algebraic theories as
/// hence living in the proof-irrelevant "0-categorical" setting, with their relations being actual
/// proof-irrelevant relations) to the n-categorical setting, with a stack of equation contexts
/// containing the generalized relations at each depth. For example (with mocked up syntax)
/// ```smt
/// ; == context 0 (sort context)
/// (declare-sort Cat 0)                               ; a sort of (abstract) categories
/// ; == context 1 (variable context 0)
/// (declare-fun Func (Cat Cat) Type)                  ; functors are arrows between categories
/// ; == context 2 (equation context 0, variable context 1)
/// ; identity functor is a proof relevant constructor of the
/// ; "generalized relation" Func
/// (declare-fun Func.id (A Cat) (B Cat) (Func A A)))
/// ; NatTrans is a level-2 "generalized relation"  
/// (declare-fun NatTrans (A Cat) (B Cat) (F (Func A B)) (G (Func A B)) Type)
/// ; == context 3 (equation context 1, variable context 2)
/// ; composition
/// ; equations about composition
/// ; identity natural transformation is a proof-relevant constructor of
/// ; the "generalized relation" NatTrans
/// (declare-fun NatTrans.id (A Cat) (B Cat) (F (Func A B)) (NatTrans A B F F))
/// ; we can go on to higher order stuff...
/// ```
/// Leaving this here as a note for the future.
///
/// When we do get to universal algebra, we probably want to make this a `Vec<CtxId>` doing the
/// above, and then deal with whether SmtState should be a separate thing or just an SMT-API for the
/// universal algebra representation.
#[derive(Debug, Clone, Eq, PartialEq, Hash, PartialOrd, Ord)]
pub struct SmtProblem {
    /// The sort context
    sort_ctx: CtxId,
    /// The variable context
    var_ctx: CtxId,
    /// The equation context
    eqn_ctx: CtxId,
}

impl SmtProblem {
    /// Create a new SMT state in the given kernel
    pub fn new(kernel: &mut Kernel) -> Self {
        let sort_ctx = kernel.new_ctx();
        let var_ctx = kernel.with_parent(sort_ctx);
        let eqn_ctx = kernel.with_parent(var_ctx);
        Self {
            sort_ctx,
            var_ctx,
            eqn_ctx,
        }
    }
}
