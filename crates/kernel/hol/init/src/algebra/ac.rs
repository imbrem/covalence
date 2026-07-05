//! A **model-generic associativity-commutativity (AC) rewrite tactic**.
//!
//! Given a binary operator `∘` together with its *associativity* and
//! *commutativity* **equations**
//!
//! - `assoc : ⊢ ∀a b c. (a ∘ b) ∘ c = a ∘ (b ∘ c)`,
//! - `comm  : ⊢ ∀a b. a ∘ b = b ∘ a`,
//!
//! [`Ac::normalize`] takes any term `t` built out of `∘` (a tree of nested
//! applications) and produces a **kernel-checked** proof `⊢ t = nf`, where the
//! normal form `nf` is the *flattened, stably-sorted, right-associated*
//! re-bracketing of `t`'s operands. Two AC-equal terms have the *same* normal
//! form, so `⊢ t₁ = t₂` is decided by `normalize t₁ ⟶ ⊢ t₁ = nf`,
//! `normalize t₂ ⟶ ⊢ t₂ = nf`, and transitivity ([`Ac::prove_eq`]).
//!
//! **Every** rewrite step is a genuine kernel equality: assoc / comm are
//! *instantiated* (via [`Thm::all_elim`]) at the concrete operands and threaded
//! through [`Thm::trans`] / congruence — nothing is postulated.
//!
//! ## Model-genericity
//!
//! [`Ac`] is parameterised by an [`AcOp`] — the operator's *term theory*
//! (build / destructure an application of `∘`) plus its two axiom *equations*.
//! This is exactly the shape of the algebraic traits in [`crate::algebra::semiring`] /
//! [`crate::algebra::ring`]: a single generic normalizer runs against `nat.add`,
//! `nat.mul`, `int.add`, `∧`, `∨`, … — anything that provides an [`AcOp`].
//! [`HolAc`] is the canonical HOL instance: an op is a [`Term`] (the
//! partially-applicable `∘`), and the axioms are HOL [`Thm`]s.
//!
//! ## The normal form
//!
//! For operands `x₁, …, xₙ` (the leaves of `t`'s `∘`-tree, read left-to-right)
//! sorted by a caller-supplied stable key into `y₁ ≤ … ≤ yₙ`, the normal form is
//! the right-nested
//!
//! ```text
//!   y₁ ∘ (y₂ ∘ (⋯ ∘ yₙ))
//! ```
//!
//! A single leaf normalises to itself. The sort is **stable** (equal-key
//! operands keep their original order), so the normal form is canonical for the
//! chosen key.

use covalence_core::{Result, Term, Thm};

use crate::init::ext::ThmExt;

/// A binary operator's **term theory + AC axioms**, the model-generic input to
/// [`Ac`]. See the [module docs](self).
///
/// The axioms are supplied **already instantiated** at concrete operands —
/// [`assoc_at`](AcOp::assoc_at) / [`comm_at`](AcOp::comm_at) — so the engine
/// stays agnostic to *how* a model instantiates: a `∀`-quantified HOL axiom
/// instantiates by [`Thm::all_elim`] ([`HolAc::from_forall`]); a free-variable
/// equation instantiates by [`Thm::inst`] ([`HolAc::from_free`]); a deep
/// embedding might do something else entirely.
pub trait AcOp {
    /// Build the application `a ∘ b`.
    fn op(&self, a: Term, b: Term) -> Result<Term>;

    /// Destructure `t` as `a ∘ b`, returning `(a, b)` iff `t` is a top-level
    /// application of *this* operator. The flattener uses this to find leaves.
    fn dest(&self, t: &Term) -> Option<(Term, Term)>;

    /// The associativity equation **instantiated** at `a, b, c`:
    /// `⊢ (a ∘ b) ∘ c = a ∘ (b ∘ c)`.
    fn assoc_at(&self, a: &Term, b: &Term, c: &Term) -> Result<Thm>;

    /// The commutativity equation **instantiated** at `a, b`: `⊢ a ∘ b = b ∘ a`.
    fn comm_at(&self, a: &Term, b: &Term) -> Result<Thm>;
}

/// The model-generic AC normalizer over an [`AcOp`] and a stable operand key.
///
/// `key` maps each operand [`Term`] to a sort key `K`; operands are sorted by
/// it (stably) to form the normal form. A typical key is the term's printed
/// form (`Term::to_string`) for a deterministic syntactic order.
pub struct Ac<O, F, K> {
    op: O,
    key: F,
    _k: core::marker::PhantomData<K>,
}

impl<O, F, K> Ac<O, F, K>
where
    O: AcOp,
    F: Fn(&Term) -> K,
    K: Ord,
{
    /// Build a normalizer for operator `op`, ordering operands by `key`.
    pub fn new(op: O, key: F) -> Self {
        Self {
            op,
            key,
            _k: core::marker::PhantomData,
        }
    }

    /// The operator handle (for building/destructuring terms).
    pub fn op(&self) -> &O {
        &self.op
    }

    /// Flatten `t`'s `∘`-tree into its operand leaves, left-to-right.
    ///
    /// A leaf is any subterm that is *not* a top-level `∘`-application. A bare
    /// operand returns a one-element list.
    pub fn leaves(&self, t: &Term) -> Vec<Term> {
        let mut out = Vec::new();
        self.collect(t, &mut out);
        out
    }

    fn collect(&self, t: &Term, out: &mut Vec<Term>) {
        if let Some((a, b)) = self.op.dest(t) {
            self.collect(&a, out);
            self.collect(&b, out);
        } else {
            out.push(t.clone());
        }
    }

    /// `⊢ t = nf`: the AC normal form of `t`. See the [module docs](self).
    ///
    /// Two phases, each a chain of kernel equalities:
    /// 1. **flatten / right-associate** — `⊢ t = ral`, where `ral` is `t`'s
    ///    leaves right-nested in their original order (uses `assoc`);
    /// 2. **sort** — `⊢ ral = nf`, an insertion sort of the right-nested list
    ///    by `key`, each adjacent swap justified by `comm` + `assoc`.
    pub fn normalize(&self, t: &Term) -> Result<Thm> {
        let leaves = self.leaves(t);
        // ⊢ t = right_nested(leaves)
        let flat = self.rebuild(t, &leaves)?;
        // ⊢ right_nested(leaves) = right_nested(sorted)
        let sort = self.sort_rn(&leaves)?;
        flat.trans(sort)
    }

    /// `⊢ t₁ = t₂` when `t₁` and `t₂` are AC-equal under `∘` (same multiset of
    /// leaves). Errors — minting nothing — when their normal forms differ.
    pub fn prove_eq(&self, t1: &Term, t2: &Term) -> Result<Thm> {
        let n1 = self.normalize(t1)?; // ⊢ t1 = nf1
        let n2 = self.normalize(t2)?; // ⊢ t2 = nf2
        let nf1 = rhs(&n1)?;
        let nf2 = rhs(&n2)?;
        if nf1 != nf2 {
            return Err(covalence_core::Error::ConnectiveRule(format!(
                "ac::prove_eq: `{t1}` and `{t2}` are not AC-equal (`{nf1}` vs `{nf2}`)"
            )));
        }
        n1.trans(n2.sym()?)
    }

    // ---- phase 1: flatten to the right-nested form ----

    /// `⊢ t = right_nested(leaves)`, reassociating every left-nesting to the
    /// right. `leaves` must be exactly `self.leaves(t)`.
    fn rebuild(&self, t: &Term, leaves: &[Term]) -> Result<Thm> {
        if leaves.len() <= 1 {
            // A bare operand (or a single leaf): already normal.
            return Thm::refl(t.clone());
        }
        // `t` is `a ∘ b`. Recursively reassociate each side, then merge: the
        // result is `aₗ₁ ∘ (… ∘ (aₗₖ ∘ rebuild(b)))`.
        let (a, b) = self.op.dest(t).expect("multi-leaf term is a ∘-application");
        let a_leaves = self.leaves(&a);
        let b_leaves = self.leaves(&b);
        // ⊢ a = RN(a_leaves), ⊢ b = RN(b_leaves)
        let a_eq = self.rebuild(&a, &a_leaves)?;
        let b_eq = self.rebuild(&b, &b_leaves)?;
        let rn_b = rhs_term(&b_eq)?; // RN(b_leaves)
        // ⊢ a ∘ b = RN(a_leaves) ∘ RN(b_leaves)   (congruence)
        let cong = self.cong(a_eq, b_eq)?;
        // ⊢ RN(a_leaves) ∘ RN(b_leaves) = RN(a_leaves ++ b_leaves)
        let merge = self.append_rn(&a_leaves, &rn_b)?;
        cong.trans(merge)
    }

    /// `⊢ RN(xs) ∘ tail = RN(xs ++ leaves(tail))`, where `tail` is *already*
    /// right-nested. Pulls every operand of the left list out to the front by
    /// repeated `assoc`, so the whole thing becomes one right-nested list.
    fn append_rn(&self, xs: &[Term], tail: &Term) -> Result<Thm> {
        match xs {
            [] => unreachable!("append_rn: empty left list"),
            [_only] => {
                // `x ∘ tail` is already right-nested.
                let x = &xs[0];
                Thm::refl(self.op.op(x.clone(), tail.clone())?)
            }
            [head, rest @ ..] => {
                // (RN(rest_with_head)) where head ∘ (RN(rest) ∘ tail):
                // first recurse on `RN(rest) ∘ tail`, then prepend `head` and
                // reassociate the now-left-nested `head ∘ (RN(rest) ∘ tail)`.
                //
                // RN(xs) = head ∘ RN(rest).  We want
                //   (head ∘ RN(rest)) ∘ tail = head ∘ (RN(rest) ∘ tail)   [assoc]
                // then push `head` through the recursive append on the right.
                let rn_rest = self.right_nest(rest)?;
                // ⊢ (head ∘ RN(rest)) ∘ tail = head ∘ (RN(rest) ∘ tail)
                let step = self.assoc_at(head, &rn_rest, tail)?;
                // ⊢ RN(rest) ∘ tail = RN(rest ++ leaves(tail))   (recurse)
                let rec = self.append_rn(rest, tail)?;
                // ⊢ head ∘ (RN(rest) ∘ tail) = head ∘ RN(rest ++ …)
                let under = self.cong_tail(head, rec)?;
                step.trans(under)
            }
        }
    }

    // ---- phase 2: sort the right-nested list ----

    /// `⊢ RN(xs) = RN(sort(xs))` — insertion sort by `key`, each adjacent swap a
    /// kernel equality.
    fn sort_rn(&self, xs: &[Term]) -> Result<Thm> {
        if xs.len() <= 1 {
            return Thm::refl(self.right_nest(xs)?);
        }
        // Sort the tail first, then insert the head into the sorted tail.
        let (head, tail) = (xs[0].clone(), &xs[1..]);
        let tail_sorted = self.sort_rn(tail)?; // ⊢ RN(tail) = RN(sorted_tail)
        let sorted_tail = rn_leaves(&self.op, &rhs_term(&tail_sorted)?);
        // ⊢ head ∘ RN(tail) = head ∘ RN(sorted_tail)   (congruence on the tail)
        let cong = self.cong_tail(&head, tail_sorted)?;
        // ⊢ head ∘ RN(sorted_tail) = RN(insert(head, sorted_tail))
        let ins = self.insert_rn(&head, &sorted_tail)?;
        cong.trans(ins)
    }

    /// `⊢ x ∘ RN(sorted) = RN(insert(x, sorted))`, inserting `x` into the
    /// already-sorted right-nested list `sorted` at its key-ordered position.
    fn insert_rn(&self, x: &Term, sorted: &[Term]) -> Result<Thm> {
        // Bubble `x` rightward past every operand with a strictly-smaller key
        // (stable: stop at the first operand whose key is ≥ x's).
        match sorted {
            [] => Thm::refl(x.clone()),
            [first] if (self.key)(first) <= (self.key)(x) => {
                // Two operands, `first` first: a single `comm` — `x∘first = first∘x`.
                self.comm_at(x, first)
            }
            [first, rest @ ..] => {
                if (self.key)(first) <= (self.key)(x) {
                    // `first` sorts before `x`: swap them, recurse into the tail.
                    let rn_rest = self.right_nest(rest)?;
                    // ⊢ x ∘ (first ∘ RN(rest)) = first ∘ (x ∘ RN(rest))
                    let swap = self.swap2(x, first, &rn_rest)?;
                    // ⊢ x ∘ RN(rest) = RN(insert(x, rest))   (recurse)
                    let rec = self.insert_rn(x, rest)?;
                    // ⊢ first ∘ (x ∘ RN(rest)) = first ∘ RN(insert(x, rest))
                    let under = self.cong_tail(first, rec)?;
                    swap.trans(under)
                } else {
                    // `x` sorts at the front: `x ∘ RN(sorted)` is already normal.
                    Thm::refl(self.op.op(x.clone(), self.right_nest(sorted)?)?)
                }
            }
        }
    }

    // ---- the AC micro-steps (each a kernel equality) ----

    /// `⊢ (a ∘ b) ∘ c = a ∘ (b ∘ c)` — `assoc` instantiated at `a, b, c`.
    fn assoc_at(&self, a: &Term, b: &Term, c: &Term) -> Result<Thm> {
        self.op.assoc_at(a, b, c)
    }

    /// `⊢ a ∘ b = b ∘ a` — `comm` instantiated at `a, b`.
    fn comm_at(&self, a: &Term, b: &Term) -> Result<Thm> {
        self.op.comm_at(a, b)
    }

    /// `⊢ x ∘ (y ∘ r) = y ∘ (x ∘ r)` — swap the first two operands of a
    /// right-nested list, keeping the tail `r` fixed. Derived:
    /// `x∘(y∘r) =⟨assoc⁻¹⟩ (x∘y)∘r =⟨comm⟩ (y∘x)∘r =⟨assoc⟩ y∘(x∘r)`.
    fn swap2(&self, x: &Term, y: &Term, r: &Term) -> Result<Thm> {
        // x∘(y∘r) = (x∘y)∘r       (assoc, backwards)
        let s1 = self.assoc_at(x, y, r)?.sym()?;
        // (x∘y)∘r = (y∘x)∘r       (comm under the left congruence)
        let s2 = self.cong_head(self.comm_at(x, y)?, r)?;
        // (y∘x)∘r = y∘(x∘r)       (assoc, forwards)
        let s3 = self.assoc_at(y, x, r)?;
        s1.trans(s2)?.trans(s3)
    }

    // ---- congruence helpers ----

    /// `⊢ a₁ ∘ b₁ = a₂ ∘ b₂` from `⊢ a₁ = a₂` and `⊢ b₁ = b₂`.
    fn cong(&self, a: Thm, b: Thm) -> Result<Thm> {
        let (a1, _) = a
            .concl()
            .as_eq()
            .ok_or(covalence_core::Error::NotAnEquation)?;
        let bare = bare_op(&self.op, a1)?;
        // a.cong_arg(∘) : ⊢ (∘ a₁) = (∘ a₂) ; cong_app(b) : ⊢ (∘ a₁) b₁ = (∘ a₂) b₂.
        a.cong_arg(bare)?.cong_app(b)
    }

    /// `⊢ x ∘ r₁ = x ∘ r₂` from `⊢ r₁ = r₂` — congruence on the *tail* only.
    fn cong_tail(&self, x: &Term, r: Thm) -> Result<Thm> {
        let op_head = partial_op(&self.op, x)?;
        r.cong_arg(op_head)
    }

    /// `⊢ l₁ ∘ r = l₂ ∘ r` from `⊢ l₁ = l₂` — congruence on the *head* only.
    fn cong_head(&self, l: Thm, r: &Term) -> Result<Thm> {
        // ⊢ l₁ = l₂  ⟹  ⊢ (∘ l₁) = (∘ l₂)  ⟹  ⊢ (∘ l₁) r = (∘ l₂) r
        let (l1, _) = l
            .concl()
            .as_eq()
            .ok_or(covalence_core::Error::NotAnEquation)?;
        let bare = bare_op(&self.op, l1)?;
        l.cong_arg(bare)?.cong_fn(r.clone())
    }

    // ---- term builders ----

    /// The right-nested term `x₁ ∘ (x₂ ∘ (⋯ ∘ xₙ))` for a non-empty `xs`.
    fn right_nest(&self, xs: &[Term]) -> Result<Term> {
        match xs {
            [] => unreachable!("right_nest: empty list"),
            [only] => Ok(only.clone()),
            [head, rest @ ..] => self.op.op(head.clone(), self.right_nest(rest)?),
        }
    }
}

/// The partially-applied operator `∘ a` (`op` with its first argument fixed) —
/// the function side tail-congruence rewrites against.
fn partial_op<O: AcOp>(op: &O, a: &Term) -> Result<Term> {
    // `op(a, b)` is `App(App(∘, a), b)`; its `.as_app().0` is `∘ a`.
    let app = op.op(a.clone(), a.clone())?;
    let (head, _) = app
        .as_app()
        .ok_or_else(|| covalence_core::Error::ConnectiveRule("ac: op is not binary".into()))?;
    Ok(head.clone())
}

/// The **bare** binary operator `∘` (`App(App(∘, a), b)`'s head-of-head) — the
/// function head-congruence rewrites against. `example` is any well-typed
/// operand of the right sort; it is only used to build then destructure an
/// application, never reduced.
fn bare_op<O: AcOp>(op: &O, example: &Term) -> Result<Term> {
    let app = op.op(example.clone(), example.clone())?;
    let (head, _) = app
        .as_app()
        .ok_or_else(|| covalence_core::Error::ConnectiveRule("ac: op is not binary".into()))?;
    let (bare, _) = head
        .as_app()
        .ok_or_else(|| covalence_core::Error::ConnectiveRule("ac: op is not binary".into()))?;
    Ok(bare.clone())
}

/// The leaves of an *already right-nested* term — cheap re-flatten used to read
/// back a sorted tail.
fn rn_leaves<O: AcOp>(op: &O, t: &Term) -> Vec<Term> {
    let mut out = Vec::new();
    let mut cur = t.clone();
    while let Some((a, b)) = op.dest(&cur) {
        out.push(a);
        cur = b;
    }
    out.push(cur);
    out
}

/// The RHS term of an equational theorem.
fn rhs(thm: &Thm) -> Result<Term> {
    rhs_term(thm)
}
fn rhs_term(thm: &Thm) -> Result<Term> {
    Ok(thm
        .concl()
        .as_eq()
        .ok_or(covalence_core::Error::NotAnEquation)?
        .1
        .clone())
}

// ============================================================================
// The canonical HOL instance
// ============================================================================

/// How a HOL AC axiom is *instantiated* at concrete operands.
#[derive(Clone)]
enum Inst {
    /// A `∀`-quantified axiom (`⊢ ∀a b c. …`): strip binders by
    /// [`Thm::all_elim`] in argument order.
    Forall,
    /// A free-variable axiom (`⊢ … with free p, q, r`): substitute the named
    /// free variables by [`Thm::inst`]. The list gives the variable names in
    /// argument order (2 for `comm`, 3 for `assoc`).
    Free(Vec<String>),
}

/// A HOL [`AcOp`]: the operator is the partially-applicable [`Term`] `∘`, and
/// the AC axioms are HOL [`Thm`]s.
///
/// Two constructors cover the two shapes the catalogue ships axioms in:
/// - [`HolAc::from_forall`] — `∀`-quantified axioms (e.g. `nat.add` with
///   [`nat::add_assoc`](crate::init::nat::add_assoc) /
///   [`nat::add_comm`](crate::init::nat::add_comm));
/// - [`HolAc::from_free`] — free-variable equations (e.g. `∧` with
///   [`logic::and_assoc`](crate::init::logic::and_assoc) /
///   [`logic::and_comm`](crate::init::logic::and_comm), whose `p, q, r` are
///   *free*, not bound).
#[derive(Clone)]
pub struct HolAc {
    /// The binary operator as a curryable term (`App(App(op, a), b)` = `a ∘ b`).
    op: Term,
    assoc: Thm,
    comm: Thm,
    inst: Inst,
}

impl HolAc {
    /// Build a HOL AC operator from a `∀`-quantified `assoc` / `comm`.
    ///
    /// `assoc : ⊢ ∀a b c. (a∘b)∘c = a∘(b∘c)`, `comm : ⊢ ∀a b. a∘b = b∘a`.
    /// Instantiation is by [`Thm::all_elim`].
    pub fn from_forall(op: Term, assoc: Thm, comm: Thm) -> Self {
        Self {
            op,
            assoc,
            comm,
            inst: Inst::Forall,
        }
    }

    /// Build a HOL AC operator from *free-variable* `assoc` / `comm` equations,
    /// naming the free variables to substitute (in argument order).
    ///
    /// `assoc : ⊢ (a∘b)∘c = a∘(b∘c)` with free vars `assoc_vars = [a, b, c]`;
    /// `comm : ⊢ a∘b = b∘a` with free vars `comm_vars = [a, b]`. Instantiation
    /// is by [`Thm::inst`]. (`comm_vars` are taken as the first two of
    /// `assoc_vars` when they coincide — pass the names the equations actually
    /// use.)
    pub fn from_free(op: Term, assoc: Thm, comm: Thm, vars: [&str; 3]) -> Self {
        Self {
            op,
            assoc,
            comm,
            inst: Inst::Free(vars.iter().map(|s| s.to_string()).collect()),
        }
    }

    /// Convenience: a [`HolAc`] paired with the syntactic-print key, ready to
    /// [`normalize`](Ac::normalize) / [`prove_eq`](Ac::prove_eq).
    pub fn engine(self) -> Ac<HolAc, impl Fn(&Term) -> String, String> {
        Ac::new(self, |t: &Term| t.to_string())
    }
}

impl AcOp for HolAc {
    fn op(&self, a: Term, b: Term) -> Result<Term> {
        use crate::init::ext::TermExt;
        self.op.clone().apply(a)?.apply(b)
    }

    fn dest(&self, t: &Term) -> Option<(Term, Term)> {
        let (f, b) = t.as_app()?;
        let (head, a) = f.as_app()?;
        (head == &self.op).then(|| (a.clone(), b.clone()))
    }

    fn assoc_at(&self, a: &Term, b: &Term, c: &Term) -> Result<Thm> {
        match &self.inst {
            Inst::Forall => self
                .assoc
                .clone()
                .all_elim(a.clone())?
                .all_elim(b.clone())?
                .all_elim(c.clone()),
            Inst::Free(vars) => inst_simul(
                self.assoc.clone(),
                &[&vars[0], &vars[1], &vars[2]],
                &[a, b, c],
            ),
        }
    }

    fn comm_at(&self, a: &Term, b: &Term) -> Result<Thm> {
        match &self.inst {
            Inst::Forall => self.comm.clone().all_elim(a.clone())?.all_elim(b.clone()),
            Inst::Free(vars) => inst_simul(self.comm.clone(), &[&vars[0], &vars[1]], &[a, b]),
        }
    }
}

/// **Simultaneous** free-variable instantiation, capture-safe.
///
/// Substitutes each `names[i] ↦ reps[i]` in `thm` *at once* — done as two
/// sequential passes through disjoint fresh placeholders so a replacement that
/// mentions another substituted variable (e.g. `inst p↦r` alongside `inst r↦p`)
/// cannot capture. `names` and `reps` must have equal length.
fn inst_simul(thm: Thm, names: &[&str], reps: &[&Term]) -> Result<Thm> {
    debug_assert_eq!(names.len(), reps.len());
    // Phase 1: rename each axiom var to a unique placeholder that appears in no
    // operand (so phase 2 cannot re-capture it).
    let placeholders: Vec<String> = (0..names.len())
        .map(|i| format!("__ac_simul_{i}"))
        .collect();
    let mut t = thm;
    for (name, ph) in names.iter().zip(&placeholders) {
        // The placeholder must carry the variable's type; read it off `reps`.
        // (All operands of a binary op share the operator's argument type, so
        // any rep's type is the right one.) Use the matching rep's type.
        t = t.inst(name, Term::free(ph, reps[0].type_of()?))?;
    }
    // Phase 2: replace each placeholder with its real operand.
    for (ph, rep) in placeholders.iter().zip(reps) {
        t = t.inst(ph, (*rep).clone())?;
    }
    Ok(t)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::init::ext::TermExt;
    use crate::init::nat;
    use covalence_core::Type;

    fn v(name: &str) -> Term {
        Term::free(name, Type::nat())
    }

    fn add_engine() -> Ac<HolAc, impl Fn(&Term) -> String, String> {
        HolAc::from_forall(nat::nat_add(), nat::add_assoc(), nat::add_comm()).engine()
    }

    fn add(a: Term, b: Term) -> Term {
        nat::nat_add().apply(a).unwrap().apply(b).unwrap()
    }

    #[test]
    fn leaves_flattens_a_mixed_tree() {
        let e = add_engine();
        // (a + b) + (c + d)
        let t = add(add(v("a"), v("b")), add(v("c"), v("d")));
        let leaves = e.leaves(&t);
        let names: Vec<String> = leaves.iter().map(|t| t.to_string()).collect();
        assert_eq!(leaves.len(), 4);
        assert!(names[0].contains('a') && names[3].contains('d'));
    }

    #[test]
    fn normalize_sorts_and_proves_the_equation() {
        let e = add_engine();
        // (c + a) + b  should normalise to  a + (b + c)
        let t = add(add(v("c"), v("a")), v("b"));
        let thm = e.normalize(&t).unwrap();
        let (lhs, rhs) = thm.concl().as_eq().unwrap();
        assert_eq!(lhs, &t, "lhs is the original term");
        // rhs is right-nested and key-sorted: a + (b + c)
        let expected = add(v("a"), add(v("b"), v("c")));
        assert_eq!(rhs, &expected);
        assert!(thm.hyps().is_empty(), "AC normal form is hypothesis-free");
    }

    #[test]
    fn normalize_of_a_single_leaf_is_reflexive() {
        let e = add_engine();
        let thm = e.normalize(&v("x")).unwrap();
        let (l, r) = thm.concl().as_eq().unwrap();
        assert_eq!(l, r);
    }

    #[test]
    fn prove_eq_decides_two_ac_equal_terms() {
        let e = add_engine();
        // (a + b) + c   =   c + (a + b)   (AC-equal)
        let t1 = add(add(v("a"), v("b")), v("c"));
        let t2 = add(v("c"), add(v("a"), v("b")));
        let thm = e.prove_eq(&t1, &t2).unwrap();
        let (l, r) = thm.concl().as_eq().unwrap();
        assert_eq!(l, &t1);
        assert_eq!(r, &t2);
        assert!(thm.hyps().is_empty());
    }

    #[test]
    fn prove_eq_rejects_non_ac_equal_terms() {
        let e = add_engine();
        // a + b   vs   a + a   — different multisets, must error (mint nothing).
        let t1 = add(v("a"), v("b"));
        let t2 = add(v("a"), v("a"));
        assert!(e.prove_eq(&t1, &t2).is_err());
    }

    #[test]
    fn normalize_handles_repeated_operands_stably() {
        let e = add_engine();
        // (b + a) + a   →   a + (a + b)
        let t = add(add(v("b"), v("a")), v("a"));
        let thm = e.normalize(&t).unwrap();
        let (_, r) = thm.concl().as_eq().unwrap();
        let expected = add(v("a"), add(v("a"), v("b")));
        assert_eq!(r, &expected);
    }

    #[test]
    fn generic_over_the_connective_and() {
        // The same normalizer runs against `∧`, fed the new EQUATION forms of
        // `and.comm` / `and.assoc` from `init::logic` (Part 1 → Part 2).
        // `and.comm` / `and.assoc` are free-variable equations over `p, q, r`.
        let e = HolAc::from_free(
            covalence_core::defs::and(),
            crate::init::logic::and_assoc(),
            crate::init::logic::and_comm(),
            ["p", "q", "r"],
        )
        .engine();
        let and = |a: Term, b: Term| {
            a.and(b).unwrap() // bool conjunction
        };
        let p = Term::free("p", Type::bool());
        let q = Term::free("q", Type::bool());
        let r = Term::free("r", Type::bool());
        // (r ∧ p) ∧ q  →  p ∧ (q ∧ r)
        let t = and(and(r.clone(), p.clone()), q.clone());
        let thm = e.normalize(&t).unwrap();
        let (lhs, rhs) = thm.concl().as_eq().unwrap();
        assert_eq!(lhs, &t);
        assert_eq!(rhs, &and(p, and(q, r)));
        assert!(thm.hyps().is_empty());
    }

    #[test]
    fn generic_over_a_second_operator_mul() {
        // The same normalizer runs against `nat.mul`.
        let e = HolAc::from_forall(nat::nat_mul(), nat::mul_assoc(), nat::mul_comm()).engine();
        let mul = |a: Term, b: Term| nat::nat_mul().apply(a).unwrap().apply(b).unwrap();
        let t = mul(mul(v("c"), v("a")), v("b"));
        let thm = e.normalize(&t).unwrap();
        let (_, r) = thm.concl().as_eq().unwrap();
        let expected = mul(v("a"), mul(v("b"), v("c")));
        assert_eq!(r, &expected);
    }

    // ---- set.union / set.intersect are AC ----
    //
    // `init::set` ships `union_comm`/`union_assoc` (and the `inter` pair) as
    // free-variable EQUATIONS over `set α` (`α = tfree("a")`, vars `s, t, u`),
    // so the AC tactic decides `∪`/`∩` rearrangements the same way it does
    // `+`/`∧`.

    use covalence_core::defs::{set_intersect, set_union};

    fn set_alpha() -> Type {
        Type::tfree("a")
    }
    fn set_ty() -> Type {
        // `set α` is the carrier of the set ops' operands.
        crate::init::set::union_comm()
            .concl()
            .as_eq()
            .unwrap()
            .0
            .type_of()
            .unwrap()
    }
    fn sv(name: &str) -> Term {
        Term::free(name, set_ty())
    }

    #[test]
    fn set_union_respects_ac() {
        let e = HolAc::from_free(
            set_union(set_alpha()),
            crate::init::set::union_assoc(),
            crate::init::set::union_comm(),
            ["s", "t", "u"],
        )
        .engine();
        let un = |a: Term, b: Term| set_union(set_alpha()).apply(a).unwrap().apply(b).unwrap();
        // (u ∪ s) ∪ t   →   s ∪ (t ∪ u)
        let lhs = un(un(sv("u"), sv("s")), sv("t"));
        let thm = e.normalize(&lhs).unwrap();
        let (l, r) = thm.concl().as_eq().unwrap();
        assert_eq!(l, &lhs);
        assert_eq!(r, &un(sv("s"), un(sv("t"), sv("u"))));
        assert!(thm.hyps().is_empty());

        // and it decides an AC-equality:  (s ∪ t) ∪ u  =  u ∪ (t ∪ s)
        let a = un(un(sv("s"), sv("t")), sv("u"));
        let b = un(sv("u"), un(sv("t"), sv("s")));
        assert!(e.prove_eq(&a, &b).unwrap().hyps().is_empty());
    }

    #[test]
    fn set_intersect_respects_ac() {
        let e = HolAc::from_free(
            set_intersect(set_alpha()),
            crate::init::set::inter_assoc(),
            crate::init::set::inter_comm(),
            ["s", "t", "u"],
        )
        .engine();
        let it = |a: Term, b: Term| {
            set_intersect(set_alpha())
                .apply(a)
                .unwrap()
                .apply(b)
                .unwrap()
        };
        // (t ∩ s) ∩ u   →   s ∩ (t ∩ u)
        let lhs = it(it(sv("t"), sv("s")), sv("u"));
        let thm = e.normalize(&lhs).unwrap();
        let (_, r) = thm.concl().as_eq().unwrap();
        assert_eq!(r, &it(sv("s"), it(sv("t"), sv("u"))));
        assert!(thm.hyps().is_empty());
    }
}
