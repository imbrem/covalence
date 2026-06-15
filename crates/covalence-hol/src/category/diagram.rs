//! A high-level API for **commutative diagrams** of morphisms, built on
//! the point-free [`Category`] vocabulary.
//!
//! A commutative diagram is a directed graph whose nodes are objects and
//! whose edges are morphisms, together with the assertion that **any two
//! parallel paths are equal**. This module turns that picture into a
//! small, composable calculus:
//!
//! - [`Path`] — a *path* through the diagram: a chain of composable edges
//!   `a → … → b`. Folding a path with [`Path::morphism`] gives its
//!   composite morphism (the empty path at `a` folds to `id_a`).
//! - [`Cell`] — a *commuting cell*: a proof that two parallel paths have
//!   **equal** composites. A face of the diagram you assert commutes (via
//!   [`Cell::face`]), or one you *derive* by gluing smaller cells.
//!
//! Diagrams are then *chased* with three moves, each a thin wrapper over a
//! [`Category`] rule, so the whole calculus is model-generic and — in the
//! shallow HOL model — yields genuine, hypothesis-free theorems for every
//! step you take (the only hypotheses are the faces you choose to
//! *assume*):
//!
//! - **whisker** ([`Cell::whisker_pre`] / [`Cell::whisker_post`], and the
//!   path forms) — extend a commuting cell by pre- or post-composing both
//!   of its paths with another morphism (or path). This is the
//!   composition congruence [`comp_cong`](Category::comp_cong).
//! - **paste** ([`Cell::paste`], n-ary [`glue`]) — glue two cells that
//!   share a middle path end-to-end. This is transitivity
//!   [`trans`](Category::trans).
//! - **reassociate / unitate** ([`Cell::assoc`], [`Cell::id_left`],
//!   [`Cell::id_right`]) — the coherence cells that let you ignore how a
//!   composite is bracketed and drop identity edges.
//!
//! The payoff is [`paste_horizontal`]: pasting two commuting squares
//! along a shared edge into a commuting rectangle, proved *entirely*
//! through this API — the diagram-chase analogue of
//! [`swap_involution`](crate::monoidal::derived::swap_involution).

use crate::category::Category;

// ============================================================================
// Paths.
// ============================================================================

/// A directed **path** through a diagram: a chain of composable edges
/// `nodes[0] → nodes[1] → … → nodes[n]`, with `edges[i] : nodes[i] →
/// nodes[i+1]` (edges are listed in application order — `edges[0]` runs
/// first). The empty path (no edges) is the identity at its single node.
///
/// A path is pure data; it commits to no proof. Its composite morphism is
/// recovered on demand with [`morphism`](Path::morphism).
pub struct Path<C: Category> {
    nodes: Vec<C::Obj>,
    edges: Vec<C::Hom>,
}

// `Path` holds only `C::Obj` / `C::Hom` (both `Clone`); the model `C`
// itself is never stored, so `Clone` must not spuriously require `C: Clone`.
impl<C: Category> Clone for Path<C> {
    fn clone(&self) -> Self {
        Path {
            nodes: self.nodes.clone(),
            edges: self.edges.clone(),
        }
    }
}

impl<C: Category> Path<C> {
    /// The empty path at `obj` — the diagram's identity loop, folding to
    /// `id_obj`.
    pub fn point(obj: C::Obj) -> Self {
        Path {
            nodes: vec![obj],
            edges: Vec::new(),
        }
    }

    /// The one-edge path `src --e--> tgt`.
    pub fn edge(src: C::Obj, e: C::Hom, tgt: C::Obj) -> Self {
        Path {
            nodes: vec![src, tgt],
            edges: vec![e],
        }
    }

    /// Extend the path by one more edge `tgt() --e--> next`, walking
    /// further into the diagram.
    pub fn then(mut self, e: C::Hom, next: C::Obj) -> Self {
        self.nodes.push(next);
        self.edges.push(e);
        self
    }

    /// Append `other` to the end of this path. The two are assumed to meet
    /// (`self.tgt() == other.src()`); `other`'s leading node is dropped as
    /// the shared junction. (Object equality is not checked — the
    /// [`Category`] has no object equality — but a later
    /// [`morphism`](Path::morphism) fold will fail in the model if the
    /// edges do not actually compose.)
    pub fn concat(&self, other: &Path<C>) -> Path<C> {
        let mut nodes = self.nodes.clone();
        nodes.extend(other.nodes.iter().skip(1).cloned());
        let mut edges = self.edges.clone();
        edges.extend(other.edges.iter().cloned());
        Path { nodes, edges }
    }

    /// The source object (where the path starts).
    pub fn src(&self) -> &C::Obj {
        &self.nodes[0]
    }

    /// The target object (where the path ends).
    pub fn tgt(&self) -> &C::Obj {
        self.nodes
            .last()
            .expect("a path always has at least one node")
    }

    /// The number of edges (`0` for the identity path).
    pub fn len(&self) -> usize {
        self.edges.len()
    }

    /// Whether this is the identity path — no edges, just a single node.
    pub fn is_empty(&self) -> bool {
        self.edges.is_empty()
    }

    /// The path's edges, in application order.
    pub fn edges(&self) -> &[C::Hom] {
        &self.edges
    }

    /// The path's nodes, in order.
    pub fn nodes(&self) -> &[C::Obj] {
        &self.nodes
    }

    /// Fold the path to its composite morphism `src → tgt`.
    ///
    /// The empty path folds to `id_src`. A non-empty path
    /// `e_1, …, e_n` folds — by post-composition — to `e_n ∘ (… ∘ (e_2 ∘
    /// e_1))`, the canonical right-nested bracketing. Use the coherence
    /// cells ([`Cell::assoc`]) to relate it to any other bracketing.
    pub fn morphism(&self, c: &C) -> Result<C::Hom, C::Error> {
        let mut it = self.edges.iter().cloned();
        match it.next() {
            None => Ok(c.id(self.src().clone())),
            Some(first) => it.try_fold(first, |acc, e| c.comp(e, acc)),
        }
    }
}

// ============================================================================
// Commuting cells.
// ============================================================================

/// A **commuting cell**: a proof that two parallel paths through the
/// diagram have equal composite morphisms. The atoms are the *faces* you
/// assert ([`Cell::face`]); the combinators ([`paste`](Cell::paste),
/// [`whisker_pre`](Cell::whisker_pre), …) glue faces into larger
/// commuting regions.
///
/// A cell carries exactly one underlying [`Category::Proof`]; its two
/// sides are read back with [`sides`](Cell::sides).
pub struct Cell<C: Category> {
    proof: C::Proof,
}

impl<C: Category> Clone for Cell<C> {
    fn clone(&self) -> Self {
        Cell {
            proof: self.proof.clone(),
        }
    }
}

impl<C: Category> Cell<C> {
    /// Wrap a known equational proof as a commuting **face** — the way a
    /// diagram's hypotheses enter the calculus (e.g. a definitional
    /// equation `h = g ∘ f`, or an assumed square `b ∘ f = f' ∘ a`).
    pub fn face(proof: C::Proof) -> Self {
        Cell { proof }
    }

    /// The trivially-commuting cell on a single path: `⊢ p = p`, where `p`
    /// is the path's composite morphism.
    pub fn refl(c: &C, path: &Path<C>) -> Result<Self, C::Error> {
        Ok(Cell::face(c.refl(path.morphism(c)?)?))
    }

    /// The associativity coherence cell `⊢ (h ∘ g) ∘ f = h ∘ (g ∘ f)`.
    pub fn assoc(c: &C, h: C::Hom, g: C::Hom, f: C::Hom) -> Result<Self, C::Error> {
        Ok(Cell::face(c.assoc(h, g, f)?))
    }

    /// The left-unit coherence cell `⊢ id ∘ f = f` — collapse a leading
    /// identity edge.
    pub fn id_left(c: &C, f: C::Hom) -> Result<Self, C::Error> {
        Ok(Cell::face(c.id_left(f)?))
    }

    /// The right-unit coherence cell `⊢ f ∘ id = f` — collapse a trailing
    /// identity edge.
    pub fn id_right(c: &C, f: C::Hom) -> Result<Self, C::Error> {
        Ok(Cell::face(c.id_right(f)?))
    }

    /// The cell's two sides `(lhs, rhs)` — the composites of the two paths
    /// it proves equal.
    pub fn sides(&self, c: &C) -> (C::Hom, C::Hom) {
        c.concl(&self.proof)
    }

    /// Borrow the underlying proof.
    pub fn proof(&self) -> &C::Proof {
        &self.proof
    }

    /// Consume the cell, yielding the underlying proof — the bridge back
    /// to the model (a HOL [`Thm`](covalence_core::Thm) in the shallow
    /// model).
    pub fn into_proof(self) -> C::Proof {
        self.proof
    }

    /// Flip the cell: from `lhs = rhs` derive `rhs = lhs`.
    pub fn flip(self, c: &C) -> Result<Self, C::Error> {
        Ok(Cell::face(c.sym(self.proof)?))
    }

    /// **Paste** two cells sharing a middle path: from `this : p = q` and
    /// `next : q = r` derive `p = r`. Transitivity — the vertical
    /// composition of diagram chases. Fails in the model if the cells do
    /// not actually meet (`this`'s right side ≠ `next`'s left side).
    pub fn paste(self, c: &C, next: Cell<C>) -> Result<Self, C::Error> {
        Ok(Cell::face(c.trans(self.proof, next.proof)?))
    }

    /// **Whisker on the right** (pre-compose): from `p = q` derive `p ∘ k
    /// = q ∘ k`, running `k` *before* both sides of the cell.
    pub fn whisker_pre(self, c: &C, k: C::Hom) -> Result<Self, C::Error> {
        let k_refl = c.refl(k)?;
        Ok(Cell::face(c.comp_cong(self.proof, k_refl)?))
    }

    /// **Whisker on the left** (post-compose): from `p = q` derive `h ∘ p
    /// = h ∘ q`, running `h` *after* both sides of the cell.
    pub fn whisker_post(self, c: &C, h: C::Hom) -> Result<Self, C::Error> {
        let h_refl = c.refl(h)?;
        Ok(Cell::face(c.comp_cong(h_refl, self.proof)?))
    }

    /// Whisker on the right by a whole [`Path`] (its composite morphism).
    pub fn whisker_pre_path(self, c: &C, k: &Path<C>) -> Result<Self, C::Error> {
        let km = k.morphism(c)?;
        self.whisker_pre(c, km)
    }

    /// Whisker on the left by a whole [`Path`] (its composite morphism).
    pub fn whisker_post_path(self, c: &C, h: &Path<C>) -> Result<Self, C::Error> {
        let hm = h.morphism(c)?;
        self.whisker_post(c, hm)
    }
}

// ============================================================================
// Chasing: gluing a chain of cells.
// ============================================================================

/// **Chase** a commuting region by pasting a non-empty chain of cells
/// end-to-end: given `c_0 : p_0 = p_1`, `c_1 : p_1 = p_2`, …, conclude
/// `p_0 = p_n`. The diagram-chase workhorse — list the equal steps along
/// the way and [`glue`] folds them with [`Cell::paste`].
///
/// Returns `None` if `cells` is empty (there is nothing to conclude);
/// otherwise the chase, which still fails in the model if consecutive
/// cells do not share their middle path. See [`glue`] for the common case
/// where a non-empty chain is statically known.
pub fn try_glue<C: Category>(
    c: &C,
    cells: impl IntoIterator<Item = Cell<C>>,
) -> Option<Result<Cell<C>, C::Error>> {
    let mut it = cells.into_iter();
    let first = it.next()?;
    Some(it.try_fold(first, |acc, next| acc.paste(c, next)))
}

/// [`try_glue`] for a chain known to be non-empty. **Panics** if `cells`
/// is empty — the chase combinators always produce at least one step, so
/// the internal call sites here uphold that.
pub fn glue<C: Category>(
    c: &C,
    cells: impl IntoIterator<Item = Cell<C>>,
) -> Result<Cell<C>, C::Error> {
    try_glue(c, cells).expect("diagram::glue: cannot chase an empty chain of cells")
}

// ============================================================================
// Derived diagram lemmas.
// ============================================================================

/// **Paste two commuting squares into a commuting rectangle.**
///
/// Given the squares (each commuting along its two paths)
///
/// ```text
///        f          g
///    A ─────▶ B ─────▶ C
///    │        │        │
///  a │   ⟲    │ b  ⟲   │ cc
///    ▼        ▼        ▼
///    A'─────▶ B'─────▶ C'
///        f'         g'
/// ```
///
/// with `left : ⊢ b ∘ f = f' ∘ a` and `right : ⊢ cc ∘ g = g' ∘ b`,
/// derive the outer rectangle `⊢ cc ∘ (g ∘ f) = (g' ∘ f') ∘ a`.
///
/// Proved purely by chasing: reassociate, whisker each square's face by
/// the opposite edge, and paste. No model internals are touched, so any
/// [`Category`] — and in the shallow HOL model, any genuine theorems for
/// the two faces — yields a genuine theorem for the rectangle.
#[allow(clippy::too_many_arguments)]
pub fn paste_horizontal<C: Category>(
    c: &C,
    f: C::Hom,
    g: C::Hom,
    a: C::Hom,
    b: C::Hom,
    cc: C::Hom,
    f_low: C::Hom,
    g_low: C::Hom,
    left: Cell<C>,
    right: Cell<C>,
) -> Result<Cell<C>, C::Error> {
    // cc ∘ (g ∘ f) = (cc ∘ g) ∘ f          [sym assoc]
    let step1 = Cell::assoc(c, cc.clone(), g.clone(), f.clone())?.flip(c)?;
    // (cc ∘ g) ∘ f = (g' ∘ b) ∘ f          [right face, whiskered by f]
    let step2 = right.whisker_pre(c, f.clone())?;
    // (g' ∘ b) ∘ f = g' ∘ (b ∘ f)          [assoc]
    let step3 = Cell::assoc(c, g_low.clone(), b.clone(), f.clone())?;
    // g' ∘ (b ∘ f) = g' ∘ (f' ∘ a)         [left face, whiskered by g']
    let step4 = left.whisker_post(c, g_low.clone())?;
    // g' ∘ (f' ∘ a) = (g' ∘ f') ∘ a        [sym assoc]
    let step5 = Cell::assoc(c, g_low, f_low, a)?.flip(c)?;
    glue(c, [step1, step2, step3, step4, step5])
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::category::Hol;
    use crate::init::ext::TermExt;
    use covalence_core::{Term, Thm, Type};

    fn obj(n: &str) -> Type {
        Type::tfree(n)
    }

    fn mor(name: &str, dom: Type, cod: Type) -> Term {
        Term::free(name, Type::fun(dom, cod))
    }

    /// A face hypothesis `⊢ lhs = rhs` (carried as a self-hyp via
    /// `Thm::assume`) — stands in for a square the caller asserts commutes.
    fn assume_face(lhs: &Term, rhs: &Term) -> Cell<Hol> {
        let eq = lhs.clone().equals(rhs.clone()).unwrap();
        Cell::face(Thm::assume(eq).unwrap())
    }

    #[test]
    fn concat_joins_paths_at_the_shared_node() {
        let h = Hol::new();
        let (a, b, c) = (obj("a"), obj("b"), obj("c"));
        let f = mor("f", a.clone(), b.clone());
        let g = mor("g", b.clone(), c.clone());
        let p = Path::<Hol>::edge(a.clone(), f.clone(), b.clone());
        let q = Path::<Hol>::edge(b.clone(), g.clone(), c.clone());
        let pq = p.concat(&q);
        // The junction node `b` is shared, not duplicated: a → b → c.
        assert_eq!(pq.nodes(), &[a.clone(), b.clone(), c.clone()]);
        assert_eq!(pq.len(), 2);
        // Same composite as the two-edge path built directly: g ∘ f.
        assert_eq!(
            pq.morphism(&h).unwrap(),
            crate::init::cat::comp(&g, &f).unwrap()
        );
    }

    #[test]
    fn path_folds_to_composite() {
        let h = Hol::new();
        let (a, b, c) = (obj("a"), obj("b"), obj("c"));
        let f = mor("f", a.clone(), b.clone());
        let g = mor("g", b.clone(), c.clone());
        let path = Path::<Hol>::edge(a.clone(), f.clone(), b.clone()).then(g.clone(), c.clone());
        assert_eq!(path.len(), 2);
        assert_eq!(path.src(), &a);
        assert_eq!(path.tgt(), &c);
        // Composite is g ∘ f.
        let composite = path.morphism(&h).unwrap();
        let expected = crate::init::cat::comp(&g, &f).unwrap();
        assert_eq!(composite, expected);
    }

    #[test]
    fn empty_path_is_identity() {
        let h = Hol::new();
        let a = obj("a");
        let p = Path::<Hol>::point(a.clone());
        assert!(p.is_empty());
        assert_eq!(p.morphism(&h).unwrap(), h.id(a));
    }

    #[test]
    fn paste_glues_two_faces() {
        // p = q  and  q = r  ⟹  p = r, by transitivity.
        let h = Hol::new();
        let (a, b) = (obj("a"), obj("b"));
        let p = mor("p", a.clone(), b.clone());
        let q = mor("q", a.clone(), b.clone());
        let r = mor("r", a.clone(), b.clone());
        let c1 = assume_face(&p, &q);
        let c2 = assume_face(&q, &r);
        let glued = c1.paste(&h, c2).unwrap();
        let (l, rr) = glued.sides(&h);
        assert_eq!(l, p);
        assert_eq!(rr, r);
    }

    #[test]
    fn whisker_extends_a_face() {
        // From f = f' derive h ∘ f = h ∘ f' and f ∘ k = f' ∘ k.
        let h = Hol::new();
        let (a, b, c) = (obj("a"), obj("b"), obj("c"));
        let f = mor("f", b.clone(), c.clone());
        let f2 = mor("f2", b.clone(), c.clone());
        let hh = mor("h", c.clone(), obj("d"));
        let k = mor("k", a.clone(), b.clone());

        let post = assume_face(&f, &f2).whisker_post(&h, hh.clone()).unwrap();
        let (pl, pr) = post.sides(&h);
        assert_eq!(pl, crate::init::cat::comp(&hh, &f).unwrap());
        assert_eq!(pr, crate::init::cat::comp(&hh, &f2).unwrap());

        let pre = assume_face(&f, &f2).whisker_pre(&h, k.clone()).unwrap();
        let (kl, kr) = pre.sides(&h);
        assert_eq!(kl, crate::init::cat::comp(&f, &k).unwrap());
        assert_eq!(kr, crate::init::cat::comp(&f2, &k).unwrap());
    }

    #[test]
    fn paste_horizontal_builds_the_rectangle() {
        let h = Hol::new();
        let (aa, bb, cc_o) = (obj("A"), obj("B"), obj("C"));
        let (aa2, bb2, cc2) = (obj("A'"), obj("B'"), obj("C'"));
        let f = mor("f", aa.clone(), bb.clone());
        let g = mor("g", bb.clone(), cc_o.clone());
        let a = mor("a", aa.clone(), aa2.clone());
        let b = mor("b", bb.clone(), bb2.clone());
        let cm = mor("c", cc_o.clone(), cc2.clone());
        let f_low = mor("f'", aa2.clone(), bb2.clone());
        let g_low = mor("g'", bb2.clone(), cc2.clone());

        // Faces: b ∘ f = f' ∘ a  and  c ∘ g = g' ∘ b.
        let left = assume_face(
            &crate::init::cat::comp(&b, &f).unwrap(),
            &crate::init::cat::comp(&f_low, &a).unwrap(),
        );
        let right = assume_face(
            &crate::init::cat::comp(&cm, &g).unwrap(),
            &crate::init::cat::comp(&g_low, &b).unwrap(),
        );

        let rect = paste_horizontal(
            &h,
            f.clone(),
            g.clone(),
            a.clone(),
            b.clone(),
            cm.clone(),
            f_low.clone(),
            g_low.clone(),
            left,
            right,
        )
        .unwrap();

        // Conclusion: c ∘ (g ∘ f) = (g' ∘ f') ∘ a.
        let (lhs, rhs) = rect.sides(&h);
        let expect_l =
            crate::init::cat::comp(&cm, &crate::init::cat::comp(&g, &f).unwrap()).unwrap();
        let expect_r =
            crate::init::cat::comp(&crate::init::cat::comp(&g_low, &f_low).unwrap(), &a).unwrap();
        assert_eq!(lhs, expect_l);
        assert_eq!(rhs, expect_r);

        // The only hypotheses are the two assumed faces — the chase added
        // none of its own, and used no observers.
        let proof = rect.proof();
        assert!(proof.has_no_obs());
        assert_eq!(proof.hyps().len(), 2);
    }
}
