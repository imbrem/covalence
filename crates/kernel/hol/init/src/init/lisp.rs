//! **A basic Lisp over the carved `sexpr`** — the ACL2 groundwork.
//!
//! This module is a *consumer* of the carved (exact-type) `sexpr` carrier
//! ([`mod@crate::init::inductive::carved`]): it defines the classic Lisp
//! operations and a handful of **total recursive functions** over
//! S-expressions, each with its computation laws, and proves genuine
//! **structural-induction** theorems ACL2-style through the carrier's
//! induction principle. Everything is bundled on [`Lisp`].
//!
//! ## What is provided
//!
//! - the destructors/constructors `car`, `cdr`, `cons` (re-exported
//!   from the carved carrier — `car`/`cdr` are *recursion-position
//!   extractors*, which the rank-1 Church carrier provably cannot state);
//! - the tests `consp` (`is it a cons?`) and `atom?` (the ACL2 complement),
//!   each a `bool`-valued catamorphism with computation laws;
//! - `len` — the top-level list length, a `nat`-valued catamorphism
//!   (`len (scons h t) = succ (len t)`);
//! - `append` — list concatenation, a **paramorphism** (its `scons` step
//!   re-uses the raw head `h`: `append (scons h t) w = scons h (append t w)`);
//! - the induction theorems [`Lisp::append_assoc`]
//!   (`append (append x y) z = append x (append y z)`) and [`Lisp::len_append`]
//!   (`len (append x y) = len x + len y`), each proved by structural
//!   induction on the first argument — the archetypal ACL2 `defun` +
//!   `:induction` pair, landed here as ordinary derived theorems.
//!
//! Everything flows through existing kernel rules and the carved carrier's
//! recursor + freeness; nothing here is trusted. See
//! `notes/vibes/inductive-api-design.md` §4 for the ACL2-theory roadmap
//! (this module is its first concrete slice) and the universal-vs-exact
//! backend split (Church = no `cdr`; carved = full Lisp).

use std::sync::LazyLock;

use covalence_core::{Error, Result, Term, Type, subst};
use covalence_hol_eval::EvalThm as Thm;
use covalence_hol_eval::derived::DerivedRules;

use crate::init::ext::{TermExt, ThmExt};
use crate::init::inductive::carved::{CarvedSExpr, apply_def, carved};
use crate::init::nat::{add, add_base, add_step, nat_add, nat_succ, succ, zero};

fn bytes_ty() -> Type {
    Type::bytes()
}

// ============================================================================
// The Lisp theory (built once)
// ============================================================================

/// The Lisp operations over the carved `sexpr`: the boolean tests and the
/// total recursive functions, as [`Thm::define`]d constants paired with
/// their defining equations. Built exactly once ([`lisp`]).
pub struct Lisp {
    cs: &'static CarvedSExpr,
    /// `consp : sexpr → bool`.
    pub consp: Term,
    consp_eq: Thm,
    /// `atom? : sexpr → bool` (the ACL2 complement of [`Lisp::consp`]).
    pub atom_p: Term,
    atom_p_eq: Thm,
    /// `len : sexpr → nat`.
    pub len: Term,
    len_eq: Thm,
    /// `append : sexpr → sexpr → sexpr`.
    pub append: Term,
    append_eq: Thm,
}

/// The process-global Lisp theory.
pub fn lisp() -> Result<&'static Lisp> {
    static LISP: LazyLock<std::result::Result<Lisp, String>> =
        LazyLock::new(|| Lisp::build().map_err(|e| e.to_string()));
    LISP.as_ref()
        .map_err(|e| Error::ConnectiveRule(format!("lisp build failed: {e}")))
}

/// Split a `⊢ C = body` definition into `(C, the equation)`.
fn defined(name: &str, body: Term) -> Result<(Term, Thm)> {
    let eq = Thm::define(name, body)?;
    let c = eq.concl().as_eq().ok_or(Error::NotAnEquation)?.0.clone();
    Ok((c, eq))
}

impl Lisp {
    fn build() -> Result<Lisp> {
        let cs = carved()?;
        let tau = &cs.tau;

        // A `bool`-valued catamorphism: leaves answer `leaf`, `scons`
        // answers `node` (raw arguments + subtree images all dropped).
        let bool_cata = |leaf: bool, node: bool| -> Result<Term> {
            let bt = Type::bool();
            let sa = Term::abs(bytes_ty(), Term::bool_lit(leaf)); // λb. leaf
            let sn = Term::bool_lit(leaf);
            let sc = {
                // λh t bh bt. node
                let l_bt = Term::abs(bt.clone(), Term::bool_lit(node));
                let l_bh = Term::abs(bt.clone(), l_bt);
                let l_t = Term::abs(tau.clone(), l_bh);
                Term::abs(tau.clone(), l_t)
            };
            cs.prec(&[sa, sn, sc], &Type::bool())
        };
        let (consp, consp_eq) = defined("lisp.consp", bool_cata(false, true)?)?;
        let (atom_p, atom_p_eq) = defined("lisp.atom", bool_cata(true, false)?)?;

        // len := prec [λb. 0, 0, λh t bh bt. succ bt] — a nat catamorphism.
        let (len, len_eq) = defined("lisp.len", cs.prec(&Self::len_steps(cs), &Type::nat())?)?;

        // append := λx y. prec [λb. y, y, λh t bh bt. scons h bt] x — a
        // paramorphism (the `scons` step re-uses the raw head `h`), with the
        // second argument `y` threaded as the base of every leaf.
        let (append, append_eq) = {
            let x = Term::free("__x", tau.clone());
            let y = Term::free("__y", tau.clone());
            let rec_x = cs.prec(&Self::append_steps(cs, &y)?, tau)?.apply(x)?;
            let l_y = Term::abs(tau.clone(), subst::close(&rec_x, "__y"));
            let body = Term::abs(tau.clone(), subst::close(&l_y, "__x"));
            defined("lisp.append", body)?
        };

        Ok(Lisp {
            cs,
            consp,
            consp_eq,
            atom_p,
            atom_p_eq,
            len,
            len_eq,
            append,
            append_eq,
        })
    }

    // -- re-exported carved destructors/constructor --

    /// `car : sexpr → sexpr` (`car (scons h t) = h`; leaves default to `snil`).
    pub fn car(&self) -> &Term {
        &self.cs.car
    }

    /// `cdr : sexpr → sexpr` (`cdr (scons h t) = t`; leaves default to `snil`).
    pub fn cdr(&self) -> &Term {
        &self.cs.cdr
    }

    /// `cons = scons : sexpr → sexpr → sexpr`.
    pub fn cons(&self) -> &Term {
        &self.cs.scons
    }

    // ------------------------------------------------------------------
    // Step arrays
    // ------------------------------------------------------------------

    /// The `len` step terms (`λb. 0`, `0`, `λh t bh bt. succ bt`).
    fn len_steps(cs: &CarvedSExpr) -> [Term; 3] {
        let nat = Type::nat();
        let sa = Term::abs(bytes_ty(), zero());
        let sn = zero();
        let sc = {
            let bt = Term::free("__bt", nat.clone());
            let l_bt = Term::abs(nat.clone(), subst::close(&succ(bt), "__bt"));
            let l_bh = Term::abs(nat.clone(), l_bt);
            let l_t = Term::abs(cs.tau.clone(), l_bh);
            Term::abs(cs.tau.clone(), l_t)
        };
        [sa, sn, sc]
    }

    /// The `append` step terms at base `w` (`λb. w`, `w`, `λh t bh bt. scons h bt`).
    fn append_steps(cs: &CarvedSExpr, w: &Term) -> Result<[Term; 3]> {
        let tau = &cs.tau;
        let sa = Term::abs(bytes_ty(), w.clone());
        let sn = w.clone();
        // λh t bh bt. scons h bt  (raw head `h` re-used; `t`, `bh` dropped).
        let h = Term::free("__h", tau.clone());
        let bt = Term::free("__bt", tau.clone());
        let scons_h_bt = cs.scons.clone().apply(h)?.apply(bt)?;
        let l_bt = Term::abs(tau.clone(), subst::close(&scons_h_bt, "__bt"));
        let l_bh = Term::abs(tau.clone(), l_bt);
        let l_t = Term::abs(tau.clone(), l_bh);
        let sc = Term::abs(tau.clone(), subst::close(&l_t, "__h"));
        Ok([sa, sn, sc])
    }

    // ------------------------------------------------------------------
    // Computation laws
    // ------------------------------------------------------------------

    /// `⊢ consp (atom b) = F`, `⊢ consp snil = F`, `⊢ consp (scons h t) = T`.
    pub fn consp_atom(&self, b: &Term) -> Result<Thm> {
        self.bool_leaf(
            &self.consp_eq,
            &Self::consp_steps(self.cs),
            LeafArg::Atom(b),
        )
    }

    /// `⊢ consp snil = F`.
    pub fn consp_nil(&self) -> Result<Thm> {
        self.bool_leaf(&self.consp_eq, &Self::consp_steps(self.cs), LeafArg::Nil)
    }

    /// `⊢ consp (scons h t) = T`.
    pub fn consp_scons(&self, h: &Term, t: &Term) -> Result<Thm> {
        self.bool_node(&self.consp_eq, &Self::consp_steps(self.cs), h, t)
    }

    /// `⊢ atom? (atom b) = T`.
    pub fn atom_atom(&self, b: &Term) -> Result<Thm> {
        self.bool_leaf(
            &self.atom_p_eq,
            &Self::atom_steps(self.cs),
            LeafArg::Atom(b),
        )
    }

    /// `⊢ atom? snil = T`.
    pub fn atom_nil(&self) -> Result<Thm> {
        self.bool_leaf(&self.atom_p_eq, &Self::atom_steps(self.cs), LeafArg::Nil)
    }

    /// `⊢ atom? (scons h t) = F`.
    pub fn atom_scons(&self, h: &Term, t: &Term) -> Result<Thm> {
        self.bool_node(&self.atom_p_eq, &Self::atom_steps(self.cs), h, t)
    }

    fn consp_steps(cs: &CarvedSExpr) -> [Term; 3] {
        Self::bool_cata_steps(cs, false, true)
    }
    fn atom_steps(cs: &CarvedSExpr) -> [Term; 3] {
        Self::bool_cata_steps(cs, true, false)
    }
    fn bool_cata_steps(cs: &CarvedSExpr, leaf: bool, node: bool) -> [Term; 3] {
        let bt = Type::bool();
        let sa = Term::abs(bytes_ty(), Term::bool_lit(leaf));
        let sn = Term::bool_lit(leaf);
        let l_bt = Term::abs(bt.clone(), Term::bool_lit(node));
        let l_bh = Term::abs(bt.clone(), l_bt);
        let l_t = Term::abs(cs.tau.clone(), l_bh);
        let sc = Term::abs(cs.tau.clone(), l_t);
        [sa, sn, sc]
    }

    /// A `bool` catamorphism's leaf law: `⊢ f (atom b|snil) = leaf`.
    fn bool_leaf(&self, def_eq: &Thm, steps: &[Term; 3], leaf: LeafArg<'_>) -> Result<Thm> {
        match leaf {
            LeafArg::Atom(b) => {
                let atom_b = self.cs.atom.clone().apply(b.clone())?;
                let e = def_eq.clone().cong_fn(atom_b)?;
                let comp = self
                    .cs
                    .prec_eq(steps, 0, &Type::bool())?
                    .all_elim(b.clone())?;
                e.trans(comp)?.reduce_rhs()
            }
            LeafArg::Nil => {
                let e = def_eq.clone().cong_fn(self.cs.snil.clone())?;
                let comp = self.cs.prec_eq(steps, 1, &Type::bool())?;
                e.trans(comp)
            }
        }
    }

    /// A `bool` catamorphism's node law: `⊢ f (scons h t) = node`.
    fn bool_node(&self, def_eq: &Thm, steps: &[Term; 3], h: &Term, t: &Term) -> Result<Thm> {
        let scons_ht = self.cs.scons.clone().apply(h.clone())?.apply(t.clone())?;
        let e = def_eq.clone().cong_fn(scons_ht)?;
        let comp = self
            .cs
            .prec_eq(steps, 2, &Type::bool())?
            .all_elim(h.clone())?
            .all_elim(t.clone())?;
        e.trans(comp)?.reduce_rhs()
    }

    /// `⊢ len (atom b) = 0` / `⊢ len snil = 0`.
    pub fn len_leaf(&self, leaf: LeafArg<'_>) -> Result<Thm> {
        let steps = Self::len_steps(self.cs);
        match leaf {
            LeafArg::Atom(b) => {
                let atom_b = self.cs.atom.clone().apply(b.clone())?;
                let e = self.len_eq.clone().cong_fn(atom_b)?;
                let comp = self
                    .cs
                    .prec_eq(&steps, 0, &Type::nat())?
                    .all_elim(b.clone())?;
                e.trans(comp)?.reduce_rhs()
            }
            LeafArg::Nil => {
                let e = self.len_eq.clone().cong_fn(self.cs.snil.clone())?;
                let comp = self.cs.prec_eq(&steps, 1, &Type::nat())?;
                e.trans(comp)
            }
        }
    }

    /// `⊢ len (scons h t) = succ (len t)`.
    pub fn len_scons(&self, h: &Term, t: &Term) -> Result<Thm> {
        let steps = Self::len_steps(self.cs);
        let scons_ht = self.cs.scons.clone().apply(h.clone())?.apply(t.clone())?;
        let e = self.len_eq.clone().cong_fn(scons_ht)?;
        let comp = self
            .cs
            .prec_eq(&steps, 2, &Type::nat())?
            .all_elim(h.clone())?
            .all_elim(t.clone())?;
        // `comp` RHS holds the *recursor images* `rec s⃗ h` / `rec s⃗ t` — fold
        // them back to `len h` / `len t` (opaque, β-inert) *before* β-reducing
        // the step, so `reduce_rhs` cannot unfold the recursor's ε-term.
        let lh = self.len_eq.clone().cong_fn(h.clone())?; // len h = rec s⃗ h
        let lt = self.len_eq.clone().cong_fn(t.clone())?; // len t = rec s⃗ t
        let e = e.trans(comp)?;
        let e = e.rhs_conv(|tm| tm.rw_all(&lh.sym()?))?;
        let e = e.rhs_conv(|tm| tm.rw_all(&lt.sym()?))?;
        e.reduce_rhs() // succ (len t)
    }

    /// `⊢ append (atom b) w = w` / `⊢ append snil w = w`.
    pub fn append_leaf(&self, leaf: LeafArg<'_>, w: &Term) -> Result<Thm> {
        let steps = Self::append_steps(self.cs, w)?;
        let tau = &self.cs.tau;
        match leaf {
            LeafArg::Atom(b) => {
                let atom_b = self.cs.atom.clone().apply(b.clone())?;
                let e = apply_def(&self.append_eq, &[atom_b, w.clone()])?;
                let comp = self.cs.prec_eq(&steps, 0, tau)?.all_elim(b.clone())?;
                e.trans(comp)?.reduce_rhs()
            }
            LeafArg::Nil => {
                let e = apply_def(&self.append_eq, &[self.cs.snil.clone(), w.clone()])?;
                let comp = self.cs.prec_eq(&steps, 1, tau)?;
                e.trans(comp)
            }
        }
    }

    /// `⊢ append (scons h t) w = scons h (append t w)`.
    pub fn append_scons(&self, h: &Term, t: &Term, w: &Term) -> Result<Thm> {
        let steps = Self::append_steps(self.cs, w)?;
        let tau = &self.cs.tau;
        let scons_ht = self.cs.scons.clone().apply(h.clone())?.apply(t.clone())?;
        let e = apply_def(&self.append_eq, &[scons_ht, w.clone()])?;
        let comp = self
            .cs
            .prec_eq(&steps, 2, tau)?
            .all_elim(h.clone())?
            .all_elim(t.clone())?;
        // Fold the recursor images `rec s⃗ h` / `rec s⃗ t` back to
        // `append h w` / `append t w` (opaque, β-inert) *before* reducing the
        // step, so `reduce_rhs` cannot unfold the recursor's ε-term.
        let ah = apply_def(&self.append_eq, &[h.clone(), w.clone()])?; // append h w = rec s⃗ h
        let at = apply_def(&self.append_eq, &[t.clone(), w.clone()])?; // append t w = rec s⃗ t
        let e = e.trans(comp)?;
        let e = e.rhs_conv(|tm| tm.rw_all(&ah.sym()?))?;
        let e = e.rhs_conv(|tm| tm.rw_all(&at.sym()?))?;
        e.reduce_rhs() // scons h (append t w)
    }

    // ------------------------------------------------------------------
    // Structural-induction theorems
    // ------------------------------------------------------------------

    /// `⊢ ∀y z x. append (append x y) z = append x (append y z)` — append
    /// associativity, by structural induction on `x` (the ACL2 archetype;
    /// only the *tail* induction hypothesis is used).
    pub fn append_assoc(&self) -> Result<Thm> {
        let tau = self.cs.tau.clone();
        let y = Term::free("y", tau.clone());
        let z = Term::free("z", tau.clone());
        let ap = |a: &Term, b: &Term| self.append.clone().apply(a.clone())?.apply(b.clone());
        let yz = ap(&y, &z)?;

        // motive := λx. append (append x y) z = append x (append y z).
        let motive = {
            let x = Term::free("x", tau.clone());
            let lhs = ap(&ap(&x, &y)?, &z)?;
            let rhs = ap(&x, &yz)?;
            Term::abs(tau.clone(), subst::close(&lhs.equals(rhs)?, "x"))
        };

        // Leaf cases: both sides collapse to `append y z`.
        let leaf_case = |leaf: LeafArg<'_>, leaf_c: Term| -> Result<Thm> {
            // append (append leaf y) z = append y z  (rewrite inner leaf law)
            let inner = self.append_leaf(leaf, &y)?; // append leaf y = y
            let lhs_eq = inner.cong_arg(self.append.clone())?.cong_fn(z.clone())?;
            // append leaf (append y z) = append y z
            let rhs_eq = self.append_leaf(leaf, &yz)?;
            let raw = lhs_eq.trans(rhs_eq.sym()?)?;
            crate::init::eq::beta_expand(&motive, leaf_c, raw)
        };
        let b = Term::free("b", bytes_ty());
        let case_atom = leaf_case(LeafArg::Atom(&b), self.cs.atom.clone().apply(b.clone())?)?;
        let case_nil = leaf_case(LeafArg::Nil, self.cs.snil.clone())?;

        // Cons case: ⊢ P h ⟹ P t ⟹ P (scons h t) (only P t is used).
        let case_cons = {
            let h = Term::free("h", tau.clone());
            let t = Term::free("t", tau.clone());
            let ph = motive.clone().apply(h.clone())?;
            let pt = motive.clone().apply(t.clone())?;
            let ih = crate::init::eq::beta_reduce(Thm::assume(pt.clone())?)?; // append(append t y)z = append t (append y z)

            let scons_ht = self.cs.scons.clone().apply(h.clone())?.apply(t.clone())?;
            // LHS: append (append (scons h t) y) z
            //    = append (scons h (append t y)) z            (append_scons)
            //    = scons h (append (append t y) z)            (append_scons)
            let s1 = self.append_scons(&h, &t, &y)?; // append (scons h t) y = scons h (append t y)
            let lhs1 = s1.cong_arg(self.append.clone())?.cong_fn(z.clone())?;
            let t_y = ap(&t, &y)?;
            let s2 = self.append_scons(&h, &t_y, &z)?;
            let lhs = lhs1.trans(s2)?; // = scons h (append (append t y) z)
            // rewrite the inner via IH: scons h (append t (append y z))
            let scons_h = self.cs.scons.clone().apply(h.clone())?;
            let mid = ih.cong_arg(scons_h)?; // scons h (append(append t y)z) = scons h (append t (append y z))
            // RHS: append (scons h t) (append y z) = scons h (append t (append y z))
            let s3 = self.append_scons(&h, &t, &yz)?;
            let raw = lhs.trans(mid)?.trans(s3.sym()?)?;

            crate::init::eq::beta_expand(&motive, scons_ht, raw)?
                .imp_intro(&pt)?
                .imp_intro(&ph)?
        };

        let by_x = self
            .cs
            .induct(&motive, vec![case_atom, case_nil, case_cons])?; // ⊢ ∀x. P x
        by_x.all_intro("z", tau.clone())?.all_intro("y", tau)
    }

    /// `⊢ ∀y x. len (append x y) = len x + len y` — proved by structural
    /// induction on `x`, tying the catamorphism [`Lisp::len`], the paramorphism
    /// [`Lisp::append`], and the `nat` recursion laws together (the ACL2
    /// arithmetic-induction archetype).
    pub fn len_append(&self) -> Result<Thm> {
        let tau = self.cs.tau.clone();
        let y = Term::free("y", tau.clone());
        let len_of = |t: &Term| self.len.clone().apply(t.clone());
        let ap = |a: &Term, b: &Term| self.append.clone().apply(a.clone())?.apply(b.clone());
        let len_y = len_of(&y)?;

        // motive := λx. len (append x y) = len x + len y.
        let motive = {
            let x = Term::free("x", tau.clone());
            let lhs = len_of(&ap(&x, &y)?)?;
            let rhs = add(len_of(&x)?, len_y.clone());
            Term::abs(tau.clone(), subst::close(&lhs.equals(rhs)?, "x"))
        };

        // Leaf cases: len (append leaf y) = len y = 0 + len y = len leaf + len y.
        let leaf_case = |leaf: LeafArg<'_>, leaf_c: Term| -> Result<Thm> {
            // LHS: len (append leaf y) = len y.
            let app_leaf = self.append_leaf(leaf, &y)?; // append leaf y = y
            let lhs = app_leaf.cong_arg(self.len.clone())?; // len (append leaf y) = len y
            // RHS chain: len leaf + len y = 0 + len y = len y.
            let len_leaf = self.len_leaf(leaf)?; // len leaf = 0
            let step = len_leaf.cong_arg(nat_add())?.cong_fn(len_y.clone())?; // len leaf + len y = 0 + len y
            let base = add_base().all_elim(len_y.clone())?; // 0 + len y = len y
            let rhs = step.trans(base)?; // len leaf + len y = len y
            let raw = lhs.trans(rhs.sym()?)?;
            crate::init::eq::beta_expand(&motive, leaf_c, raw)
        };
        let b = Term::free("b", bytes_ty());
        let case_atom = leaf_case(LeafArg::Atom(&b), self.cs.atom.clone().apply(b.clone())?)?;
        let case_nil = leaf_case(LeafArg::Nil, self.cs.snil.clone())?;

        // Cons case.
        let case_cons = {
            let h = Term::free("h", tau.clone());
            let t = Term::free("t", tau.clone());
            let ph = motive.clone().apply(h.clone())?;
            let pt = motive.clone().apply(t.clone())?;
            let ih = crate::init::eq::beta_reduce(Thm::assume(pt.clone())?)?; // len (append t y) = len t + len y
            let scons_ht = self.cs.scons.clone().apply(h.clone())?.apply(t.clone())?;

            // LHS: len (append (scons h t) y)
            //    = len (scons h (append t y))     (append_scons)
            //    = succ (len (append t y))        (len_scons)
            //    = succ (len t + len y)           (IH)
            let s1 = self.append_scons(&h, &t, &y)?;
            let lhs1 = s1.cong_arg(self.len.clone())?; // len(append(scons h t)y) = len(scons h (append t y))
            let t_y = ap(&t, &y)?;
            let ls = self.len_scons(&h, &t_y)?; // len(scons h (append t y)) = succ(len(append t y))
            let lhs2 = lhs1.trans(ls)?;
            let ih_s = ih.cong_arg(nat_succ())?; // succ(len(append t y)) = succ(len t + len y)
            let lhs = lhs2.trans(ih_s)?; // = succ (len t + len y)

            // RHS: len (scons h t) + len y
            //    = succ (len t) + len y           (len_scons)
            //    = succ (len t + len y)           (add_step)
            let lc = self.len_scons(&h, &t)?; // len(scons h t) = succ(len t)
            let rhs1 = lc.cong_arg(nat_add())?.cong_fn(len_y.clone())?; // len(scons h t)+len y = succ(len t)+len y
            let as_ = add_step().all_elim(len_of(&t)?)?.all_elim(len_y.clone())?; // succ(len t)+len y = succ(len t + len y)
            let rhs = rhs1.trans(as_)?; // = succ (len t + len y)

            let raw = lhs.trans(rhs.sym()?)?;
            crate::init::eq::beta_expand(&motive, scons_ht, raw)?
                .imp_intro(&pt)?
                .imp_intro(&ph)?
        };

        let by_x = self
            .cs
            .induct(&motive, vec![case_atom, case_nil, case_cons])?;
        by_x.all_intro("y", tau)
    }
}

/// Which leaf a computation law is applied to.
#[derive(Clone, Copy)]
pub enum LeafArg<'a> {
    /// `atom b`.
    Atom(&'a Term),
    /// `snil`.
    Nil,
}

#[cfg(test)]
mod tests {
    use super::*;

    fn tau() -> Type {
        carved().unwrap().tau.clone()
    }

    fn svar(n: &str) -> Term {
        Term::free(n, tau())
    }

    /// The theory builds and the recursive-function constants are distinct.
    #[test]
    fn theory_builds() {
        let l = lisp().unwrap();
        // car/cdr are the recursion-position extractors (unavailable to Church).
        assert_eq!(l.car().type_of().unwrap(), Type::fun(tau(), tau()));
        assert_eq!(l.cdr().type_of().unwrap(), Type::fun(tau(), tau()));
        assert_eq!(
            l.append.type_of().unwrap(),
            Type::fun(tau(), Type::fun(tau(), tau()))
        );
        assert_eq!(l.len.type_of().unwrap(), Type::fun(tau(), Type::nat()));
    }

    /// `consp`/`atom?` computation laws — closed theorems with literal RHS.
    #[test]
    fn boolean_tests_compute() {
        let l = lisp().unwrap();
        let b = Term::free("b", bytes_ty());
        let (h, t) = (svar("h"), svar("t"));

        for (thm, want) in [
            (l.consp_atom(&b).unwrap(), false),
            (l.consp_nil().unwrap(), false),
            (l.consp_scons(&h, &t).unwrap(), true),
            (l.atom_atom(&b).unwrap(), true),
            (l.atom_nil().unwrap(), true),
            (l.atom_scons(&h, &t).unwrap(), false),
        ] {
            assert!(thm.hyps().is_empty());
            assert_eq!(thm.concl().as_eq().unwrap().1, &Term::bool_lit(want));
        }
    }

    /// `len` computation laws: `len (atom b) = 0`, `len snil = 0`,
    /// `len (scons h t) = succ (len t)`.
    #[test]
    fn len_computes() {
        let l = lisp().unwrap();
        let b = Term::free("b", bytes_ty());
        let (h, t) = (svar("h"), svar("t"));

        let la = l.len_leaf(LeafArg::Atom(&b)).unwrap();
        assert!(la.hyps().is_empty());
        assert_eq!(la.concl().as_eq().unwrap().1, &zero());

        let ln = l.len_leaf(LeafArg::Nil).unwrap();
        assert_eq!(ln.concl().as_eq().unwrap().1, &zero());

        let ls = l.len_scons(&h, &t).unwrap();
        assert!(ls.hyps().is_empty());
        let want = succ(l.len.clone().apply(t.clone()).unwrap());
        assert_eq!(ls.concl().as_eq().unwrap().1, &want);
    }

    /// `append` computation laws, including the paramorphic `scons` step
    /// `append (scons h t) w = scons h (append t w)`.
    #[test]
    fn append_computes() {
        let l = lisp().unwrap();
        let b = Term::free("b", bytes_ty());
        let (h, t, w) = (svar("h"), svar("t"), svar("w"));

        let aa = l.append_leaf(LeafArg::Atom(&b), &w).unwrap();
        assert!(aa.hyps().is_empty());
        assert_eq!(aa.concl().as_eq().unwrap().1, &w);

        let an = l.append_leaf(LeafArg::Nil, &w).unwrap();
        assert_eq!(an.concl().as_eq().unwrap().1, &w);

        let ac = l.append_scons(&h, &t, &w).unwrap();
        assert!(ac.hyps().is_empty());
        let want = l
            .cons()
            .clone()
            .apply(h.clone())
            .unwrap()
            .apply(
                l.append
                    .clone()
                    .apply(t.clone())
                    .unwrap()
                    .apply(w.clone())
                    .unwrap(),
            )
            .unwrap();
        assert_eq!(ac.concl().as_eq().unwrap().1, &want);
    }

    /// **The ACL2 archetype**: append associativity by structural induction.
    #[test]
    fn append_assoc_is_a_theorem() {
        let l = lisp().unwrap();
        let thm = l.append_assoc().unwrap(); // ⊢ ∀y z x. …
        assert!(thm.hyps().is_empty(), "append_assoc must be closed");
        let (x, y, z) = (svar("x0"), svar("y0"), svar("z0"));
        let inst = thm
            .all_elim(y.clone())
            .unwrap()
            .all_elim(z.clone())
            .unwrap()
            .all_elim(x.clone())
            .unwrap();
        let inst = crate::init::eq::beta_reduce(inst).unwrap();
        let ap = |a: &Term, b: &Term| {
            l.append
                .clone()
                .apply(a.clone())
                .unwrap()
                .apply(b.clone())
                .unwrap()
        };
        let lhs = ap(&ap(&x, &y), &z);
        let rhs = ap(&x, &ap(&y, &z));
        assert_eq!(inst.concl(), &lhs.equals(rhs).unwrap());
    }

    /// `len (append x y) = len x + len y` — the mixed catamorphism /
    /// paramorphism / `nat`-induction theorem.
    #[test]
    fn len_append_is_a_theorem() {
        let l = lisp().unwrap();
        let thm = l.len_append().unwrap(); // ⊢ ∀y x. …
        assert!(thm.hyps().is_empty(), "len_append must be closed");
        let (x, y) = (svar("x0"), svar("y0"));
        let inst = thm
            .all_elim(y.clone())
            .unwrap()
            .all_elim(x.clone())
            .unwrap();
        let inst = crate::init::eq::beta_reduce(inst).unwrap();
        let len_of = |t: &Term| l.len.clone().apply(t.clone()).unwrap();
        let ap = l
            .append
            .clone()
            .apply(x.clone())
            .unwrap()
            .apply(y.clone())
            .unwrap();
        let lhs = len_of(&ap);
        let rhs = add(len_of(&x), len_of(&y));
        assert_eq!(inst.concl(), &lhs.equals(rhs).unwrap());
    }
}
