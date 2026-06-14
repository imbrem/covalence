//! Conservative-extension primitives: `Thm::define` (fresh defined
//! constants) and `Thm::new_type_definition` (fresh subtypes), plus
//! the [`TypeDef`] result bundle and the private fresh-identity
//! markers. Split out of `thm/mod.rs` so the two extension primitives
//! are auditable as one unit; they still mint `Thm`s only through the
//! module-private `Thm::build`, which (as a descendant module of
//! `thm`) this file may call.

use std::fmt;
use std::sync::Arc;

use smol_str::SmolStr;

use crate::error::{Error, Result};
use crate::hol;
use crate::ctx::Ctx;
use crate::term::{Def, Term, TermKind, Type, TypeKind};

use super::Thm;

impl Thm {
    pub fn new_type_definition(
        hint: impl Into<SmolStr>,
        abs_hint: impl Into<SmolStr>,
        rep_hint: impl Into<SmolStr>,
        witness: Thm,
    ) -> Result<TypeDef> {
        // 1. Decompose witness's concl as `P x` (an application).
        let TermKind::App(p, x) = witness.concl.kind() else {
            return Err(Error::BadTypeDefWitness(format!("{}", witness.concl)));
        };
        let p = p.clone();
        let x = x.clone();

        // 2. Read α from x's type.
        let alpha = x.type_of()?;

        // 3. Validate P : α → bool.
        let p_ty = p.type_of()?;
        let TypeKind::Fun(p_dom, p_cod) = p_ty.kind() else {
            return Err(Error::NotFunction(p_ty));
        };
        if *p_dom != alpha {
            return Err(Error::TypeMismatch {
                expected: alpha.clone(),
                got: p_dom.clone(),
            });
        }
        if !p_cod.is_bool() {
            return Err(Error::NotBool(p_cod.clone()));
        }

        // 4. Compute the type-variable arity from α's free TFrees.
        //    τ becomes parametric in those tvars (in canonical order),
        //    so `inst_tfree` after typedef substitutes inside τ's args.
        let tvar_names = alpha.free_tvars();
        let tvar_types: Vec<Type> = tvar_names.iter().map(|n| Type::tfree(n.clone())).collect();

        // 5. Allocate ONE fresh marker tying the typedef + abs + rep
        //    together via Arc identity. The marker is a kernel-private
        //    zero-sized struct with no methods, so user code can never
        //    forge or equate it across calls.
        let marker = TypeDefMarker::new();
        let _ = hint;
        let tau = Type::tycon_obs(marker.clone(), tvar_types);

        // 6. Build abs and rep as Obs leaves wrapping per-role markers
        //    that carry a reference to the shared typedef marker. This
        //    gives abs and rep their own Arc identities while keeping
        //    them tied to the typedef.
        let abs_marker = TypeDefAbsMarker::new(&marker, abs_hint.into());
        let rep_marker = TypeDefRepMarker::new(&marker, rep_hint.into());
        let abs_ty = Type::fun(alpha.clone(), tau.clone());
        let rep_ty = Type::fun(tau.clone(), alpha.clone());
        let abs = Term::obs(abs_marker, abs_ty);
        let rep = Term::obs(rep_marker, rep_ty);

        // 7. Build the three bijection theorems at HOL `=` / `⟹` /
        //    `∀` — all conclusions are `bool`-typed.
        //
        //    abs_rep: ⊢ ∀a:τ. abs (rep a) = a
        let a_free = Term::free("a", tau.clone());
        let abs_rep_body = hol::hol_eq(
            Term::app(abs.clone(), Term::app(rep.clone(), a_free.clone())),
            a_free,
        );
        let abs_rep_concl = hol::hol_forall("a", tau.clone(), abs_rep_body);

        //    rep_abs_eq : `rep (abs r) = r`
        //    p_at_r     : `P r`
        let r_free = Term::free("r", alpha.clone());
        let p_at_r = Term::app(p, r_free.clone());
        let rep_abs_eq = hol::hol_eq(
            Term::app(rep.clone(), Term::app(abs.clone(), r_free.clone())),
            r_free,
        );
        //    fwd: ⊢ ∀r:α. P r ⟹ rep (abs r) = r
        let fwd_concl = hol::hol_forall(
            "r",
            alpha.clone(),
            hol::hol_imp(p_at_r.clone(), rep_abs_eq.clone()),
        );
        //    back: ⊢ ∀r:α. rep (abs r) = r ⟹ P r
        let back_concl = hol::hol_forall(
            "r",
            alpha,
            hol::hol_imp(rep_abs_eq, p_at_r),
        );

        // 8. Propagate witness's hyps to each emitted theorem — every
        //    fact about the new typedef depends on the witness's
        //    inhabitedness justification. `TermSet` clones share the
        //    underlying set via `Arc`.
        let hyps = witness.hyps.clone();
        let abs_rep = Self::build(hyps.clone(), abs_rep_concl)?;
        let rep_abs_fwd = Self::build(hyps.clone(), fwd_concl)?;
        let rep_abs_back = Self::build(hyps, back_concl)?;

        Ok(TypeDef {
            tau,
            abs,
            rep,
            abs_rep,
            rep_abs_fwd,
            rep_abs_back,
            tvars: tvar_names,
        })
    }

    /// Introduce a fresh defined constant: emit `⊢ Def(name, body) ≡ body`.
    ///
    /// Each call allocates a *fresh* `Arc` for the body, so two
    /// distinct `define` calls — even with the same name and the same
    /// body term — produce distinct `Def`s. The kernel never reuses a
    /// `Def` identity, so users cannot accidentally derive
    /// `⊢ body₁ ≡ body₂` by `trans`+`sym`-ing two equations for "the
    /// same name" — the two `Def`s are simply different symbols that
    /// happen to share a display label.
    ///
    /// The `name` is a display-only label (a `SmolStr`). The
    /// `body` must be a valid Core term (typeable in isolation).
    ///
    /// ## Soundness
    ///
    /// Sound because the resulting `Def` is a brand-new symbol whose
    /// only equation says it equals `body`. In any model satisfying
    /// the prior theory, we extend by interpreting this `Def` as
    /// `⟦body⟧` — a conservative extension. No global signature is
    /// needed because the allocator gives us uniqueness per call.
    pub fn define(name: impl Into<SmolStr>, body: Term) -> Result<Thm> {
        let body_type = body.type_of()?;
        // Soundness check (Isabelle/Pure parity): no "phantom"
        // tvars — every free tvar appearing inside any type
        // annotation in `body` must also appear in `body_type`.
        // Without this, a phantom tvar inside `body` would be
        // invisible to `instance_type`, so `subst_tfree_in_term`
        // could leave a `Def` whose body still mentions the
        // phantom tvar at the original type — inconsistent with
        // the `Def ≡ body` equation it stands for.
        let type_tvars: std::collections::BTreeSet<smol_str::SmolStr> =
            body_type.free_tvars().into_iter().collect();
        let mut body_tvars = std::collections::BTreeSet::new();
        crate::subst::collect_term_tvars(&body, &mut body_tvars);
        for tv in &body_tvars {
            if !type_tvars.contains(tv) {
                return Err(crate::error::Error::DefPhantomTFree {
                    tvar: tv.clone(),
                    body_type,
                });
            }
        }
        let d = Def::new_internal(name.into(), body.clone(), body_type);
        let concl = hol::hol_eq(Term::def(d), body);
        Self::build(Ctx::new(), concl)
    }
}

// ============================================================================
// new_type_definition — result bundle and private markers
// ============================================================================

/// Result of [`Thm::new_type_definition`]: the fresh subtype τ along
/// with its abs/rep bijection constants and the three theorems that
/// witness the bijection. All three theorems carry the witness's
/// hypotheses.
#[derive(Clone, Debug)]
pub struct TypeDef {
    /// The freshly-introduced type. `TyConObs` carrying a marker Arc
    /// shared by `abs` and `rep`. Parametric in `tvars` (in canonical
    /// order, so `inst_tfree` propagates correctly).
    pub tau: Type,
    /// The fresh `abs : α → τ` constant. An `Obs` leaf whose marker
    /// references the typedef.
    pub abs: Term,
    /// The fresh `rep : τ → α` constant.
    pub rep: Term,
    /// `⊢ ⋀a:τ. abs (rep a) ≡ a`.
    pub abs_rep: Thm,
    /// `⊢ ⋀r:α. P r ⟹ rep (abs r) ≡ r`.
    pub rep_abs_fwd: Thm,
    /// `⊢ ⋀r:α. rep (abs r) ≡ r ⟹ P r`.
    pub rep_abs_back: Thm,
    /// Sorted list of type-variable names that appear in α. τ is
    /// parametric in exactly these tvars (positionally, in this order).
    pub tvars: Vec<smol_str::SmolStr>,
}

/// Private marker carried inside a `TypeDef`'s `Type::tycon_obs` and
/// (via the abs/rep markers below) inside its abs/rep `Term::obs`
/// leaves. Zero-sized, no methods — its sole purpose is to provide
/// fresh `Arc` identity per `new_type_definition` call. Cannot be
/// constructed outside this module.
#[derive(Debug, Clone)]
struct TypeDefMarker(Arc<TypeDefMarkerInner>);

#[derive(Debug)]
struct TypeDefMarkerInner;

impl TypeDefMarker {
    fn new() -> Self {
        TypeDefMarker(Arc::new(TypeDefMarkerInner))
    }
}

/// Marker carried by a typedef's `abs` constant. Holds an Arc to the
/// shared typedef marker so it's uniquely tied to the typedef, plus
/// a display hint for pretty-printing.
struct TypeDefAbsMarker {
    #[allow(dead_code)]
    typedef: Arc<TypeDefMarkerInner>,
    hint: SmolStr,
}

impl TypeDefAbsMarker {
    fn new(m: &TypeDefMarker, hint: SmolStr) -> Self {
        TypeDefAbsMarker {
            typedef: Arc::clone(&m.0),
            hint,
        }
    }
}

impl fmt::Debug for TypeDefAbsMarker {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.hint.is_empty() {
            write!(f, "abs")
        } else {
            write!(f, "{}", self.hint)
        }
    }
}

/// Marker for the typedef's `rep` constant.
struct TypeDefRepMarker {
    #[allow(dead_code)]
    typedef: Arc<TypeDefMarkerInner>,
    hint: SmolStr,
}

impl TypeDefRepMarker {
    fn new(m: &TypeDefMarker, hint: SmolStr) -> Self {
        TypeDefRepMarker {
            typedef: Arc::clone(&m.0),
            hint,
        }
    }
}

impl fmt::Debug for TypeDefRepMarker {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.hint.is_empty() {
            write!(f, "rep")
        } else {
            write!(f, "{}", self.hint)
        }
    }
}
