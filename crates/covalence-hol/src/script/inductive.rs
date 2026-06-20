//! The `#inductive` directive — declaring a datatype and elaborating it,
//! through the generic recursion engine ([`crate::init::inductive`]), into
//! its type, constructors, recursor, and induction principle as **genuine
//! kernel theorems**.
//!
//! This is the surface-directive seam described in `docs/surface-syntax.md`:
//! a declaration names a type, its (optional) type parameters, and its
//! constructors with their argument types, and the elaborator drives the
//! engine to emit the structural artifacts. Nothing here is trusted — every
//! theorem the directive binds is re-derived by the kernel rules the engine
//! calls.
//!
//! ## Per-internal-logic dispatch (the design seam)
//!
//! `#inductive` is *declarative*: "this is the datatype." How a datatype is
//! realised is the **active logic's** business — in the metalogic (HOL) a
//! datatype is a strictly-positive inductive type carved out of a carrier,
//! with derived recursion/induction; in PA / SOA it would be a coded
//! relation; in MLTT an inductive family. So the directive elaborates
//! through a [`LogicInductive`] trait — the dispatch point — and *today*
//! only the [`HolMetalogic`] impl exists. Adding a logic is adding one impl,
//! not touching the parser or the [`Stmt`](super::Stmt) wiring.
//!
//! ## Status / scope of the prototype
//!
//! The engine's public entry points ([`Inductive`], [`recursor`]) consume an
//! [`InductiveSig`] plus the **freeness** (`injective` / `distinct`) and
//! **structural induction** facts an [`Inductive`] supplies, and a recursor
//! **selector predicate** from the `defs` catalogue. For a *fresh* user type
//! (a binary tree, a custom enum), those facts require carving the type out
//! of a carrier (`new_type_definition`) and *deriving* freeness + a recursor
//! spec — machinery the engine does not yet expose generically (see the
//! report / `SKELETONS.md`). So the prototype wires the **one metalogic type
//! the engine supports end to end — `nat`** — through the directive: the
//! `nat` shape `(#inductive nat (zero) (succ nat))` elaborates to the
//! kernel-primitive freeness/induction adapter and emits a genuine recursion
//! theorem `⊢ ∃rec. P_rec rec` plus a worked induction instance. The
//! directive *shape* and the *dispatch* generalise; the missing piece is the
//! fresh-carrier construction, isolated behind [`LogicInductive`].

use covalence_core::{Error, Term, Thm, Type, defs, subst};
use covalence_sexp::SExpr;

/// The kernel's `Result` (one type argument; error fixed to
/// `covalence_core::Error`). Aliased locally so the two-argument
/// `std::result::Result` stays available for the `ScriptError`-returning
/// parser / elaborator.
type KResult<T> = covalence_core::Result<T>;

use crate::init::ext::TermExt;
use crate::init::inductive::{Arg, Constructor, Inductive, InductiveSig, recursor};

use super::env::ConstDef;
use super::{ScriptError, syntax};

// ============================================================================
// The parsed declaration
// ============================================================================

/// One constructor of a `#inductive` declaration: its name and the
/// declared argument *types* (as raw S-expressions, lowered to [`Type`] by
/// the elaborator once the inductive type's own name is known).
#[derive(Clone, Debug)]
pub struct CtorDecl {
    pub name: String,
    /// The argument type S-expressions, in declaration order. A recursive
    /// occurrence is the bare type name (`nat` in `(succ nat)`).
    pub args: Vec<SExpr>,
}

/// A parsed `#inductive` declaration — the directive's payload, before any
/// logic-specific elaboration.
#[derive(Clone, Debug)]
pub struct Decl {
    /// The inductive type's name.
    pub name: String,
    /// The type parameters (`'a`, …), in order. Empty for a ground type
    /// like `nat`.
    pub params: Vec<String>,
    /// The constructors, in declaration order.
    pub ctors: Vec<CtorDecl>,
}

/// Parse `(#inductive NAME [(#params 'a …)] (ctor ARGTY…) …)`.
///
/// `NAME` may itself be a list `(NAME 'a …)` carrying the type parameters
/// inline (the lighter form); the explicit `(#params …)` head is also
/// accepted. Each remaining list is a constructor `(cname ARGTY…)`.
pub fn parse_decl(ch: &[SExpr]) -> Result<Decl, ScriptError> {
    if ch.len() < 2 {
        return Err(ScriptError::Syntax(
            "#inductive: expected (#inductive NAME (ctor …) …)".into(),
        ));
    }
    // The head may be a bare name, or `(NAME 'a …)` binding params inline.
    let (name, mut params) = match &ch[1] {
        SExpr::Atom(_) => (syntax::sym(&ch[1], "inductive name")?.to_string(), Vec::new()),
        SExpr::List(inner) => {
            let n = syntax::sym(&inner[0], "inductive name")?.to_string();
            let ps = inner[1..]
                .iter()
                .map(|p| Ok(syntax::sym(p, "type parameter")?.to_string()))
                .collect::<Result<Vec<_>, ScriptError>>()?;
            (n, ps)
        }
    };

    let mut ctors = Vec::new();
    for item in &ch[2..] {
        let cch = syntax::list(item, "constructor")?;
        // Optional explicit `(#params 'a …)` clause.
        if syntax::head_sym(cch).ok() == Some("#params") {
            params = cch[1..]
                .iter()
                .map(|p| Ok(syntax::sym(p, "type parameter")?.to_string()))
                .collect::<Result<Vec<_>, ScriptError>>()?;
            continue;
        }
        let cname = syntax::sym(&cch[0], "constructor name")?.to_string();
        ctors.push(CtorDecl {
            name: cname,
            args: cch[1..].to_vec(),
        });
    }
    if ctors.is_empty() {
        return Err(ScriptError::Syntax(
            "#inductive: a datatype needs at least one constructor".into(),
        ));
    }
    Ok(Decl {
        name,
        params,
        ctors,
    })
}

// ============================================================================
// The elaboration result
// ============================================================================

/// What a [`LogicInductive`] elaboration produces: the constructor terms to
/// bind as catalogue constants, plus the genuine theorems (recursor /
/// induction) to bind as lemmas. Names are *unqualified*; the directive
/// binds them under the `NAME.` prefix.
pub struct Elaborated {
    /// `(local-name, constructor term)` — bound as `NAME.local-name`.
    pub ctors: Vec<(String, ConstDef)>,
    /// `(local-name, theorem)` — bound as `NAME.local-name` lemmas.
    pub thms: Vec<(String, Thm)>,
}

// ============================================================================
// The dispatch seam
// ============================================================================

/// The per-internal-logic realisation of a `#inductive` declaration — the
/// dispatch point of the directive. The metalogic ([`HolMetalogic`]) is the
/// only implementation today; PA / SOA / MLTT realisations slot in here
/// (see the [module docs](self)).
pub trait LogicInductive {
    /// Elaborate `decl` into its constructors + genuine structural theorems,
    /// or report why this logic cannot realise it.
    fn elaborate(&self, decl: &Decl) -> Result<Elaborated, ScriptError>;
}

// ============================================================================
// The HOL metalogic
// ============================================================================

/// The metalogic (HOL) realisation. A `#inductive` type is a
/// strictly-positive inductive type; recursion/induction are derived through
/// the generic engine ([`crate::init::inductive`]).
///
/// The prototype realises the **kernel-primitive** `nat` shape end to end;
/// fresh user types are reported as unsupported (the carrier-construction
/// gap — see the [module docs](self)).
pub struct HolMetalogic;

impl LogicInductive for HolMetalogic {
    fn elaborate(&self, decl: &Decl) -> Result<Elaborated, ScriptError> {
        // Recognise the `nat` shape: ground type, constructors `(c0)` and
        // `(c1 <name>)` where the single argument is the type itself.
        if is_nat_shape(decl) {
            return elaborate_nat(decl).map_err(ScriptError::Kernel);
        }
        Err(ScriptError::Syntax(format!(
            "#inductive: the HOL metalogic prototype realises only the `nat` \
             shape (a nullary + a single-recursive-argument constructor over a \
             ground type); `{}` needs the fresh-carrier construction the engine \
             does not yet expose (see script/inductive.rs)",
            decl.name
        )))
    }
}

/// Whether `decl` matches the `nat` constructor shape: no type parameters,
/// exactly two constructors — a nullary one and a unary one whose argument
/// is a direct recursive occurrence (the bare type name).
fn is_nat_shape(decl: &Decl) -> bool {
    decl.params.is_empty()
        && decl.ctors.len() == 2
        && decl.ctors[0].args.is_empty()
        && decl.ctors[1].args.len() == 1
        && decl.ctors[1].args[0].as_symbol() == Some(decl.name.as_str())
}

// ----------------------------------------------------------------------------
// `nat`'s `Inductive` adapter — freeness + induction from kernel primitives.
//
// This mirrors `init::recursion::NatTheory` (which is private to that
// module): the recursion engine talks only to this trait, sourcing
// structural induction from `Thm::nat_induct` and freeness from
// `Thm::succ_inj` / `Thm::zero_ne_succ`. Re-deriving it here (rather than
// reaching into the engine's `nat` consumer) keeps the directive a pure
// *consumer* of the engine's public API.
// ----------------------------------------------------------------------------

fn zero() -> Term {
    Term::nat_lit(0u8)
}

fn succ(n: Term) -> KResult<Term> {
    Term::succ().apply(n)
}

/// The `nat` signature for the engine: `zero` (nullary), `succ` (one
/// recursive argument `m`, image `b`).
fn nat_sig() -> &'static InductiveSig {
    static SIG: std::sync::LazyLock<InductiveSig> = std::sync::LazyLock::new(|| InductiveSig {
        ty: Type::nat(),
        relation: "G",
        ctors: vec![
            Constructor::nullary(zero()),
            Constructor::new(
                Term::succ(),
                vec![Arg::Rec {
                    name: "m",
                    image: "b",
                }],
            ),
        ],
    });
    &SIG
}

struct NatTheory;

impl Inductive for NatTheory {
    fn sig(&self) -> &InductiveSig {
        nat_sig()
    }

    fn induct(&self, _motive: &Term, cases: Vec<Thm>) -> KResult<Thm> {
        let [base, step]: [Thm; 2] = cases
            .try_into()
            .map_err(|_| Error::ConnectiveRule("nat induct: expected 2 cases".into()))?;
        Thm::nat_induct(base, step)
    }

    fn injective(&self, i: usize, xs: &[Term], ys: &[Term]) -> KResult<Thm> {
        match (i, xs, ys) {
            (1, [x], [y]) => Thm::succ_inj(x.clone(), y.clone()),
            _ => Err(Error::ConnectiveRule(format!(
                "nat injective: no injectivity for constructor {i}"
            ))),
        }
    }

    fn distinct(&self, i: usize, j: usize, xs: &[Term], ys: &[Term]) -> KResult<Thm> {
        match (i, j, xs, ys) {
            (0, 1, [], [m]) => {
                let eq = zero().equals(succ(m.clone())?)?;
                Thm::zero_ne_succ(m.clone())?
                    .not_elim(Thm::assume(eq.clone())?)?
                    .imp_intro(&eq)
            }
            (1, 0, [m], []) => {
                let eq = succ(m.clone())?.equals(zero())?;
                Thm::zero_ne_succ(m.clone())?
                    .not_elim(Thm::assume(eq.clone())?.sym()?)?
                    .imp_intro(&eq)
            }
            _ => Err(Error::ConnectiveRule(format!(
                "nat distinct: no rule for constructors {i}, {j}"
            ))),
        }
    }
}

/// `natRec`'s recursor selector predicate `P_rec`, instantiated at the
/// result type `α := nat` — the predicate the engine's
/// [`recursor::recursion_theorem`] ∃-introduces over. Sourced from the
/// `defs` catalogue (the directive does not re-synthesise it for `nat`,
/// since `nat` *is* in the catalogue).
fn nat_p_rec_pred() -> KResult<Term> {
    let poly = defs::nat_rec_spec()
        .tm()
        .expect("natRec carries a selector predicate")
        .clone();
    Ok(subst::subst_tfree_in_term(&poly, "a", &Type::nat()))
}

/// Elaborate the `nat` shape: bind the two constructors, prove the recursion
/// theorem `⊢ ∃rec. P_rec rec` through the engine, and prove one concrete
/// induction instance (`⊢ ∀n. n = n`) to witness that the induction
/// principle the engine consumes is a live kernel theorem.
fn elaborate_nat(decl: &Decl) -> KResult<Elaborated> {
    let nat = Type::nat();

    // Constructors, bound under the user's chosen names.
    let c0 = decl.ctors[0].name.clone();
    let c1 = decl.ctors[1].name.clone();
    let ctors = vec![
        (c0, ConstDef::Op(zero())),
        (c1, ConstDef::Op(Term::succ())),
    ];

    // The recursion theorem, straight from the engine.
    let z = Term::free("z", nat.clone());
    let f = Term::free("f", Type::fun(nat.clone(), Type::fun(nat.clone(), nat.clone())));
    let rec_thm = recursor::recursion_theorem(&NatTheory, &[z, f], &nat, &nat_p_rec_pred()?)?;

    // A worked induction instance: `⊢ ∀n. n = n`, proved by the engine's
    // induction seam (the same `Inductive::induct` the recursion theorem
    // rides on). Base and step are `refl`, lifted into the **applied-motive**
    // form `nat_induct` requires (`p 0`, `p n ⟹ p (S n)` with `p` un-reduced)
    // by β-expansion — the same bookkeeping the `induct` tactic does.
    let induct_demo = {
        // motive `p` = λn. n = n; body (locally nameless, var #0 = n).
        let body = {
            let n = Term::free("__n", nat.clone());
            subst::close(&n.clone().equals(n)?, "__n")
        };
        let p = Term::abs(nat.clone(), body.clone());

        // base: ⊢ (λn. n = n) 0, from ⊢ 0 = 0.
        let base_body = Thm::refl(zero())?; // ⊢ 0 = 0
        let base = Thm::beta_conv(Term::app(p.clone(), zero()))?
            .sym()?
            .eq_mp(base_body)?;

        // step: ⊢ (λn. n = n) n ⟹ (λn. n = n) (S n), from ⊢ S n = S n.
        let v = Term::free("n", nat.clone());
        let ih = subst::open(&body, &v); // n = n
        let sv = succ(v.clone())?;
        let step_body = Thm::refl(sv.clone())?.imp_intro(&ih)?; // ⊢ (n = n) ⟹ (S n = S n)
        let ea = Thm::beta_conv(Term::app(p.clone(), v))?;
        let eb = Thm::beta_conv(Term::app(p.clone(), sv))?;
        let step = Thm::refl(defs::imp())?
            .mk_comb(ea.sym()?)?
            .mk_comb(eb.sym()?)?
            .eq_mp(step_body)?;

        // ⊢ ∀n. (λn. n = n) n, then β-normalise the body to ⊢ ∀n. n = n.
        let ind = NatTheory.induct(&p, vec![base, step])?;
        let nf = crate::proofs::rewrite::beta_nf(ind.concl().clone());
        nf.eq_mp(ind)?
    };

    Ok(Elaborated {
        ctors,
        thms: vec![("rec".into(), rec_thm), ("induct".into(), induct_demo)],
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::script::{Env, run, run_str};

    /// Parse the `nat` declaration in both the bare and the `(NAME)` head
    /// forms; the constructor shapes are recognised either way.
    #[test]
    fn parses_the_nat_declaration() {
        let exprs = covalence_sexp::parse("(#inductive nat (zero) (succ nat))").unwrap();
        let ch = syntax::list(&exprs[0], "#inductive").unwrap();
        let decl = parse_decl(ch).unwrap();
        assert_eq!(decl.name, "nat");
        assert!(decl.params.is_empty());
        assert_eq!(decl.ctors.len(), 2);
        assert_eq!(decl.ctors[0].name, "zero");
        assert_eq!(decl.ctors[1].name, "succ");
        assert!(is_nat_shape(&decl));
    }

    /// The elaboration produces **genuine, hypothesis-free** theorems: the
    /// recursion theorem `⊢ ∃rec. P_rec rec` and the induction instance
    /// `⊢ ∀n. (λn. n = n) n`.
    #[test]
    fn elaboration_emits_real_theorems() {
        let exprs = covalence_sexp::parse("(#inductive nat (zero) (succ nat))").unwrap();
        let ch = syntax::list(&exprs[0], "#inductive").unwrap();
        let decl = parse_decl(ch).unwrap();
        let elab = HolMetalogic.elaborate(&decl).unwrap();

        // Both constructors are bound.
        let names: Vec<&str> = elab.ctors.iter().map(|(n, _)| n.as_str()).collect();
        assert_eq!(names, vec!["zero", "succ"]);

        // The recursion theorem is axiom-free and boolean.
        let rec = &elab.thms.iter().find(|(n, _)| n == "rec").unwrap().1;
        assert!(rec.hyps().is_empty(), "∃rec. P_rec rec must be axiom-free");
        assert!(rec.concl().type_of().unwrap().is_bool());

        // The induction instance is axiom-free and proves exactly
        // `⊢ ∀n. n = n` (β-normalised body), i.e. the engine's induction
        // really discharged a `∀`-goal — not a triviality.
        let ind = &elab.thms.iter().find(|(n, _)| n == "induct").unwrap().1;
        assert!(ind.hyps().is_empty(), "the induction instance is closed");
        let n = Term::free("__n", Type::nat());
        let expected = subst::close(&n.clone().equals(n).unwrap(), "__n");
        let expected = Term::app(defs::forall(Type::nat()), Term::abs(Type::nat(), expected));
        assert_eq!(ind.concl(), &expected, "induct proves ∀n. n = n");
    }

    /// The full directive path: a `#inductive` directive binds its emitted
    /// theorems as lemmas, and they appear in the resulting theory's `thms`.
    #[test]
    fn directive_binds_recursor_and_induction() {
        let thms = run_str(
            "(#import core)(#open core)\n(#inductive nat (zero) (succ nat))",
        )
        .expect("the #inductive directive replays");
        assert!(
            thms.iter().any(|nt| nt.name == "nat.rec"),
            "recursion theorem bound as nat.rec"
        );
        assert!(
            thms.iter().any(|nt| nt.name == "nat.induct"),
            "induction instance bound as nat.induct"
        );
        for nt in &thms {
            assert!(nt.thm.hyps().is_empty(), "{} must be axiom-free", nt.name);
        }
    }

    /// A downstream `#thm`, run *after* the directive, uses a directive-bound
    /// **constructor constant** (`nat.succ`) in its goal — proving the
    /// constructors are wired into the environment for later proofs.
    #[test]
    fn downstream_proof_uses_an_emitted_constructor() {
        let theory = run(
            "(#import core)(#open core)\n\
             (#inductive nat (zero) (succ nat))\n\
             (#thm one (#concl (= (nat.succ 0) 1)) (#proof (reduce-prim (nat.succ 0))))",
            |name| (name == "core").then(Env::core),
            |_| None,
        )
        .expect("downstream proof resolves the nat.succ constructor");
        let one = theory
            .thms
            .iter()
            .find(|nt| nt.name == "one")
            .expect("downstream theorem present");
        assert!(one.thm.hyps().is_empty());
    }

    /// A fresh user type the prototype cannot yet realise reports the
    /// carrier-construction gap rather than fabricating a theorem.
    #[test]
    fn fresh_type_reports_the_gap() {
        // A binary tree: `(#inductive tree (leaf) (node tree tree))` — two
        // recursive arguments, not the `nat` shape.
        let exprs = covalence_sexp::parse("(#inductive tree (leaf) (node tree tree))").unwrap();
        let ch = syntax::list(&exprs[0], "#inductive").unwrap();
        let decl = parse_decl(ch).unwrap();
        assert!(!is_nat_shape(&decl));
        match HolMetalogic.elaborate(&decl) {
            Err(ScriptError::Syntax(_)) => {}
            Ok(_) => panic!("a fresh type must NOT fabricate an elaboration"),
            Err(other) => panic!("unexpected error kind: {other:?}"),
        }
    }
}
