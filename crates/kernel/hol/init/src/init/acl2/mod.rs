//! **The ACL2 soundness ladder** — deep-embedded ACL2 over a HOL model
//! of its object universe, per `notes/vibes/lisp/acl2-full-plan.md` and
//! the S0–S3 design `notes/vibes/lisp/acl2-s0-s3-design.md`.
//!
//! Everything here is *untrusted userspace* over existing kernel rules:
//! no new axioms, no TCB surface. Stages:
//!
//! - **S0** ([`carrier`]) — the object-universe carrier
//!   `A := aatom (coprod int bytes) | anil | acons A A`, a second instance
//!   of the payload-parametric carved construction
//!   ([`crate::init::inductive::carved`]), with induction, case analysis,
//!   constructor injectivity/distinctness, and the paramorphic recursor.
//! - **S1** ([`prims`]) — total model primitives
//!   (`consp`/`atom`/`endp`/`symbolp`/`integerp`/`equal`/`if`/arithmetic
//!   via the `intval : A → int` seam) with ACL2's completion axioms
//!   *proved* (car/cdr of non-conses = `nil`, non-numbers read as `0`)
//!   and the arithmetic axioms lifted from the proved
//!   [`crate::init::int`] ring (`plus_comm`/`plus_assoc`).
//! - **S2** ([`term`]) — metacircular pseudo-terms (terms *are* carrier
//!   values) with the pair-valued paramorphic evaluator `ev`
//!   (`eval`/`evlis`) and substituter (`subst`/`lsubst`), their
//!   per-constructor computation laws, and the semantic-substitution
//!   lemma `subst_sema` (S3's INST discharge).
//! - **S3** ([`ladder`]/[`derivable`]) — the reusable unary derivation
//!   layer (`derive_mixed` twin + β-bridge discharge helpers, promotion
//!   target `metalogic/`), the reified `Derivable_ACL2` (env-driven
//!   clause set: axioms, MP, INST, per-primitive congruence/computation)
//!   with its derivation constructors, and the **soundness half**: the
//!   rule-inducted metatheorem
//!   `⊢ ∀A. Derivable_ACL2 A ⟹ (∀σ. ¬(eval A σ = anil))` with one-step
//!   projection and `transport_equal` landing ground equations in base
//!   HOL (the plan's first transported theorem,
//!   `⊢ aplus (aint 2) (aint 2) = aint 4`).
//! - **S4** ([`defun`], design `notes/vibes/lisp/acl2-s4-s6-design.md`) —
//!   the definitional principle (conservative tier): user `defun`s admit
//!   into new env generations with genuinely *defined* model functions
//!   (plain `Thm::define`, or the S0 paramorphic recursor for the
//!   consp-guarded structural template), **proved** defining equations,
//!   per-env evaluator rebuild ([`term::Terms::build_with`]), the
//!   `Def(j)` clause + uniform soundness discharge, the per-axiom
//!   [`derivable::Discharge`] hook API, and [`defun::Acl2Session`]
//!   caching per-generation soundness (S4 gate:
//!   `⊢ app ⌜(1)⌝ ⌜(2)⌝ = ⌜(1 2)⌝` transported through the ladder).
//! - **S5** ([`ordinal`], design `notes/vibes/lisp/acl2-s5-design.md`)
//!   — ordinals below ε₀ over the model: `o-p`/`o<` as carrier functions
//!   (pair-valued paramorphisms dissolving the depth-2 `caar` descent),
//!   ACL2's ordinal defining equations *proved*, the `ord_fold` ground
//!   normaliser, the accessibility predicate with the `nat ↪ int`
//!   bridge (`init/int.rs`), and **THE well-foundedness theorem for all
//!   CNF notations** — `⊢ ∀x. ¬(o-p x = anil) ⟹ Acc x` — with
//!   `main_ord`/`graded_wf`/`wf_induct`. S5c wires the ordinals into the
//!   env: [`ordinal::with_ordinals`] installs the seven ordinal rows
//!   through the [`derivable::install_user_rows`] hand-row seam (each
//!   `def_eq_model` pinned against `model_image`) plus the S5 axiom pack
//!   (the classical `cases` split, `equal-mp`/`contra`/`truth`, and the
//!   `ModelImplies` typed-arithmetic rows), with
//!   [`derivable::transport_implies_open`] landing conditional model
//!   facts in base HOL. **S5d** adds the **IND-ORD clause family**
//!   (measured induction along `o<`, design §7): `Acl2Env::ind_ord`
//!   shapes + [`derivable::derive_ind_ord`], soundness discharged by
//!   well-founded induction through `wf_induct` (no carrier induction —
//!   the `subst_sema` valuation identification is the only delicate
//!   move). G4 gate ([`gate_s5d`], test-only): `ACL2-COUNT` admitted by
//!   the plain S4 template, its `NATP`/`O-P`/`O<`-decrease obligations
//!   derived in-object over the S5 pack, and app-assoc re-derived **by
//!   measure `(ACL2-COUNT X)`** — cross-checked against the S6
//!   structural route on the same env.
//! - **S6-structural** ([`derivable::s6_env`] + [`hilbert`], design
//!   §7–§13) — the **IND structural-induction clause** (tree induction
//!   over the formula-as-data + designated variable, soundness by
//!   carrier induction routed through S2's `subst_sema`), the
//!   `prop-k`/`prop-s` Hilbert axioms, the structural axiom pack
//!   (`car-cons`/`cdr-cons`/`consp-cons` as `ModelEq`/`ModelHolds`
//!   rows), the implication-form `CongImpl` clause family, the
//!   [`hilbert`] deduction compiler (K/S/MP), and open-`EQUAL` transport
//!   ([`derivable::transport_equal_open`]). S6 gate: `(defthm app-assoc …)`
//!   derived in the object logic and transported to the closed base-HOL
//!   `⊢ ∀x y z. app (app x y) z = app x (app y z)`.
//!
//! Open work is tracked in this directory's the generated open-work index.

pub mod carrier;
pub mod defun;
pub mod derivable;
pub mod fixers;
#[cfg(test)]
mod gate_s5d;
pub mod hilbert;
pub mod ladder;
pub mod ordinal;
pub mod prims;
pub mod simplify;
pub mod term;
pub mod wfrec;
