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
//! - **S3** (`ladder`/`derivable`, not yet built) — reified
//!   `Derivable_ACL2` + soundness + transport into base HOL.
//!
//! Open work is tracked in this directory's `SKELETONS.md`.

pub mod carrier;
pub mod prims;
pub mod term;
