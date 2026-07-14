//! **The K-framework frontend lowering** — turn the KORE rewrite rules a
//! [`covalence_k`] frontend extracts from a kompiled definition into internal
//! `Derivable_KStep` reduction theorems.
//!
//! The K analogue of [`crate::wasm`]. Where the WASM front end lowers SpecTec
//! *inductive judgements*, this lowers KORE *rewrite rules* — the single-step
//! transition relation `Step` — through the same impredicative rule-induction
//! engine ([`crate::metalogic`]). A concrete reduction step is a value
//! `⊢ Derivable_KStep ⌜Step(cfg, cfg')⌝`, pure syntactic data the kernel
//! re-checks; the untrusted [`covalence_k`] driver only ever *proposes* which
//! rule fires at which redex.
//!
//! - [`encode`] — KORE configuration [`covalence_k::ast::Pattern`] → the reified
//!   free term algebra over `Φ = nat` (mirrors [`crate::wasm::encode`]).
//! - [`reduce`] — [`covalence_k::fragment::RewriteRule`]s → a [`crate::metalogic::RuleSet`]
//!   of `Step` clauses; [`reduce::step`] mints one concrete step.
//!
//! Trust boundary: identical to Metamath/SpecTec. The KORE input is untrusted,
//! the kernel re-checks every construction, and a `Derivable_KStep` witness is
//! hypothesis-free syntactic data — bugs cost faithfulness/completeness, never
//! soundness. Fragment ladder + roadmap: `notes/design/k-frontend.md`. This is
//! **F0** (unconditional single steps); multi-step closure, conditional rules
//! (F1), and reachability claims (F2/F3) are recorded in `SKELETONS.md`.

pub mod encode;
pub mod reduce;
