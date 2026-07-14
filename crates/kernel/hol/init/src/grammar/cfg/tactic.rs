//! **The CFG parsing tactic** (M2 — stub).
//!
//! Two-phase, mirroring [`crate::grammar::regex::tactic`]: a pure-Rust memoised
//! recognizer over concrete bytes produces a derivation plan, then a builder
//! walks it once assembling the `⊢ Derives_E ⌜nt⌝ w` theorem with zero failed
//! kernel calls — terminal segments discharged by the regex tactic, non-terminal
//! segments recursed. Not yet implemented; see `grammar/cfg/SKELETONS.md`.
