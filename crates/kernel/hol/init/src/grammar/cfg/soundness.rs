//! **CFG soundness** (M3 — stub).
//!
//! The discharge-free family least-fixpoint package: for a language family
//! `F : nat → set (list u8)` closed under the env's productions
//! (`ClosedFam_E F`), every derivable word is in its family —
//! `⊢ ∀F. ClosedFam_E F ⟹ ∀n w. Derives_E n w ⟹ mem w (F n)`. Built by
//! `rule_induction2`, grammar-size-independent. Not yet implemented; see
//! `grammar/cfg/SKELETONS.md` and `notes/vibes/logics/cfg-stratum-design.md`.
