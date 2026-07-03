//! The `ArticleMachine` trait — fat per-command interface for the OpenTheory
//! stack machine. Allows future implementations to override individual commands
//! (e.g., intercepting `thm` for theory import).

use covalence_hol::traits::HolLightKernel;

use crate::error::OtError;

/// Result of interpreting an article.
pub struct ArticleResult<K: HolLightKernel> {
    /// Assumptions (axioms) introduced.
    pub assumptions: Vec<K::Thm>,
    /// Theorems produced (exported via `thm` command).
    pub theorems: Vec<K::Thm>,
}

/// Fat per-command trait for the OpenTheory article stack machine.
///
/// Each method corresponds to one OpenTheory command. The default
/// implementation returns `UnknownCommand` for version 6+ commands.
pub trait ArticleMachine {
    type Kernel: HolLightKernel;

    // --- Literal pushes ---
    fn push_num(&mut self, n: i64) -> Result<(), OtError>;
    fn push_name(&mut self, s: &str) -> Result<(), OtError>;

    // --- Standard commands (version 5) ---
    fn cmd_abs_term(&mut self) -> Result<(), OtError>;
    fn cmd_abs_thm(&mut self) -> Result<(), OtError>;
    fn cmd_app_term(&mut self) -> Result<(), OtError>;
    fn cmd_app_thm(&mut self) -> Result<(), OtError>;
    fn cmd_assume(&mut self) -> Result<(), OtError>;
    fn cmd_axiom(&mut self) -> Result<(), OtError>;
    fn cmd_beta_conv(&mut self) -> Result<(), OtError>;
    fn cmd_cons(&mut self) -> Result<(), OtError>;
    fn cmd_const(&mut self) -> Result<(), OtError>;
    fn cmd_const_term(&mut self) -> Result<(), OtError>;
    fn cmd_deduct_antisym(&mut self) -> Result<(), OtError>;
    fn cmd_def(&mut self) -> Result<(), OtError>;
    fn cmd_define_const(&mut self) -> Result<(), OtError>;
    fn cmd_define_type_op(&mut self) -> Result<(), OtError>;
    fn cmd_eq_mp(&mut self) -> Result<(), OtError>;
    fn cmd_nil(&mut self) -> Result<(), OtError>;
    fn cmd_op_type(&mut self) -> Result<(), OtError>;
    fn cmd_pop(&mut self) -> Result<(), OtError>;
    fn cmd_ref(&mut self) -> Result<(), OtError>;
    fn cmd_refl(&mut self) -> Result<(), OtError>;
    fn cmd_remove(&mut self) -> Result<(), OtError>;
    fn cmd_subst(&mut self) -> Result<(), OtError>;
    fn cmd_thm(&mut self) -> Result<(), OtError>;
    fn cmd_trans(&mut self) -> Result<(), OtError>;
    fn cmd_type_op(&mut self) -> Result<(), OtError>;
    fn cmd_var(&mut self) -> Result<(), OtError>;
    fn cmd_var_term(&mut self) -> Result<(), OtError>;
    fn cmd_var_type(&mut self) -> Result<(), OtError>;
    fn cmd_version(&mut self) -> Result<(), OtError>;

    // --- Version 6+ commands ---
    fn cmd_define_const_list(&mut self) -> Result<(), OtError> {
        Err(OtError::UnknownCommand("defineConstList".into()))
    }
    fn cmd_hd_tl(&mut self) -> Result<(), OtError>;
    fn cmd_pragma(&mut self) -> Result<(), OtError>;
    fn cmd_prove_hyp(&mut self) -> Result<(), OtError>;
    fn cmd_sym(&mut self) -> Result<(), OtError>;

    /// Consume the machine and return the article result.
    fn finish(self) -> ArticleResult<Self::Kernel>;
}
