/// Kernel error messages
pub mod kernel_error {
    /// Not implemented
    pub const NOT_IMPLEMENTED: &'static str = "covalence: not implemented";
    /// Strategy did not return a valid subcontext
    pub const ASSUME_NOT_SUBCTX: &'static str = "assume: not a subcontext of parent";
    /// Strategy changed assumptions in ensure_assumptions_valid_under
    pub const ENSURE_ASSUMPTIONS_VALID_UNDER_CHANGED: &'static str =
        "ensure_assumptions_valid_under: assumptions changed";
    /// An assumption must be a valid type
    pub const ASSUME_IS_TY: &'static str = "assume: ty is not a valid type";
    /// To add a variable, its type must be inhabited
    pub const ADD_VAR_IS_INHAB: &'static str = "add_var: ty is not inhabited";
    /// When we add a variable, it should be _well-scoped_: only contain variables from the current
    /// context
    ///
    /// Later, this restriction may be lifted slightly to allow _semi-well-scoped_ terms.
    pub const DERIVE_FV_ILL_SCOPED: &'static str = "derive_fv: var is ill-scoped";
    pub const DERIVE_CLOSE_HAS_TY_UNDER_ILL_SCOPED: &'static str =
        "derive_close_has_ty_under: variable's context is not a subcontext of the current context";
    pub const DERIVE_CLOSE_HAS_TY_UNDER_TOO_MANY_VARS: &'static str =
        "derive_close_has_ty_under: variable's context must define exactly one variable";
    pub const DERIVE_CLOSE_HAS_TY_UNDER_INVALID_ASSUMPTION: &'static str =
        "derive_close_has_ty_under: assumption is not valid";
    pub const DERIVE_CLOSE_HAS_TY_UNDER_HAS_TY: &'static str = "derive_close_has_ty_under: tm";
    pub const DERIVE_EQN_LHS: &'static str = "derive_eqn: lhs";
    pub const DERIVE_EQN_RHS: &'static str = "derive_eqn: rhs";
    pub const DERIVE_PI_IMAX_LE: &'static str =
        "derive_pi: cannot deduce that imax(arg_lvl, res_lvl) ≤ lvl";
    pub const DERIVE_PI_ARG_TY: &'static str = "derive_pi: arg_ty";
    pub const DERIVE_PI_RES_TY: &'static str = "derive_pi: res_ty";
    pub const DERIVE_SIGMA_ARG_LVL_LE: &'static str =
        "derive_sigma: cannot deduce that arg_lvl ≤ lvl";
    pub const DERIVE_SIGMA_RES_LVL_LE: &'static str =
        "derive_sigma: cannot deduce that res_lvl ≤ lvl";
    pub const DERIVE_SIGMA_ARG_TY: &'static str = "derive_sigma: arg_ty";
    pub const DERIVE_SIGMA_RES_TY: &'static str = "derive_sigma: res_ty";
    pub const DERIVE_ABS_BODY: &'static str = "derive_abs: body";
    pub const DERIVE_APP_ARG: &'static str = "derive_app: arg";
    pub const DERIVE_APP_FUNC: &'static str = "derive_app: func";
    pub const DERIVE_PAIR_RES_TY: &'static str = "derive_pair: res_ty";
    pub const DERIVE_PAIR_FST: &'static str = "derive_pair: fst";
    pub const DERIVE_PAIR_SND: &'static str = "derive_pair: snd";
    pub const DERIVE_FST_PAIR: &'static str = "derive_fst: pair";
    pub const DERIVE_SND_PAIR: &'static str = "derive_snd: pair";
    pub const DERIVE_DITE_COND: &'static str = "derive_dite: cond";
    pub const DERIVE_DITE_THEN_BR: &'static str = "derive_dite: then_br";
    pub const DERIVE_DITE_ELSE_BR: &'static str = "derive_dite: else_br";
    pub const DERIVE_TRUNC_TY: &'static str = "derive_trunc: ty";
    pub const DERIVE_CHOOSE_TY: &'static str = "derive_choose: ty";
    pub const DERIVE_CHOOSE_PRED: &'static str = "derive_choose: pred";
    pub const DERIVE_NATS_SET_LE_LVL: &'static str = "derive_nats: cannot deduce that SET ≤ lvl";
    pub const DERIVE_SUCC_N: &'static str = "derive_succ: n";
    pub const DERIVE_NATREC_MOT: &'static str = "derive_natrec: mot";
    pub const DERIVE_NATREC_Z: &'static str = "derive_natrec: z";
    pub const DERIVE_NATREC_S: &'static str = "derive_natrec: s";
    pub const DERIVE_LET_BOUND: &'static str = "derive_let: bound";
    pub const DERIVE_LET_BODY: &'static str = "derive_let: body";
    pub const DERIVE_BETA_ABS_TM_EQ_ABS: &'static str = "derive_beta_abs: tm ≡ abs A b";
    pub const DERIVE_BETA_ABS_TM_WF: &'static str = "derive_beta_abs: tm wf";
    pub const DERIVE_BETA_ABS_ARG: &'static str = "derive_beta_abs: arg";
    pub const DERIVE_BETA_ZERO_TM_EQ_NATREC: &'static str = "derive_beta_zero: tm ≡ natrec C z s";
    pub const DERIVE_BETA_ZERO_TM_WF: &'static str = "derive_beta_zero: tm wf";
    pub const DERIVE_BETA_SUCC_TM_EQ_NATREC: &'static str = "derive_beta_zero: tm ≡ natrec C z s";
    pub const DERIVE_BETA_SUCC_TM_WF: &'static str = "derive_beta_zero: tm wf";
    pub const DERIVE_BETA_SUCC_N: &'static str = "derive_beta_succ: n";
    pub const DERIVE_CHOOSE_SPEC_EXISTS: &'static str = "derive_choose_spec: exists";
    pub const DERIVE_UNIT_EXT_A: &'static str = "derive_unit_ext: a";
    pub const DERIVE_PROP_EXT_TT_PROP: &'static str = "derive_prop_ext_tt: a prop";
    pub const DERIVE_PROP_EXT_TT_INHAB: &'static str = "derive_prop_ext_tt: a inhab";
    pub const DERIVE_PROP_EXT_FF_PROP: &'static str = "derive_prop_ext_ff: a prop";
    pub const DERIVE_PROP_EXT_FF_EMPTY: &'static str = "derive_prop_ext_ff: a empty";
    pub const DERIVE_EXT_EQN_INHAB: &'static str = "derive_ext: eqn inhab";
    pub const DERIVE_PI_ETA_TY_EQ_PI: &'static str = "derive_pi_eta: ty ≡ pi A B";
    pub const DERIVE_PI_ETA_F: &'static str = "derive_pi_eta: f";
    pub const DERIVE_SIGMA_ETA_TY_EQ_SIGMA: &'static str = "derive_sigma_eta: ty ≡ sigma A B";
    pub const DERIVE_SIGMA_ETA_P: &'static str = "derive_sigma_eta: p";
}
