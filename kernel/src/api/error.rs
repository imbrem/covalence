/// Kernel error messages
pub mod kernel_error {
    /// Not implemented
    pub const NOT_IMPLEMENTED: &str = "covalence: not implemented";
    /// Strategy did not return a valid subcontext
    pub const ASSUME_NOT_SUBCTX: &str = "assume: not a subcontext of parent";
    /// Strategy changed assumptions in ensure_assumptions_valid_under
    pub const ENSURE_ASSUMPTIONS_VALID_UNDER_CHANGED: &str =
        "ensure_assumptions_valid_under: assumptions changed";
    /// An assumption must be a valid type
    pub const ASSUME_IS_TY: &str = "assume: ty is not a valid type";
    /// A variable must have a valid type
    pub const ADD_VAR_IS_TY: &str = "add_var: ty is not a valid type";
    /// The parent argument of `set_parent` must have all existing parents as subcontexts
    pub const SET_PARENT_NOT_SUBCTX: &str = "set_parent: expected subcontext";
    /// The parent argument of `set_parent` must not have `ctx` as a subcontext
    pub const SET_PARENT_WOULD_CYCLE: &str = "set_parent: would induce a cycle";
    /// When we add a variable, it should be _well-scoped_: only contain variables  visible from
    /// within the current context
    pub const DERIVE_FV_ILL_SCOPED: &str = "derive_fv: var is ill-scoped";
    /// Cannot deduce that lvl1 ≤ lvl2
    pub const DERIVE_U_LE_U_LE: &str = "derive_u_le: cannot deduce that lvl1 ≤ lvl2";
    /// tm must be of type U(lvl1)
    pub const DERIVE_U_LE_TM: &str = "derive_u_le: tm must be of type U(lvl1)";
    /// `derive_close_has_ty_under` does not support variables of nonzero index
    pub const DERIVE_CLOSE_HAS_TY_UNDER_IX_NONZERO: &str =
        "derive_close_has_ty_under: we do not currently support variables of nonzero index";
    /// variable's type must be well-scoped in the parent context
    pub const DERIVE_CLOSE_HAS_TY_UNDER_ILL_SCOPED: &str =
        "derive_close_has_ty_under: variable's type may be ill-scoped";
    pub const DERIVE_CLOSE_HAS_TY_UNDER_TOO_MANY_VARS: &str =
        "derive_close_has_ty_under: variable's context must define exactly one variable";
    pub const DERIVE_CLOSE_HAS_TY_UNDER_INVALID_ASSUMPTION: &str =
        "derive_close_has_ty_under: assumption is not valid";
    pub const DERIVE_CLOSE_HAS_TY_UNDER_HAS_TY: &str = "derive_close_has_ty_under: tm";
    pub const DERIVE_EQN_LHS: &str = "derive_eqn: lhs";
    pub const DERIVE_EQN_RHS: &str = "derive_eqn: rhs";
    pub const DERIVE_PI_IMAX_LE: &str =
        "derive_pi: cannot deduce that imax(arg_lvl, res_lvl) ≤ lvl";
    pub const DERIVE_PI_ARG_TY: &str = "derive_pi: arg_ty";
    pub const DERIVE_PI_RES_TY: &str = "derive_pi: res_ty";
    pub const DERIVE_SIGMA_ARG_LVL_LE: &str = "derive_sigma: cannot deduce that arg_lvl ≤ lvl";
    pub const DERIVE_SIGMA_RES_LVL_LE: &str = "derive_sigma: cannot deduce that res_lvl ≤ lvl";
    pub const DERIVE_SIGMA_ARG_TY: &str = "derive_sigma: arg_ty";
    pub const DERIVE_SIGMA_RES_TY: &str = "derive_sigma: res_ty";
    pub const DERIVE_ABS_BODY: &str = "derive_abs: body";
    pub const DERIVE_APP_ARG: &str = "derive_app: arg";
    pub const DERIVE_APP_FUNC: &str = "derive_app: func";
    pub const DERIVE_PAIR_RES_TY: &str = "derive_pair: res_ty";
    pub const DERIVE_PAIR_FST: &str = "derive_pair: fst";
    pub const DERIVE_PAIR_SND: &str = "derive_pair: snd";
    pub const DERIVE_FST_PAIR: &str = "derive_fst: pair";
    pub const DERIVE_SND_PAIR: &str = "derive_snd: pair";
    pub const DERIVE_DITE_COND: &str = "derive_dite: cond";
    pub const DERIVE_DITE_THEN_BR: &str = "derive_dite: then_br";
    pub const DERIVE_DITE_ELSE_BR: &str = "derive_dite: else_br";
    pub const DERIVE_TRUNC_TY: &str = "derive_trunc: ty";
    pub const DERIVE_CHOOSE_TY: &str = "derive_choose: ty";
    pub const DERIVE_CHOOSE_PRED: &str = "derive_choose: pred";
    pub const DERIVE_NATS_SET_LE_LVL: &str = "derive_nats: cannot deduce that SET ≤ lvl";
    pub const DERIVE_SUCC_N: &str = "derive_succ: n";
    pub const DERIVE_NATREC_MOT: &str = "derive_natrec: mot";
    pub const DERIVE_NATREC_Z: &str = "derive_natrec: z";
    pub const DERIVE_NATREC_S: &str = "derive_natrec: s";
    pub const DERIVE_LET_BOUND: &str = "derive_let: bound";
    pub const DERIVE_LET_BODY: &str = "derive_let: body";
    pub const DERIVE_BETA_ABS_TM_EQ_ABS: &str = "derive_beta_abs: tm ≡ abs A b";
    pub const DERIVE_BETA_ABS_TM_WF: &str = "derive_beta_abs: tm wf";
    pub const DERIVE_BETA_ABS_ARG: &str = "derive_beta_abs: arg";
    pub const DERIVE_BETA_ZERO_TM_EQ_NATREC: &str = "derive_beta_zero: tm ≡ natrec C z s";
    pub const DERIVE_BETA_ZERO_TM_WF: &str = "derive_beta_zero: tm wf";
    pub const DERIVE_BETA_SUCC_TM_EQ_NATREC: &str = "derive_beta_zero: tm ≡ natrec C z s";
    pub const DERIVE_BETA_SUCC_TM_WF: &str = "derive_beta_zero: tm wf";
    pub const DERIVE_BETA_SUCC_N: &str = "derive_beta_succ: n";
    pub const DERIVE_CHOOSE_SPEC_EXISTS: &str = "derive_choose_spec: exists";
    pub const DERIVE_UNIT_EXT_A: &str = "derive_unit_ext: a";
    pub const DERIVE_PROP_EXT_TT_PROP: &str = "derive_prop_ext_tt: a prop";
    pub const DERIVE_PROP_EXT_TT_INHAB: &str = "derive_prop_ext_tt: a inhab";
    pub const DERIVE_PROP_EXT_FF_PROP: &str = "derive_prop_ext_ff: a prop";
    pub const DERIVE_PROP_EXT_FF_EMPTY: &str = "derive_prop_ext_ff: a empty";
    pub const DERIVE_EXT_EQN_INHAB: &str = "derive_ext: eqn inhab";
    pub const DERIVE_PI_ETA_TY_EQ_PI: &str = "derive_pi_eta: ty ≡ pi A B";
    pub const DERIVE_PI_ETA_F: &str = "derive_pi_eta: f";
    pub const DERIVE_SIGMA_ETA_TY_EQ_SIGMA: &str = "derive_sigma_eta: ty ≡ sigma A B";
    pub const DERIVE_SIGMA_ETA_P: &str = "derive_sigma_eta: p";
}
