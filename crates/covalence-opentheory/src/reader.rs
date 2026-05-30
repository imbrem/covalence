//! Text parser for OpenTheory articles.
//!
//! Dispatches each line to the appropriate `ArticleMachine` method.

use crate::error::OtError;
use crate::machine::ArticleMachine;

/// Parse and execute an OpenTheory article (a sequence of lines) on the given machine.
pub fn read_article<M: ArticleMachine>(machine: &mut M, input: &str) -> Result<(), OtError> {
    for (lineno, line) in input.lines().enumerate() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        execute_line(machine, line)
            .map_err(|e| OtError::ParseError(format!("line {}: {line}: {e}", lineno + 1)))?;
    }
    Ok(())
}

fn execute_line<M: ArticleMachine>(machine: &mut M, line: &str) -> Result<(), OtError> {
    // Check for number literal.
    if let Ok(n) = line.parse::<i64>() {
        return machine.push_num(n);
    }
    // Check for quoted name.
    if line.starts_with('"') && line.ends_with('"') && line.len() >= 2 {
        let s = &line[1..line.len() - 1];
        return machine.push_name(s);
    }

    match line {
        "absTerm" => machine.cmd_abs_term(),
        "absThm" => machine.cmd_abs_thm(),
        "appTerm" => machine.cmd_app_term(),
        "appThm" => machine.cmd_app_thm(),
        "assume" => machine.cmd_assume(),
        "axiom" => machine.cmd_axiom(),
        "betaConv" => machine.cmd_beta_conv(),
        "cons" => machine.cmd_cons(),
        "const" => machine.cmd_const(),
        "constTerm" => machine.cmd_const_term(),
        "deductAntisym" => machine.cmd_deduct_antisym(),
        "def" => machine.cmd_def(),
        "defineConst" => machine.cmd_define_const(),
        "defineTypeOp" => machine.cmd_define_type_op(),
        "eqMp" => machine.cmd_eq_mp(),
        "nil" => machine.cmd_nil(),
        "opType" => machine.cmd_op_type(),
        "pop" => machine.cmd_pop(),
        "ref" => machine.cmd_ref(),
        "refl" => machine.cmd_refl(),
        "remove" => machine.cmd_remove(),
        "subst" => machine.cmd_subst(),
        "thm" => machine.cmd_thm(),
        "trans" => machine.cmd_trans(),
        "typeOp" => machine.cmd_type_op(),
        "var" => machine.cmd_var(),
        "varTerm" => machine.cmd_var_term(),
        "varType" => machine.cmd_var_type(),
        "version" => machine.cmd_version(),
        // version 6+ commands
        "defineConstList" => machine.cmd_define_const_list(),
        "hdTl" => machine.cmd_hd_tl(),
        "pragma" => machine.cmd_pragma(),
        "proveHyp" => machine.cmd_prove_hyp(),
        "sym" => machine.cmd_sym(),
        _ => Err(OtError::UnknownCommand(line.to_string())),
    }
}
