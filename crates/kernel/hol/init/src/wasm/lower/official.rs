//! Checked, source-attributed witnesses for the normative WebAssembly rules.
//!
//! These are deliberately called *witnesses*, rather than upstream examples:
//! the small programs below are ours, while every instruction-typing and
//! execution step they use is a direct instance of a rule in the vendored,
//! pinned WebAssembly 3.0 SpecTec source.  The source locations are part of
//! the public result so a facade can display honest provenance without
//! exposing a SpecTec AST.
//!
//! Proof search happens in the zero-opaque [`wasm1_slice`](super::slice::wasm1_slice).
//! Every theorem returned by [`normative_witnesses`] has then been transported
//! into the caller's *full combined* rule set by [`SliceEnv::transport`].
//! Transport is kernel-checked clause-set inclusion; neither this module nor
//! the untrusted lowering mints a theorem.

use covalence_core::subst::subst_free;
use covalence_core::{Result, Term, Var};
use covalence_hol_eval::EvalThm as Thm;

use super::super::encode::{app, con, metavar_name, phi, tag};
use super::slice::SliceEnv;
use super::trace::{Config, TraceEnv, const_fold_drop_trace};
use crate::metalogic::{Premise, RuleSet};

/// Upstream pin for the vendored normative source.
pub const SPECTEC_UPSTREAM_PIN: &str = "acc6e834ff403c82554d081237f327346190ad96";

/// A stable source reference into the vendored WebAssembly 3.0 semantics.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NormativeSource {
    /// Pinned local source used by the lowering.
    pub path: &'static str,
    /// Stable source rule identity in that file.
    pub rule: &'static str,
    /// Corresponding normative section in the official WebAssembly spec.
    pub official_url: &'static str,
}

/// One checked instruction-typing instance used by a witness program.
#[derive(Debug, Clone)]
pub struct CheckedInstructionTyping {
    /// Neutral display spelling; not a SpecTec implementation object.
    pub instruction: &'static str,
    /// The exact normative rule instantiated by [`theorem`].
    pub source: NormativeSource,
    /// Hypothesis-free theorem in the full combined rule set.
    pub theorem: Thm,
}

/// A checked concrete program witness.
#[derive(Debug, Clone)]
pub struct NormativeWitness {
    /// Stable, facade-friendly identifier.
    pub id: &'static str,
    /// Human-readable WebAssembly instruction sequence.
    pub program: &'static [&'static str],
    /// Checked typing facts for every instruction schema used by the program.
    pub typing: Vec<CheckedInstructionTyping>,
    /// Hypothesis-free `Instrs_ok` theorem for the complete instruction
    /// sequence, when the exact sequence driver is available.
    pub program_typing: Option<Thm>,
    /// Normative rules used by the execution path, in program-step order.
    pub execution_sources: &'static [NormativeSource],
    /// Hypothesis-free `Steps` theorem in the full combined rule set.
    pub execution: Thm,
    /// Exact encoded initial configuration appearing in [`execution`].
    pub from: Config,
    /// Exact encoded final configuration appearing in [`execution`].
    pub to: Config,
    /// Number of non-reflexive `Step`s in the derived `Steps` chain.
    pub n_steps: usize,
}

const VALIDATION: &str = "assets/spectec/wasm-3.0/2.3-validation.instructions.spectec";
const EXECUTION: &str = "assets/spectec/wasm-3.0/4.3-execution.instructions.spectec";

const T_NOP: NormativeSource = NormativeSource {
    path: VALIDATION,
    rule: "Instr_ok/nop",
    official_url: "https://webassembly.github.io/spec/core/valid/instructions.html#valid-nop",
};
const T_CONST: NormativeSource = NormativeSource {
    path: VALIDATION,
    rule: "Instr_ok/const",
    official_url: "https://webassembly.github.io/spec/core/valid/instructions.html#valid-const",
};
const T_BINOP: NormativeSource = NormativeSource {
    path: VALIDATION,
    rule: "Instr_ok/binop",
    official_url: "https://webassembly.github.io/spec/core/valid/instructions.html#valid-binop",
};
const T_DROP: NormativeSource = NormativeSource {
    path: VALIDATION,
    rule: "Instr_ok/drop",
    official_url: "https://webassembly.github.io/spec/core/valid/instructions.html#valid-drop",
};
const E_NOP: NormativeSource = NormativeSource {
    path: EXECUTION,
    rule: "Step_pure/nop",
    official_url: "https://webassembly.github.io/spec/core/exec/instructions.html#exec-nop",
};
const E_DROP: NormativeSource = NormativeSource {
    path: EXECUTION,
    rule: "Step_pure/drop",
    official_url: "https://webassembly.github.io/spec/core/exec/instructions.html#exec-drop",
};
const E_BINOP: NormativeSource = NormativeSource {
    path: EXECUTION,
    rule: "Step_pure/binop-val",
    official_url: "https://webassembly.github.io/spec/core/exec/instructions.html#exec-binop",
};
const E_PURE: NormativeSource = NormativeSource {
    path: EXECUTION,
    rule: "Step/pure",
    official_url: "https://webassembly.github.io/spec/core/exec/conventions.html#exec-notation",
};
const E_FRAME: NormativeSource = NormativeSource {
    path: EXECUTION,
    rule: "Step/ctxt-instrs",
    official_url: "https://webassembly.github.io/spec/core/exec/conventions.html#exec-notation",
};
const E_TRANS: NormativeSource = NormativeSource {
    path: EXECUTION,
    rule: "Steps/trans",
    official_url: "https://webassembly.github.io/spec/core/exec/conventions.html#exec-notation",
};

fn err(message: impl Into<String>) -> covalence_core::Error {
    covalence_core::Error::ConnectiveRule(format!("WASM normative witness: {}", message.into()))
}

fn a(x: Term, y: Term) -> Result<Term> {
    app(x, y)
}

fn i32t() -> Result<Term> {
    a(con("case.I32"), con("tup"))
}

fn addop() -> Result<Term> {
    a(con("case.ADD"), con("tup"))
}

fn payload(k: u64) -> Result<Term> {
    a(
        con("tup"),
        a(con("num.nat"), covalence_hol_eval::mk_nat(k))?,
    )
}

fn iv(k: u64) -> Result<Term> {
    a(con("case.%"), payload(k)?)
}

fn const_i32(k: u64) -> Result<Term> {
    a(con("case.CONST"), a(a(con("tup"), i32t()?)?, iv(k)?)?)
}

fn drop_instr() -> Result<Term> {
    a(con("case.DROP"), con("tup"))
}

fn list(es: impl IntoIterator<Item = Term>) -> Result<Term> {
    es.into_iter().try_fold(con("list"), a)
}

fn instr_type(inputs: Term, locals: Term, outputs: Term) -> Result<Term> {
    a(
        con("case.%->_%%"),
        a(
            a(
                a(con("tup"), a(con("case.%"), a(con("tup"), inputs)?)?)?,
                locals,
            )?,
            a(con("case.%"), a(con("tup"), outputs)?)?,
        )?,
    )
}

fn relation_tag(term: &Term) -> Option<String> {
    let mut cur = term;
    loop {
        let (f, _) = cur.as_app()?;
        match f.as_app() {
            Some((head, constant)) => {
                if head.as_free().map(|v| v.name()) == Some("st$app")
                    && let Some(tag) = constant
                        .as_free()
                        .and_then(|v| v.name().strip_prefix("st$c$rel."))
                {
                    return Some(tag.to_owned());
                }
                cur = f;
            }
            None => return None,
        }
    }
}

/// Derive the complete `Instrs_ok` judgement for `[NOP]`.
///
/// This deliberately exercises every premise of `Instrs_ok/seq`: both
/// concatenations, the instruction rule, the empty locals-condition star,
/// the exact `(SET t)*` map, `$with_locals` at empty lists, and the recursive
/// empty sequence. Nothing is skipped or assumed.
fn nop_program_typing(env: &SliceEnv, full: &RuleSet<'static>, ctx: &Term) -> Result<Thm> {
    let tr = TraceEnv::for_slice(env)?;
    let nil = con("list");
    let nop = a(con("case.NOP"), con("tup"))?;

    let empty_idx = env
        .rule_index(Some("Instrs_ok"), "empty")
        .ok_or_else(|| err("wasm1 slice has no Instrs_ok/empty"))?;
    let empty = env.derive(empty_idx, std::slice::from_ref(ctx), vec![])?;

    let nop_idx = env
        .rule_index(Some("Instr_ok"), "nop")
        .ok_or_else(|| err("wasm1 slice has no Instr_ok/nop"))?;
    let nop_ok = env.derive(nop_idx, std::slice::from_ref(ctx), vec![])?;

    let star_idx = env
        .rules()
        .iter()
        .position(|meta| meta.relation == "star.Instrs_ok.seq.1" && meta.metavars.len() == 1)
        .ok_or_else(|| err("wasm1 slice has no empty Instrs_ok/seq locals star"))?;
    let star = env.derive(star_idx, std::slice::from_ref(ctx), vec![])?;

    let seq_idx = env
        .rule_index(Some("Instrs_ok"), "seq")
        .ok_or_else(|| err("wasm1 slice has no Instrs_ok/seq"))?;
    let seq_clause = &env.slice().clauses()[seq_idx];
    let map_relation = seq_clause
        .prems
        .iter()
        .filter_map(|premise| match premise {
            crate::wasm::lower::LowerPrem::Judgement(judgement) => relation_tag(judgement),
            crate::wasm::lower::LowerPrem::Side(_) => None,
        })
        .find(|relation| relation.starts_with("ev.map."))
        .ok_or_else(|| err("Instrs_ok/seq has no exact localtype map premise"))?;
    let map_idx = env
        .rules()
        .iter()
        .position(|meta| meta.relation == map_relation && meta.metavars.is_empty())
        .ok_or_else(|| err(format!("{map_relation} has no empty-map clause")))?;
    let map = env.derive(map_idx, &[], vec![])?;

    let with_locals_idx = env
        .rules()
        .iter()
        .position(|meta| meta.relation == "fn.with_locals" && meta.metavars.len() == 1)
        .ok_or_else(|| err("wasm1 slice has no empty with_locals clause"))?;
    let with_locals = env.derive(with_locals_idx, std::slice::from_ref(ctx), vec![])?;

    let singleton = list([nop.clone()])?;
    let (whole, cat_instrs) = tr.prove_cat(&singleton, &nil)?;
    if whole != singleton {
        return Err(err("singleton instruction concatenation endpoint mismatch"));
    }
    let (locals, cat_locals) = tr.prove_cat(&nil, &nil)?;
    if locals != nil {
        return Err(err("empty locals concatenation endpoint mismatch"));
    }

    // Metavariable order is pinned by ClauseMeta and asserted by derive.
    let args = [
        ctx.clone(), // C
        nop,         // instr_1
        nil.clone(), // instr_2*
        nil.clone(), // t_1*
        nil.clone(), // x_1*
        nil.clone(), // x_2*
        nil.clone(), // t_3*
        singleton,   // concatenated instruction sequence
        nil.clone(), // concatenated initialized-local indices
        nil.clone(), // t_2*
        nil.clone(), // init*
        nil.clone(), // t*
        i32t()?,     // unused empty-star element witness
        nil.clone(), // exact (SET t)* map result
        ctx.clone(), // with_locals result
    ];
    if args.len() != env.rules()[seq_idx].metavars.len() {
        return Err(err(format!(
            "Instrs_ok/seq metavar layout changed: expected {}, got {}",
            args.len(),
            env.rules()[seq_idx].metavars.len()
        )));
    }
    let small = env.derive(
        seq_idx,
        &args,
        vec![
            Premise::Derivation(cat_instrs),
            Premise::Derivation(cat_locals),
            Premise::Derivation(nop_ok),
            Premise::Derivation(star),
            Premise::Derivation(map),
            Premise::Derivation(with_locals),
            Premise::Derivation(empty),
        ],
    )?;
    let judgement = tag(
        "Instrs_ok",
        a(
            a(a(con("tup"), ctx.clone())?, whole)?,
            instr_type(nil.clone(), nil.clone(), nil)?,
        )?,
    )?;
    let mut instantiated = seq_clause.concl.clone();
    for (metavar, argument) in seq_clause.metavars.iter().zip(&args) {
        instantiated = subst_free(
            &instantiated,
            &Var::new(metavar_name(metavar), phi()),
            argument,
        );
    }
    if instantiated != judgement {
        return Err(err(format!(
            "neutral NOP judgement encoding mismatch:\nclause={instantiated:#?}\nneutral={judgement:#?}"
        )));
    }
    let expected_small = crate::metalogic::derivable(env.rule_set(), &judgement)?;
    if small.concl() != &expected_small {
        return Err(err(
            "Instrs_ok theorem does not state exact NOP program typing",
        ));
    }
    let theorem = env.transport(full, &small)?;
    if !theorem.hyps().is_empty() {
        return Err(err("transported Instrs_ok theorem has hypotheses"));
    }
    Ok(theorem)
}

fn typing(
    env: &SliceEnv,
    full: &RuleSet<'static>,
    instruction: &'static str,
    rule: &'static str,
    source: NormativeSource,
    args: &[Term],
    premises: Vec<Premise>,
) -> Result<CheckedInstructionTyping> {
    let idx = env
        .rule_index(Some("Instr_ok"), rule)
        .ok_or_else(|| err(format!("wasm1 slice has no Instr_ok/{rule}")))?;
    let small = env.derive(idx, args, premises)?;
    let theorem = env.transport(full, &small)?;
    if !theorem.hyps().is_empty() {
        return Err(err(format!("Instr_ok/{rule} transport has hypotheses")));
    }
    Ok(CheckedInstructionTyping {
        instruction,
        source,
        theorem,
    })
}

fn i32_valtype_ok(env: &SliceEnv, ctx: &Term, i32: &Term) -> Result<Thm> {
    let num = env
        .rule_index(Some("Numtype_ok"), "")
        .ok_or_else(|| err("wasm1 slice has no Numtype_ok rule"))?;
    let d_num = env.derive(num, &[ctx.clone(), i32.clone()], vec![])?;
    let sort = env
        .rule_index(Some("ev.sort.numtype"), "")
        .ok_or_else(|| err("wasm1 slice has no ev.sort.numtype rule"))?;
    let d_sort = env.derive(sort, &[], vec![])?;
    let val = env
        .rule_index(Some("Valtype_ok"), "num")
        .ok_or_else(|| err("wasm1 slice has no Valtype_ok/num rule"))?;
    env.derive(
        val,
        &[ctx.clone(), i32.clone()],
        vec![Premise::Derivation(d_num), Premise::Derivation(d_sort)],
    )
}

fn transport_trace(env: &SliceEnv, full: &RuleSet<'static>, small: Thm) -> Result<Thm> {
    let theorem = env.transport(full, &small)?;
    if !theorem.hyps().is_empty() {
        return Err(err("transported execution theorem has hypotheses"));
    }
    Ok(theorem)
}

/// Derive three concrete, hypothesis-free normative witnesses and transport
/// every theorem into `full`.
///
/// `env` must be a [`wasm1_slice`](super::slice::wasm1_slice) environment (or
/// another slice containing the same closure):
///
/// 1. `nop` is well-typed and executes to the empty sequence;
/// 2. `i32.const 5; drop` has checked `const`/`drop` instruction typings and
///    executes to the empty sequence;
/// 3. `i32.const 2; i32.const 3; i32.add; drop` has checked instruction
///    typings and executes by exact integer evaluation to the empty sequence.
///
/// The concrete programs are local witnesses, not claimed to be files from
/// upstream. Their rule semantics are the pinned normative sources recorded
/// in each result.
pub fn normative_witnesses(
    env: &SliceEnv,
    full: &RuleSet<'static>,
    z: &Term,
) -> Result<Vec<NormativeWitness>> {
    let tr = TraceEnv::for_slice(env)?;
    let ctx = con("struct");
    let i32 = i32t()?;

    // NOP: exact instruction typing and one genuine Step followed by refl.
    let nop_typing = typing(env, full, "nop", "nop", T_NOP, &[ctx.clone()], vec![])?;
    let nop_idx = tr
        .rule_index("Step_pure", "nop")
        .ok_or_else(|| err("wasm1 slice has no Step_pure/nop"))?;
    let nop_pure = tr.derive(nop_idx, &[], vec![])?;
    let nop_prog = list([a(con("case.NOP"), con("tup"))?])?;
    let nop_step = tr.lift_pure(z, &nop_prog, &con("list"), nop_pure)?;
    let nop_small = tr.chain(std::slice::from_ref(&nop_step))?;
    let nop_program_typing = nop_program_typing(env, full, &ctx)?;
    let nop = NormativeWitness {
        id: "mvp.nop",
        program: &["nop"],
        typing: vec![nop_typing],
        program_typing: Some(nop_program_typing),
        execution_sources: &[E_NOP, E_PURE, E_TRANS],
        execution: transport_trace(env, full, nop_small)?,
        from: nop_step.from,
        to: nop_step.to,
        n_steps: 1,
    };

    // CONST; DROP: `const` is premise-free; `drop` uses a checked
    // Valtype_ok(I32) derivation. Execution applies the normative drop rule
    // to the concrete value instruction.
    let c5 = const_i32(5)?;
    let d = drop_instr()?;
    let const5_typing = typing(
        env,
        full,
        "i32.const 5",
        "const",
        T_CONST,
        &[ctx.clone(), i32.clone(), iv(5)?],
        vec![],
    )?;
    let drop_premise = i32_valtype_ok(env, &ctx, &i32)?;
    let drop_typing = typing(
        env,
        full,
        "drop",
        "drop",
        T_DROP,
        &[ctx.clone(), i32.clone()],
        vec![Premise::Derivation(drop_premise)],
    )?;
    let drop_idx = tr
        .rule_index("Step_pure", "drop")
        .ok_or_else(|| err("wasm1 slice has no Step_pure/drop"))?;
    let d_sort = tr.prove_sort_val(&c5)?;
    let drop_pure = tr.derive(
        drop_idx,
        std::slice::from_ref(&c5),
        vec![Premise::Derivation(d_sort)],
    )?;
    let const_drop_prog = list([c5, d])?;
    let drop_step = tr.lift_pure(z, &const_drop_prog, &con("list"), drop_pure)?;
    let drop_small = tr.chain(std::slice::from_ref(&drop_step))?;
    let const_drop = NormativeWitness {
        id: "mvp.const-drop",
        program: &["i32.const 5", "drop"],
        typing: vec![const5_typing, drop_typing.clone()],
        program_typing: None,
        execution_sources: &[E_DROP, E_PURE, E_TRANS],
        execution: transport_trace(env, full, drop_small)?,
        from: drop_step.from,
        to: drop_step.to,
        n_steps: 1,
    };

    // CONST; CONST; ADD; DROP: reuse the exact arithmetic trace constructor,
    // then independently instantiate the three normative instruction-typing
    // schemas it uses.
    let const2 = typing(
        env,
        full,
        "i32.const 2",
        "const",
        T_CONST,
        &[ctx.clone(), i32.clone(), iv(2)?],
        vec![],
    )?;
    let const3 = typing(
        env,
        full,
        "i32.const 3",
        "const",
        T_CONST,
        &[ctx.clone(), i32.clone(), iv(3)?],
        vec![],
    )?;
    let add = typing(
        env,
        full,
        "i32.add",
        "binop",
        T_BINOP,
        &[ctx, i32, addop()?],
        vec![],
    )?;
    let (small, from, to, n_steps) = const_fold_drop_trace(&tr, z)?;
    let add_drop = NormativeWitness {
        id: "mvp.i32-add-drop",
        program: &["i32.const 2", "i32.const 3", "i32.add", "drop"],
        typing: vec![const2, const3, add, drop_typing],
        program_typing: None,
        execution_sources: &[E_BINOP, E_PURE, E_FRAME, E_DROP, E_PURE, E_TRANS],
        execution: transport_trace(env, full, small)?,
        from,
        to,
        n_steps,
    };

    Ok(vec![nop, const_drop, add_drop])
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::wasm::lower::rule_set_of;
    use crate::wasm::lower::slice::{SliceEnv, wasm1_slice};
    use crate::wasm::lower::total::{total_spec_clauses, with_total_stack};
    use crate::wasm::spec::wasm_spec;

    fn ground_z() -> Term {
        a(
            con("case.%;%"),
            a(a(con("tup"), con("struct")).unwrap(), con("struct")).unwrap(),
        )
        .unwrap()
    }

    #[test]
    fn normative_witnesses_are_checked_in_the_full_combined_set() {
        with_total_stack(|| {
            let (clauses, report) = total_spec_clauses(&wasm_spec()).unwrap();
            let full = rule_set_of(clauses.clone());
            let slice = wasm1_slice(&clauses, &report.metas).unwrap();
            assert_eq!(slice.report().opaque_total(), 0);
            let env = SliceEnv::new(slice);
            let witnesses = normative_witnesses(&env, &full, &ground_z()).unwrap();

            assert_eq!(
                witnesses.iter().map(|w| w.id).collect::<Vec<_>>(),
                ["mvp.nop", "mvp.const-drop", "mvp.i32-add-drop"]
            );
            assert_eq!(
                witnesses.iter().map(|w| w.n_steps).collect::<Vec<_>>(),
                [1, 1, 2]
            );
            assert!(witnesses[0].program_typing.is_some());
            assert!(
                witnesses[1..]
                    .iter()
                    .all(|witness| witness.program_typing.is_none())
            );
            for witness in &witnesses {
                assert!(
                    witness.execution.hyps().is_empty(),
                    "{} execution has hypotheses",
                    witness.id
                );
                assert_eq!(
                    witness.execution.concl(),
                    &crate::metalogic::derivable(
                        &full,
                        &TraceEnv::for_slice(&env)
                            .unwrap()
                            .steps_judgement(&witness.from, &witness.to)
                            .unwrap(),
                    )
                    .unwrap(),
                    "{} execution theorem states the exact endpoints",
                    witness.id
                );
                assert!(!witness.typing.is_empty());
                if let Some(program_typing) = &witness.program_typing {
                    assert!(program_typing.hyps().is_empty());
                }
                for typing in &witness.typing {
                    assert!(
                        typing.theorem.hyps().is_empty(),
                        "{} typing has hypotheses",
                        typing.instruction
                    );
                    assert_eq!(typing.source.path, VALIDATION);
                    assert!(
                        typing
                            .source
                            .official_url
                            .starts_with("https://webassembly.github.io/spec/core/")
                    );
                }
                for source in witness.execution_sources {
                    assert_eq!(source.path, EXECUTION);
                    assert!(
                        source
                            .official_url
                            .starts_with("https://webassembly.github.io/spec/core/")
                    );
                }
            }
        })
    }
}
