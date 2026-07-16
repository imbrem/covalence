//! [`RelationEnv`] — the high-level API for a lowered SpecTec **relation**, the
//! peer of [`GrammarEnv`](crate::grammar::cfg::GrammarEnv) for grammars.
//!
//! [`crate::wasm::relation`] already lowers a SpecTec `rel` into an impredicative
//! `Derivable_R` rule set and applies rules ([`derive`](crate::wasm::relation::derive)),
//! but as *free functions over a bare `RuleSet`*: a caller must itself track the
//! rule count, each rule's metavariable order, and the reified-and-tagged
//! judgement term. `RelationEnv` bundles those so a caller states judgements and
//! applies rules by name/expression — exactly the ergonomics `GrammarEnv` gives
//! for grammars.

use covalence_core::{Error, Result, Term};
use covalence_hol_eval::EvalThm as Thm;
use covalence_spectec::ast::{SpecTecDef, SpecTecExp, SpecTecRule};

use crate::metalogic::RuleSet;
use crate::wasm::encode::{collect_metavars, encode_exp, tag};
use crate::wasm::relation::{LoweringReport, derivable, derive, rule_set, spec_rule_set};

/// Per-clause metadata: which relation the rule belongs to, its name, and its
/// metavariable order (the `∀`-order [`RelationEnv::derive`] fills with `args`).
#[derive(Debug, Clone)]
pub struct RuleMeta {
    /// The relation name (the tag on the encoded judgement).
    pub relation: String,
    /// The rule's name (`""` for an unnamed rule).
    pub name: String,
    /// Metavariable ids in first-seen (`∀`-binding = `args`) order.
    pub metavars: Vec<String>,
}

/// A lowered SpecTec relation (or a whole spec's relations) you build
/// `⊢ Derivable_R ⌜J⌝` derivations in.
pub struct RelationEnv {
    rs: RuleSet<'static>,
    n_clauses: usize,
    rules: Vec<RuleMeta>,
    report: LoweringReport,
}

impl RelationEnv {
    /// Build from a **single** relation `def` (a [`SpecTecDef::Rel`]); errors if
    /// any of its rules can't be lowered. Peer of `GrammarEnv::new`. Clause `i`
    /// is rule `i`.
    pub fn relation(def: &SpecTecDef) -> Result<Self> {
        let SpecTecDef::Rel { x, rules, .. } = def else {
            return Err(Error::ConnectiveRule(
                "spectec relation: definition is not a `rel`".into(),
            ));
        };
        let rs = rule_set(def)?;
        let n_clauses = rules.len();
        let meta = rules.iter().map(|r| rule_meta(x, r)).collect();
        Ok(RelationEnv {
            rs,
            n_clauses,
            rules: meta,
            report: LoweringReport::default(),
        })
    }

    /// Build from a **whole spec**'s relations (peer of `spec_rule_set`),
    /// skipping rules that can't lower yet and recording them in the
    /// [`LoweringReport`]. Clause order follows the flattened *lowered* rules.
    /// This is the WASM-semantics entry point: `RelationEnv::spec(wasm_spec())`.
    pub fn spec(defs: &[SpecTecDef]) -> Self {
        let (rs, report) = spec_rule_set(defs);
        // Recompute per-clause metadata over exactly the lowered rules, in the
        // same flattened order `spec_rule_set` uses.
        let mut rules = Vec::new();
        for def in relations(defs) {
            let SpecTecDef::Rel {
                x, rules: rs_rules, ..
            } = def
            else {
                continue;
            };
            for rule in rs_rules {
                if rule_lowers(rule) {
                    rules.push(rule_meta(x, rule));
                }
            }
        }
        let n_clauses = rules.len();
        debug_assert_eq!(n_clauses, report.lowered);
        RelationEnv {
            rs,
            n_clauses,
            rules,
            report,
        }
    }

    /// The lowering report (populated by [`RelationEnv::spec`]).
    pub fn report(&self) -> &LoweringReport {
        &self.report
    }

    /// The number of clauses (lowered rules).
    pub fn n_clauses(&self) -> usize {
        self.n_clauses
    }

    /// Per-clause metadata (relation/rule name + metavar order).
    pub fn rules(&self) -> &[RuleMeta] {
        &self.rules
    }

    /// The clause index of the first rule named `name` (in `relation`, if
    /// given), or `None`.
    pub fn rule_index(&self, relation: Option<&str>, name: &str) -> Option<usize> {
        self.rules
            .iter()
            .position(|m| m.name == name && relation.is_none_or(|r| m.relation == r))
    }

    /// State `Derivable_R ⌜R(e)⌝` for a relation name and a SpecTec expression —
    /// the reified proposition a derivation for this judgement concludes.
    pub fn derivable(&self, relation: &str, e: &SpecTecExp) -> Result<Term> {
        derivable(&self.rs, &tag(relation, encode_exp(e)?)?)
    }

    /// **Apply rule `clause_idx`** with pre-encoded `args` (in the rule's
    /// metavar order) and `premise_ders` (each `⊢ Derivable_R ⌜premⱼ⌝`),
    /// yielding a hypothesis-free `⊢ Derivable_R ⌜concl[args]⌝`. Delegates to
    /// [`crate::wasm::relation::derive`].
    pub fn derive(&self, clause_idx: usize, args: &[Term], premise_ders: Vec<Thm>) -> Result<Thm> {
        derive(&self.rs, clause_idx, self.n_clauses, args, premise_ders)
    }

    /// Ergonomic [`RelationEnv::derive`]: pass the metavariable instantiations as
    /// **SpecTec expressions** (they are encoded internally, in `args` order —
    /// which must match this clause's [`RuleMeta::metavars`] order).
    pub fn derive_exprs(
        &self,
        clause_idx: usize,
        args: &[SpecTecExp],
        premise_ders: Vec<Thm>,
    ) -> Result<Thm> {
        let encoded = args.iter().map(encode_exp).collect::<Result<Vec<_>>>()?;
        self.derive(clause_idx, &encoded, premise_ders)
    }
}

impl super::Fragment for RelationEnv {
    fn judgement_kind(&self) -> &'static str {
        "Derivable_R"
    }

    fn n_clauses(&self) -> usize {
        self.n_clauses
    }

    fn derive(
        &self,
        clause_idx: usize,
        args: &[Term],
        premises: Vec<super::FragPremise>,
    ) -> Result<Thm> {
        // Relation premises are all sub-derivations; a `Side` leaf is a grammar
        // concept that never occurs here — reject it rather than silently drop.
        let ders = premises
            .into_iter()
            .map(|p| match p {
                super::FragPremise::Derivation(t) => Ok(t),
                super::FragPremise::Side(_) => Err(Error::ConnectiveRule(
                    "spectec relation: a relation has no `Side` premises".into(),
                )),
            })
            .collect::<Result<Vec<_>>>()?;
        RelationEnv::derive(self, clause_idx, args, ders)
    }
}

/// The metavariable order of a rule — conclusion first, then each inductive
/// premise, matching [`crate::wasm::relation`]'s `lower_rule` collection.
fn rule_meta(relation: &str, rule: &SpecTecRule) -> RuleMeta {
    let SpecTecRule::Rule { x, e, prs, .. } = rule;
    let mut metavars = Vec::new();
    collect_metavars(e, &mut metavars);
    for pr in prs {
        if let covalence_spectec::ast::SpecTecPrem::Rule { e: pr_e, .. } = pr {
            collect_metavars(pr_e, &mut metavars);
        }
    }
    RuleMeta {
        relation: relation.to_string(),
        name: x.clone(),
        metavars,
    }
}

/// Whether a rule lowers under the current engine (only inductive `Rule`
/// premises supported) — mirrors `lower_rule`'s acceptance so [`RelationEnv::spec`]
/// re-derives clause metadata over exactly the lowered rules.
fn rule_lowers(rule: &SpecTecRule) -> bool {
    let SpecTecRule::Rule { prs, .. } = rule;
    prs.iter()
        .all(|pr| matches!(pr, covalence_spectec::ast::SpecTecPrem::Rule { .. }))
}

/// Every `rel` in `defs`, descending into `Rec` groups.
fn relations(defs: &[SpecTecDef]) -> Vec<&SpecTecDef> {
    let mut out = Vec::new();
    for def in defs {
        match def {
            SpecTecDef::Rel { .. } => out.push(def),
            SpecTecDef::Rec { ds } => out.extend(relations(ds)),
            _ => {}
        }
    }
    out
}

/// Find a relation `rel` by name in `defs`, descending into `Rec` groups.
pub fn find_relation<'a>(defs: &'a [SpecTecDef], name: &str) -> Option<&'a SpecTecDef> {
    relations(defs)
        .into_iter()
        .find(|d| matches!(d, SpecTecDef::Rel { x, .. } if x == name))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::wasm::spec::wasm_spec;

    /// A ground nullary constructor leaf, e.g. `S`, `I32`, `ZERO`, `NOP`.
    fn leaf(name: &str) -> SpecTecExp {
        SpecTecExp::Case {
            op: covalence_spectec::ast::MixOp::new(vec![name.to_string()]),
            e1: Box::new(SpecTecExp::Tup { es: vec![] }),
        }
    }

    /// **Basic WASM semantics: value typing.** `Num_ok` is the single-rule
    /// relation "a numeric constant `CONST nt c` has type `nt`". We derive the
    /// concrete instance `S ⊢ CONST(I32, 0) : I32`, kernel-checked and
    /// hypothesis-free, entirely through `RelationEnv`.
    #[test]
    fn wasm_num_ok_typing() {
        let defs = wasm_spec();
        let def = find_relation(&defs, "Num_ok").expect("Num_ok relation present");
        let env = RelationEnv::relation(def).unwrap();
        assert_eq!(env.n_clauses(), 1);

        // rule 0, metavars [s, nt, c] := [S, I32, ZERO].
        let args = [leaf("S"), leaf("I32"), leaf("ZERO")];
        let thm = env.derive_exprs(0, &args, vec![]).unwrap();
        assert!(thm.hyps().is_empty(), "value typing is hypothesis-free");

        // The conclusion is exactly `Derivable_Num_ok ⌜(S, CONST(I32,ZERO), I32)⌝`.
        let judgement = SpecTecExp::Tup {
            es: vec![
                leaf("S"),
                SpecTecExp::Case {
                    op: covalence_spectec::ast::MixOp::new(vec!["CONST".to_string()]),
                    e1: Box::new(SpecTecExp::Tup {
                        es: vec![leaf("I32"), leaf("ZERO")],
                    }),
                },
                leaf("I32"),
            ],
        };
        assert_eq!(thm.concl(), &env.derivable("Num_ok", &judgement).unwrap());
    }

    /// **Basic WASM semantics: reduction.** `Steps` is the reflexive-transitive
    /// closure of single-step reduction (`↪*`). Its `refl` rule gives
    /// `z; instr* ↪* z; instr*`; we derive `Z; [NOP] ↪* Z; [NOP]`, kernel-checked
    /// and hypothesis-free, through `RelationEnv` — a genuine (if trivial)
    /// operational-semantics judgement.
    #[test]
    fn wasm_steps_refl_reduction() {
        let defs = wasm_spec();
        let def = find_relation(&defs, "Steps").expect("Steps relation present");
        let env = RelationEnv::relation(def).unwrap();
        let refl = env.rule_index(Some("Steps"), "refl").expect("refl rule");

        // metavars [z, instr] := [Z, NOP].
        let thm = env
            .derive_exprs(refl, &[leaf("Z"), leaf("NOP")], vec![])
            .unwrap();
        assert!(thm.hyps().is_empty());
        // Reached through the unifying `Fragment` trait.
        assert_eq!(super::super::Fragment::judgement_kind(&env), "Derivable_R");
        assert_eq!(super::super::Fragment::n_clauses(&env), 2);
    }

    /// `[e₀, e₁, …]` as a SpecTec instruction sequence expression.
    fn list(es: Vec<SpecTecExp>) -> SpecTecExp {
        SpecTecExp::List { es }
    }

    /// **Basic WASM semantics: actual instruction reduction.** `Step_pure` is
    /// the pure single-step reduction relation (`instr* ↪ instr*`). Several of
    /// its rules are premise-free — genuine one-step executions we derive
    /// through the combined spec env (which keeps the premise-free rules and
    /// skips the side-condition ones), kernel-checked and hypothesis-free:
    ///
    /// - `nop`:         `[NOP] ↪ []`               (fully ground, no metavars)
    /// - `unreachable`: `[UNREACHABLE] ↪ [TRAP]`   (fully ground)
    /// - `drop`:        `[v, DROP] ↪ []`           (one metavar, the dropped value)
    #[test]
    fn wasm_step_pure_reduction() {
        let defs = wasm_spec();
        let env = RelationEnv::spec(&defs);

        // nop: [NOP] ↪ []  — the cleanest real reduction, zero metavars.
        let nop = env.rule_index(Some("Step_pure"), "nop").expect("nop rule");
        let thm = env.derive_exprs(nop, &[], vec![]).unwrap();
        assert!(thm.hyps().is_empty());
        let nop_judgement = SpecTecExp::Tup {
            es: vec![list(vec![leaf("NOP")]), list(vec![])],
        };
        assert_eq!(
            thm.concl(),
            &env.derivable("Step_pure", &nop_judgement).unwrap(),
            "nop reduces [NOP] to []"
        );

        // unreachable: [UNREACHABLE] ↪ [TRAP].
        let unreach = env
            .rule_index(Some("Step_pure"), "unreachable")
            .expect("unreachable rule");
        let thm = env.derive_exprs(unreach, &[], vec![]).unwrap();
        assert!(thm.hyps().is_empty());
        assert_eq!(
            thm.concl(),
            &env.derivable(
                "Step_pure",
                &SpecTecExp::Tup {
                    es: vec![list(vec![leaf("UNREACHABLE")]), list(vec![leaf("TRAP")])],
                }
            )
            .unwrap()
        );

        // drop: [v, DROP] ↪ []  — one metavar `val`, instantiated with a const.
        let drop = env
            .rule_index(Some("Step_pure"), "drop")
            .expect("drop rule");
        let val = SpecTecExp::Case {
            op: covalence_spectec::ast::MixOp::new(vec!["CONST".to_string()]),
            e1: Box::new(SpecTecExp::Tup {
                es: vec![leaf("I32"), leaf("ZERO")],
            }),
        };
        let thm = env.derive_exprs(drop, &[val], vec![]).unwrap();
        assert!(thm.hyps().is_empty());
    }

    /// **Basic WASM semantics: compositional validity typing.** A `valtype`
    /// that is a numeric type is valid iff that numeric type is valid —
    /// `Valtype_ok/num` has the inductive premise `Numtype_ok`. Over the
    /// *combined* spec rule set (where all relations share one predicate `d`, so
    /// a cross-relation premise composes), we derive the `Numtype_ok` base then
    /// discharge it into `Valtype_ok/num`, building `⊢ C ⊢ (num I32) : ok` from
    /// `⊢ C ⊢ I32 : ok` — a real two-relation WASM validity derivation, kernel-
    /// checked and hypothesis-free.
    #[test]
    fn wasm_valtype_ok_compositional() {
        let defs = wasm_spec();
        let env = RelationEnv::spec(&defs);

        let numtype_ok = env
            .rule_index(Some("Numtype_ok"), "")
            .expect("Numtype_ok base");
        let valtype_num = env
            .rule_index(Some("Valtype_ok"), "num")
            .expect("Valtype_ok/num");

        // Base: ⊢ Derivable_Numtype_ok ⌜(C, I32)⌝  (metavars [C, numtype]).
        let ctx = leaf("C"); // an opaque context constant
        let i32 = leaf("I32");
        let base = env
            .derive_exprs(numtype_ok, &[ctx.clone(), i32.clone()], vec![])
            .unwrap();
        assert!(base.hyps().is_empty());
        let num_judgement = SpecTecExp::Tup {
            es: vec![ctx.clone(), i32.clone()],
        };
        assert_eq!(
            base.concl(),
            &env.derivable("Numtype_ok", &num_judgement).unwrap()
        );

        // Step: Valtype_ok/num (metavars [C, numtype]) discharging the base
        // premise → ⊢ Derivable_Valtype_ok ⌜(C, num I32)⌝, hypothesis-free.
        // (The `numtype ↑ valtype` subtype coercion encodes to its underlying
        // numtype, so the valtype judgement is `(C, I32)` too.)
        let valid = env
            .derive_exprs(valtype_num, &[ctx.clone(), i32.clone()], vec![base])
            .unwrap();
        assert!(valid.hyps().is_empty());
        // `numtype ↑ valtype` encodes as `sub(numtype)`, so the valtype
        // judgement is `(C, sub I32)`.
        let tyvar = |name: &str| covalence_spectec::ast::SpecTecTyp::Var {
            x: name.to_string(),
            as1: vec![],
        };
        let valtype_judgement = SpecTecExp::Tup {
            es: vec![
                ctx.clone(),
                SpecTecExp::Sub {
                    t1: tyvar("numtype"),
                    t2: tyvar("valtype"),
                    e1: Box::new(i32.clone()),
                },
            ],
        };
        assert_eq!(
            valid.concl(),
            &env.derivable("Valtype_ok", &valtype_judgement).unwrap(),
            "the composed derivation concludes Derivable_Valtype_ok of the judgement"
        );

        // The premise genuinely feeds the conclusion: with NO premise
        // derivation the rule's `Numtype_ok` antecedent stays undischarged, so
        // the result is a strictly weaker conditional, NOT the Valtype_ok
        // judgement above.
        let undischarged = env.derive_exprs(valtype_num, &[ctx, i32], vec![]).unwrap();
        assert_ne!(
            undischarged.concl(),
            valid.concl(),
            "without the premise the conclusion is not the Valtype_ok judgement"
        );
    }

    /// **Basic WASM semantics: instruction typing.** `Instr_ok` is the
    /// instruction validation relation (`C ⊢ instr : t₁* → t₂*` — the core of
    /// WASM's type system). Several rules are premise-free; we derive real
    /// instruction typings through the combined spec env, kernel-checked and
    /// hypothesis-free:
    ///
    /// - `nop`:   `C ⊢ NOP : [] → []`
    /// - `const`: `C ⊢ (CONST I32 c) : [] → [I32]`   (value push)
    /// - `binop`: `C ⊢ (BINOP I32 op) : [I32 I32] → [I32]`  (arithmetic)
    #[test]
    fn wasm_instr_ok_typing() {
        let defs = wasm_spec();
        let env = RelationEnv::spec(&defs);

        // nop : [] → []  (metavars [C]).
        let nop = env
            .rule_index(Some("Instr_ok"), "nop")
            .expect("Instr_ok/nop");
        let thm = env.derive_exprs(nop, &[leaf("C")], vec![]).unwrap();
        assert!(
            thm.hyps().is_empty(),
            "instruction typing is hypothesis-free"
        );

        // const : [] → [nt]  (metavars [C, nt, c_nt]).
        let konst = env
            .rule_index(Some("Instr_ok"), "const")
            .expect("Instr_ok/const");
        let thm = env
            .derive_exprs(konst, &[leaf("C"), leaf("I32"), leaf("ZERO")], vec![])
            .unwrap();
        assert!(thm.hyps().is_empty());

        // binop : [nt nt] → [nt]  (metavars [C, nt, binop_nt]).
        let binop = env
            .rule_index(Some("Instr_ok"), "binop")
            .expect("Instr_ok/binop");
        let thm = env
            .derive_exprs(binop, &[leaf("C"), leaf("I32"), leaf("ADD")], vec![])
            .unwrap();
        assert!(thm.hyps().is_empty());
    }

    /// **Compositional instruction typing.** `Instr_ok/drop` (`C ⊢ DROP : [t] →
    /// []`) has the inductive premise `Valtype_ok(C, t)`. We build the value-type
    /// validity for `t := num I32` (itself `Valtype_ok/num` discharging
    /// `Numtype_ok`) and feed it into `drop` — a three-relation typing
    /// derivation, kernel-checked and hypothesis-free.
    #[test]
    fn wasm_instr_ok_drop_compositional() {
        let defs = wasm_spec();
        let env = RelationEnv::spec(&defs);
        let ctx = leaf("C");
        let i32 = leaf("I32");

        // Numtype_ok(C, I32)  →  Valtype_ok/num(C, num I32).
        let numtype_ok = env.rule_index(Some("Numtype_ok"), "").unwrap();
        let valtype_num = env.rule_index(Some("Valtype_ok"), "num").unwrap();
        let base = env
            .derive_exprs(numtype_ok, &[ctx.clone(), i32.clone()], vec![])
            .unwrap();
        let vt = env
            .derive_exprs(valtype_num, &[ctx.clone(), i32.clone()], vec![base])
            .unwrap();

        // drop (metavars [C, t]) discharging Valtype_ok(C, t) with t := num I32.
        let drop = env
            .rule_index(Some("Instr_ok"), "drop")
            .expect("Instr_ok/drop");
        // The valtype coercion `num I32` as `t`.
        let t = SpecTecExp::Sub {
            t1: covalence_spectec::ast::SpecTecTyp::Var {
                x: "numtype".into(),
                as1: vec![],
            },
            t2: covalence_spectec::ast::SpecTecTyp::Var {
                x: "valtype".into(),
                as1: vec![],
            },
            e1: Box::new(i32),
        };
        let thm = env.derive_exprs(drop, &[ctx, t], vec![vt]).unwrap();
        assert!(
            thm.hyps().is_empty(),
            "compositional typing is hypothesis-free"
        );
    }

    /// The whole-spec entry point lowers many relations and reports the rest.
    #[test]
    fn wasm_spec_env_lowers_relations() {
        let defs = wasm_spec();
        let env = RelationEnv::spec(&defs);
        assert!(env.n_clauses() >= 200, "spec lowers many rules");
        assert_eq!(env.rules().len(), env.n_clauses());
        // Num_ok's rule is among the lowered clauses, reachable by name.
        assert!(env.rule_index(Some("Num_ok"), "").is_some());
    }

    /// A grammar and a relation are both driven through the one `Fragment`
    /// trait — the unification the layered-API directive asks for.
    #[test]
    fn grammar_and_relation_share_the_fragment_trait() {
        use super::super::Fragment;
        let defs = wasm_spec();
        let rel = RelationEnv::relation(find_relation(&defs, "Num_ok").unwrap()).unwrap();
        fn kind_of(f: &dyn Fragment) -> &'static str {
            f.judgement_kind()
        }
        assert_eq!(kind_of(&rel), "Derivable_R");
        // GrammarEnv also impls Fragment (see spectec/mod.rs) — checked by the
        // grammar tests; here we confirm the relation side is trait-object-safe.
    }
}
