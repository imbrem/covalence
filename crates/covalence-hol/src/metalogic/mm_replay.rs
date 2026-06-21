//! **Metamath-Prop → HOL replay** — the *construct, don't trust* bridge into
//! **pure derivability over the encoded syntax** (`docs/metatheory.md`,
//! `docs/theories-models-and-logics.md §5.6`).
//!
//! Given a **verified** Metamath proof in a propositional-calculus database
//! (set.mm's `ax-1` / `ax-2` / `ax-mp` fragment), [`replay_prop`] walks the
//! proof and builds the kernel theorem `⊢ Derivable_Prop ⌜S⌝` **step by step**,
//! re-deriving every step through the kernel. The Metamath proof is **untrusted**
//! — [`crate::metamath::verify`]'s say-so is *not* trusted for the HOL theorem;
//! the kernel re-checks each rule:
//!
//! | Metamath step             | HOL re-derivation                                |
//! |---------------------------|--------------------------------------------------|
//! | syntax former `wi`        | [`init::prop::p_imp`] (a term-building step)      |
//! | axiom instance `ax-1`     | [`init::prop::derive_axiom`]`(1, …)`             |
//! | axiom instance `ax-2`     | [`init::prop::derive_axiom`]`(2, …)`             |
//! | modus ponens `ax-mp`      | [`init::prop::derive_mp`] + [`Thm::imp_elim`]    |
//! | essential hypothesis `$e` | [`Thm::assume`]`(Derivable_Prop ⌜hyp⌝)`          |
//!
//! ## Proof irrelevance: we land in *derivability*, never *denotation*
//!
//! This is the crucial difference from the PA replay
//! ([`crate::peano::mm_replay`]), which lands `⊢ ⟦S⟧` — the standard-model
//! *denotation* of the conclusion (a fact about `nat`/`bool`). Here we land
//! `⊢ Derivable_Prop ⌜S⌝` — *pure derivability over the encoded syntax*:
//!
//! - **No denotation.** `⌜S⌝` is reified data (an `init::prop` Church fold);
//!   `Derivable_Prop ⌜S⌝` says "`S` has a derivation in the Hilbert system",
//!   nothing about what `S` *means*. There is no `⟦·⟧`, no valuation `v`, no
//!   appeal to the standard model.
//! - **No observer / no oracle.** Every step is an ordinary kernel rule; the
//!   returned `Thm` is `has_no_obs()`.
//!
//! Because we never denote, the bridge is *proof-irrelevant*: it certifies the
//! **existence** of a derivation (the §5.6 primitive `Derivable_A(S)`) by
//! reconstructing one in the kernel's reified Hilbert system, without ever
//! caring what `S` asserts. The Metamath object is a witness; the kernel theorem
//! re-establishes the witnessed fact from scratch.
//!
//! ## The encoding `⌜·⌝`
//!
//! A propositional wff in this database is built from `(`, `)`, `->`, and the
//! variables `ph`/`ps`/`ch`. [`parse_wff`] is a recursive-descent parser over the
//! flat token body: a single variable token → [`init::prop::p_var_lit`] at a
//! **stable** name→index (`ph`↦0, `ps`↦1, `ch`↦2, …, via [`VarIndex`]); a
//! parenthesised `( A -> B )` → [`init::prop::p_imp`]. The database's `ax-1` /
//! `ax-2` schemas match set.mm's exactly, so [`init::prop::derive_axiom`]'s
//! schemas 1/2 are their kernel images byte-for-byte.

use std::collections::HashMap;

use covalence_core::{Error, Result, Term, Thm};

use crate::init::prop;
use crate::metamath::expr::{body_of, typecode_of};
use crate::metamath::{Assertion, Database, Expr, Proof, Statement};

// ============================================================================
// Errors
// ============================================================================

fn replay_err(msg: impl Into<String>) -> Error {
    Error::ConnectiveRule(format!("mm-prop-replay: {}", msg.into()))
}

// ============================================================================
// Stable variable indexing (name → `init::prop` var index)
// ============================================================================

/// A stable assignment of propositional-variable names to `init::prop` var
/// indices, so the same Metamath variable always encodes to the same
/// `enc(var k)` (`ph`↦0, `ps`↦1, `ch`↦2, … in first-seen order). Mirrors the
/// `FreeVars` map in [`crate::peano::mm_replay`].
#[derive(Debug, Default, Clone)]
pub struct VarIndex {
    map: HashMap<String, u32>,
    next: u32,
}

impl VarIndex {
    pub fn new() -> Self {
        Self::default()
    }

    fn index(&mut self, name: &str) -> u32 {
        if let Some(k) = self.map.get(name) {
            return *k;
        }
        let k = self.next;
        self.next += 1;
        self.map.insert(name.to_string(), k);
        k
    }
}

// ============================================================================
// Metamath flat wff → `init::prop` encoding `⌜·⌝`
// ============================================================================

/// Parse the body of a `|-` statement (the tokens after the `|-` typecode) into
/// an encoded `init::prop` formula `⌜S⌝`.
pub fn parse_prov(e: &Expr, vars: &mut VarIndex) -> Result<Term> {
    if typecode_of(e) != Some("|-") {
        return Err(replay_err("expected a `|-` statement"));
    }
    parse_body(e, vars)
}

/// Parse the body of a `wff` statement (the tokens after the `wff` typecode)
/// into an encoded `init::prop` formula `⌜S⌝`.
pub fn parse_wff(e: &Expr, vars: &mut VarIndex) -> Result<Term> {
    if typecode_of(e) != Some("wff") {
        return Err(replay_err("expected a `wff` statement"));
    }
    parse_body(e, vars)
}

/// Parse the body tokens (everything after the typecode) of `e` as a single
/// complete wff.
fn parse_body(e: &Expr, vars: &mut VarIndex) -> Result<Term> {
    let body = body_of(e).ok_or_else(|| replay_err("malformed statement"))?;
    let syms: Vec<&str> = body.iter().map(|s| s.as_str()).collect();
    let (term, rest) = parse_one(&syms, vars)?;
    if !rest.is_empty() {
        return Err(replay_err("trailing symbols after wff"));
    }
    Ok(term)
}

/// Parse one wff off the front of `syms`, returning the encoded term and the
/// remaining symbols. Grammar (the PROP database): a wff is either a single
/// variable token → `enc(var k)`, or `( WFF -> WFF )` → `enc(A ⟹ B)`.
fn parse_one<'a>(syms: &'a [&'a str], vars: &mut VarIndex) -> Result<(Term, &'a [&'a str])> {
    let (head, rest) = syms
        .split_first()
        .ok_or_else(|| replay_err("unexpected end of wff"))?;
    match *head {
        "(" => {
            let (a, rest2) = parse_one(rest, vars)?;
            let rest3 = expect(rest2, "->")?;
            let (b, rest4) = parse_one(rest3, vars)?;
            let rest5 = expect(rest4, ")")?;
            Ok((prop::p_imp(a, b), rest5))
        }
        // Any other lone token is a propositional variable.
        ")" | "->" => Err(replay_err(format!("unexpected token `{head}`"))),
        var => Ok((prop::p_var_lit(vars.index(var)), rest)),
    }
}

fn expect<'a>(syms: &'a [&'a str], tok: &str) -> Result<&'a [&'a str]> {
    let (head, rest) = syms
        .split_first()
        .ok_or_else(|| replay_err(format!("expected `{tok}`, found end")))?;
    if *head != tok {
        return Err(replay_err(format!("expected `{tok}`, found `{head}`")));
    }
    Ok(rest)
}

// ============================================================================
// The replay stack
// ============================================================================

/// One slot on the replay stack, mirroring a pushed Metamath expression.
#[derive(Clone)]
enum Slot {
    /// A `wff` expression: only its encoded `init::prop` term matters.
    Wff(Term),
    /// A `|-` statement: the encoded formula plus the genuine kernel theorem
    /// `Γ ⊢ Derivable_Prop ⌜form⌝`.
    Proved { form: Term, thm: Thm },
}

// ============================================================================
// The replay
// ============================================================================

/// **Replay a verified Metamath propositional-calculus proof, re-deriving
/// `⊢ Derivable_Prop ⌜S⌝` in the kernel.**
///
/// `assertion` must be a `$p` theorem of a PROP database whose proof
/// [`crate::metamath::verify`] *accepts* (the caller verifies it; the replay
/// re-derives the HOL theorem independently). Returns a genuine kernel theorem
/// whose conclusion is `Derivable_Prop ⌜S⌝` for the assertion's conclusion `S`;
/// any **essential hypotheses** of the assertion appear as the theorem's
/// hypotheses `Derivable_Prop ⌜hyp⌝ ⊢ Derivable_Prop ⌜S⌝`.
pub fn replay_prop(db: &Database, assertion: &Assertion) -> Result<Thm> {
    let labels = match assertion.proof.as_ref() {
        Some(Proof::Normal(labels)) => labels,
        Some(Proof::Compressed { .. }) => {
            return Err(replay_err(
                "compressed-proof replay is not supported (decompress to a normal proof first)",
            ));
        }
        None => return Err(replay_err("assertion has no proof to replay")),
    };

    let mut vars = VarIndex::new();
    let mut stack: Vec<Slot> = Vec::new();

    for label in labels {
        let stmt = db
            .statement_by_label(label)
            .ok_or_else(|| replay_err(format!("unknown proof label `{label}`")))?;
        match stmt {
            Statement::Float(f) => {
                // `$f wff <var>` — push the encoded variable wff.
                stack.push(Slot::Wff(prop::p_var_lit(vars.index(&f.var))));
            }
            Statement::Essential(h) => {
                // `$e |- <hyp>` — a hypothesis. Its derivability is *assumed*;
                // it appears as a hypothesis of the final theorem.
                let form = parse_prov(&h.expr, &mut vars)?;
                let thm = Thm::assume(prop::derivable(&form)?)?;
                stack.push(Slot::Proved { form, thm });
            }
            Statement::Assert(target) => {
                apply(target, label, &mut stack)?;
            }
            _ => return Err(replay_err(format!("label `{label}` is not applicable"))),
        }
    }

    match stack.as_slice() {
        [Slot::Proved { form, thm }] => {
            // Sanity: the re-derived theorem must be the derivability of the
            // claimed conclusion's encoding. Re-parse the conclusion under the
            // *same* `vars` map the replay built, so variable indices agree
            // regardless of whether the conclusion mentions variables in a
            // different first-seen order than the proof did.
            let claimed = parse_prov(&assertion.conclusion, &mut vars)?;
            if form != &claimed {
                return Err(replay_err(format!(
                    "replayed formula does not match the claimed conclusion `{}`",
                    crate::metamath::expr::render(&assertion.conclusion),
                )));
            }
            let want = prop::derivable(&claimed)?;
            if thm.concl() != &want {
                return Err(replay_err(format!(
                    "replayed conclusion does not match the claimed `{}`",
                    crate::metamath::expr::render(&assertion.conclusion),
                )));
            }
            Ok(thm.clone())
        }
        [_] => Err(replay_err("proof ended on a non-`|-` slot")),
        other => Err(replay_err(format!(
            "proof did not reduce to a single result (stack depth {})",
            other.len()
        ))),
    }
}

/// Apply a target assertion `label` during replay: pop its mandatory operands
/// (floats first, then essentials, in frame order), dispatch on the label, push
/// the result slot.
fn apply(target: &Assertion, label: &str, stack: &mut Vec<Slot>) -> Result<()> {
    let n_floats = target.frame.floats.len();
    let n = target.frame.mandatory_count();
    if stack.len() < n {
        return Err(replay_err(format!(
            "stack underflow applying `{label}` (need {n}, have {})",
            stack.len()
        )));
    }
    let args: Vec<Slot> = stack.split_off(stack.len() - n);
    // `args[0..n_floats]` are the float (wff) operands; `args[n_floats..]` are
    // the essential (proved) operands, both in frame order.

    let result = if typecode_of(&target.conclusion) == Some("wff") {
        // --- syntax former: builds a wff, no proof ---
        syntax_former(target, label, &args)?
    } else if target.frame.essentials.is_empty() {
        // --- axiom: a `|-` assertion with no essential premises ---
        axiom_instance(label, &args, n_floats)?
    } else {
        // --- inference rule: a `|-` assertion with essential premises ---
        rule_instance(label, &args, n_floats)?
    };
    stack.push(result);
    Ok(())
}

/// A wff-formation step. The only former in the PROP database is `wi`
/// (`wff ( ph -> ps )`): pop its two wff operands and build `enc(a ⟹ b)`.
fn syntax_former(target: &Assertion, label: &str, args: &[Slot]) -> Result<Slot> {
    // Dispatch on the conclusion shape `( ph -> ps )` (equivalently label `wi`).
    if label == "wi" || former_is_imp(target) {
        let [a, b] = two_wff(args, label)?;
        Ok(Slot::Wff(prop::p_imp(a, b)))
    } else {
        Err(replay_err(format!("unknown syntax former `{label}`")))
    }
}

/// Whether `target`'s conclusion has the `->`-former shape `wff ( _ -> _ )`.
fn former_is_imp(target: &Assertion) -> bool {
    match body_of(&target.conclusion) {
        Some(body) => {
            let syms: Vec<&str> = body.iter().map(|s| s.as_str()).collect();
            matches!(syms.as_slice(), [first, .., last] if *first == "(" && *last == ")")
                && body.iter().any(|s| s.as_str() == "->")
        }
        None => false,
    }
}

/// An axiom instance (`ax-1` / `ax-2`). The float operands are the encoded
/// sub-formulas; re-derive `⊢ Derivable_Prop ⌜axiom_i …⌝` via
/// [`init::prop::derive_axiom`].
fn axiom_instance(label: &str, args: &[Slot], n_floats: usize) -> Result<Slot> {
    let floats = wff_floats(args, n_floats, label)?;
    match label {
        "ax-1" => {
            // ax-1 : ⊢ ( ph -> ( ps -> ph ) ).  Floats (ph, ps).
            let [a, b] = expect_floats::<2>(&floats, label)?;
            // axiom_schema 1 is `a ⟹ (b ⟹ a)`; `c` is unused, pass `a`.
            let thm = prop::derive_axiom(1, &a, &b, &a)?;
            let form = prop::p_imp(a.clone(), prop::p_imp(b, a));
            Ok(Slot::Proved { form, thm })
        }
        "ax-2" => {
            // ax-2 : ⊢ ( (ph->(ps->ch)) -> ((ph->ps)->(ph->ch)) ).  Floats (ph, ps, ch).
            let [a, b, c] = expect_floats::<3>(&floats, label)?;
            let thm = prop::derive_axiom(2, &a, &b, &c)?;
            let form = prop::p_imp(
                prop::p_imp(a.clone(), prop::p_imp(b.clone(), c.clone())),
                prop::p_imp(prop::p_imp(a.clone(), b), prop::p_imp(a, c)),
            );
            Ok(Slot::Proved { form, thm })
        }
        other => Err(replay_err(format!("no replay rule for axiom `{other}`"))),
    }
}

/// An inference-rule instance (`ax-mp`). Float operands give the substitution;
/// essential operands are the (proved) premises.
fn rule_instance(label: &str, args: &[Slot], n_floats: usize) -> Result<Slot> {
    match label {
        "ax-mp" => {
            // ax-mp : floats (ph := a, ps := b); essentials maj = ⊢ ph, min = ⊢ ( ph -> ps ).
            let floats = wff_floats(args, n_floats, label)?;
            let [a, b] = expect_floats::<2>(&floats, label)?;
            let [maj, min] = two_proved(&args[n_floats..], label)?;
            // derive_mp(a,b) : ⊢ Der ⌜a⌝ ⟹ Der ⌜a⟹b⌝ ⟹ Der ⌜b⌝.
            let thm = prop::derive_mp(&a, &b)?
                .imp_elim(maj.thm)? // ⊢ Der ⌜a⟹b⌝ ⟹ Der ⌜b⌝   (carrying maj's hyps)
                .imp_elim(min.thm)?; // ⊢ Der ⌜b⌝                  (carrying min's hyps)
            Ok(Slot::Proved { form: b, thm })
        }
        other => Err(replay_err(format!("no replay rule for `{other}`"))),
    }
}

// ============================================================================
// Operand helpers
// ============================================================================

/// Collect the `n_floats` leading wff operands' encoded terms (in frame order).
fn wff_floats(args: &[Slot], n_floats: usize, label: &str) -> Result<Vec<Term>> {
    args.get(..n_floats)
        .ok_or_else(|| replay_err(format!("`{label}`: not enough float operands")))?
        .iter()
        .enumerate()
        .map(|(i, s)| match s {
            Slot::Wff(t) => Ok(t.clone()),
            Slot::Proved { .. } => {
                Err(replay_err(format!("`{label}`: operand {i} is not a wff")))
            }
        })
        .collect()
}

/// Exactly `N` float operands, by value.
fn expect_floats<const N: usize>(floats: &[Term], label: &str) -> Result<[Term; N]> {
    <[Term; N]>::try_from(floats.to_vec())
        .map_err(|_| replay_err(format!("`{label}` expects {N} float operands, got {}", floats.len())))
}

/// Exactly two wff operands (a syntax former's args).
fn two_wff(args: &[Slot], label: &str) -> Result<[Term; 2]> {
    let floats = wff_floats(args, args.len(), label)?;
    expect_floats::<2>(&floats, label)
}

/// A borrowed-into-owned proved operand.
struct Proved {
    thm: Thm,
}

/// Exactly two proved operands, in order (the essential premises of a rule).
fn two_proved(args: &[Slot], label: &str) -> Result<[Proved; 2]> {
    let proved: Vec<Proved> = args
        .iter()
        .map(|s| match s {
            Slot::Proved { thm, .. } => Ok(Proved { thm: thm.clone() }),
            Slot::Wff(_) => Err(replay_err(format!("`{label}`: expected a `|-` premise"))),
        })
        .collect::<Result<_>>()?;
    <[Proved; 2]>::try_from(proved)
        .map_err(|v| replay_err(format!("`{label}` expects 2 `|-` premises, got {}", v.len())))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn prop_src() -> &'static str {
        "\
            $c ( ) -> wff |- $.
            $v ph ps ch $.
            wph $f wff ph $.
            wps $f wff ps $.
            wch $f wff ch $.
            wi $a wff ( ph -> ps ) $.
            ax-1 $a |- ( ph -> ( ps -> ph ) ) $.
            ax-2 $a |- ( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ch ) ) ) $.
            ${
              mp.maj $e |- ph $.
              mp.min $e |- ( ph -> ps ) $.
              ax-mp $a |- ps $.
            $}
        "
    }

    fn assert_genuine_obs_free(thm: &Thm) {
        assert!(thm.has_no_obs(), "replayed theorem must be oracle-free");
    }

    /// **`ax2i`** — a single `ax-2` instance (`ch := ph`), NO essentials. The
    /// replay re-derives a hypothesis-free, oracle-free kernel theorem whose
    /// conclusion is exactly `Derivable_Prop ⌜S⌝` for the claimed `S`.
    #[test]
    fn replay_ax2i() {
        let src = format!(
            "{}\n\
            ax2i $p |- ( ( ph -> ( ps -> ph ) ) -> ( ( ph -> ps ) -> ( ph -> ph ) ) ) $=\n\
              wph wps wph ax-2 $.\n",
            prop_src()
        );
        let db = crate::metamath::parse(&src).unwrap();
        // The engine accepts the proof (untrusted input).
        assert_eq!(crate::metamath::verify_all(&db).unwrap(), 1);

        let a = db.assertions().find(|a| a.label == "ax2i").unwrap();
        let thm = replay_prop(&db, a).unwrap();

        // Hypothesis-free (no essentials) and oracle-free.
        assert!(thm.hyps().is_empty(), "ax2i replay must be hypothesis-free");
        assert_genuine_obs_free(&thm);

        // Its conclusion is `Derivable_Prop ⌜S⌝` for the parsed conclusion `S`.
        let expected = parse_prov(&a.conclusion, &mut VarIndex::new()).unwrap();
        assert_eq!(thm.concl(), &prop::derivable(&expected).unwrap());
    }

    /// **`a1i`** — the derived rule with essential `a1i.1 $e |- ph`. The replay
    /// re-derives `Derivable_Prop ⌜( ps -> ph )⌝` carrying exactly one
    /// hypothesis, `Derivable_Prop ⌜ph⌝`.
    #[test]
    fn replay_a1i() {
        let src = format!(
            "{}\n\
            ${{\n\
              a1i.1 $e |- ph $.\n\
              a1i $p |- ( ps -> ph ) $=\n\
                wph  wps wph wi  a1i.1  wph wps ax-1  ax-mp $.\n\
            $}}\n",
            prop_src()
        );
        let db = crate::metamath::parse(&src).unwrap();
        assert_eq!(crate::metamath::verify_all(&db).unwrap(), 1);

        let a = db.assertions().find(|a| a.label == "a1i").unwrap();
        let thm = replay_prop(&db, a).unwrap();

        assert_genuine_obs_free(&thm);

        // The replay's `VarIndex` is driven by *proof* order: the proof opens
        // `wph wps …`, so `ph`↦0, `ps`↦1 in the returned theorem (regardless of
        // the conclusion's own first-seen order). The conclusion is therefore
        // `Derivable_Prop ⌜( ps -> ph )⌝ = Der ⌜p_imp(var 1, var 0)⌝`.
        let ph = prop::p_var_lit(0);
        let ps = prop::p_var_lit(1);
        let concl_wff = prop::p_imp(ps, ph.clone()); // ( ps -> ph )
        assert_eq!(thm.concl(), &prop::derivable(&concl_wff).unwrap());

        // Exactly one hypothesis: `Derivable_Prop ⌜ph⌝`, sharing the SAME `ph`
        // encoding as the conclusion.
        let hyps: Vec<&Term> = thm.hyps().iter().collect();
        assert_eq!(hyps.len(), 1, "a1i carries exactly one hypothesis");
        assert_eq!(hyps[0], &prop::derivable(&ph).unwrap());
    }
}
