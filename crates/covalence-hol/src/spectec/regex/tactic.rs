//! The **matching tactic**: search for a `Matches ⌜r⌝ w` derivation and
//! assemble it from [`crate::init::regex`]'s seven rule constructors.
//!
//! Two entry points:
//!
//! - [`prove_matches`] takes a regex and a **concrete** bytestring and returns
//!   `⊢ Matches ⌜r⌝ w` (or `None` if the bytes are not in the language). The
//!   word `w` is built rule-shaped: byte literals, `cat`, single-byte `cons`,
//!   and `nil`.
//! - [`prove_word`] takes a [`Word`] — an expression of byte literals,
//!   concatenation, and **variables** carrying a "parses as this category"
//!   assumption — and returns `{Matches ⌜cᵢ⌝ Xᵢ}ᵢ ⊢ Matches ⌜r⌝ w`. A variable
//!   token is opaque: it is consumed only by matching the regex sub-goal that
//!   equals its category, discharged against the assumption `Matches ⌜cᵢ⌝ Xᵢ`.
//!   This is the seed for grammar *composition* — "a section is a header then a
//!   payload that parses as `Vec(func)`" — and for sharing one derivation
//!   across Metamath / WASM / S-expression grammars.
//!
//! The search is plain backtracking over how `seq`/`star`/`alt` split the
//! input. It is untrusted: every step is re-checked by the kernel as the `Thm`
//! is built, so a wrong split simply fails to typecheck and the search moves
//! on. Worst-case it is exponential in the input length — fine for the small
//! tokens this bootstraps on; a derivative/memoised matcher is a later
//! optimisation (`SKELETONS.md`).

use covalence_core::{Result, Term, Thm, Type};
use covalence_grammar::regex::Regex;

use super::{Core, core_to_term, desugar};
use crate::init::ext::TermExt;
use crate::init::regex as ir;

// ============================================================================
// Word terms (the rule-shaped `list u8` the derivations talk about).
// ============================================================================

fn u8ty() -> Type {
    ir::u8_alphabet()
}

fn word_ty() -> Type {
    crate::init::list::list(u8ty())
}

fn nil_w() -> Term {
    crate::init::list::nil(u8ty())
}

fn cons_w(b: u8, rest: Term) -> Result<Term> {
    crate::init::list::cons(u8ty())
        .apply(Term::u8_lit(b))?
        .apply(rest)
}

fn singleton_w(b: u8) -> Result<Term> {
    cons_w(b, nil_w())
}

fn cat_w(w1: Term, w2: Term) -> Result<Term> {
    crate::init::list::list_cat(u8ty()).apply(w1)?.apply(w2)
}

// ============================================================================
// The atom sequence the matcher runs over.
// ============================================================================

/// A variable occurring in a [`Word`]: a free `list u8` term `X` assumed to
/// parse as `category`.
struct VarInfo {
    name: String,
    term: Term,
    category: Core,
}

/// One position of the flattened input: a concrete byte, or a variable token
/// (index into the var table).
#[derive(Clone, Copy)]
enum Atom {
    Byte(u8),
    Var(usize),
}

// ============================================================================
// The deriver — `Matches ⌜c⌝ w` over a slice of atoms.
// ============================================================================

/// Try to build `⊢ Matches ⌜c⌝ w` (possibly under variable assumptions) where
/// `w` consumes exactly `atoms`. Returns the theorem and its word term, or
/// `None` if `atoms ∉ L(c)`. `Ok(None)` is "no derivation"; `Err` is a genuine
/// kernel failure.
fn derive(c: &Core, atoms: &[Atom], vars: &[VarInfo]) -> Result<Option<(Thm, Term)>> {
    let a = u8ty();

    // Variable rule: a lone variable token is consumed only by the regex goal
    // that *is* its category — discharged against `Matches ⌜category⌝ X`.
    if let [Atom::Var(i)] = atoms {
        let vi = &vars[*i];
        if *c == vi.category {
            let prop = ir::matches(&a, &core_to_term(c), &vi.term)?;
            return Ok(Some((Thm::assume(prop)?, vi.term.clone())));
        }
        // Otherwise fall through: a structural goal (alt/seq/star) may still
        // recurse and bottom out at this rule with a matching sub-core.
    }

    match c {
        Core::Empty => Ok(None),

        Core::Eps => {
            if atoms.is_empty() {
                Ok(Some((ir::match_eps(&a)?, nil_w())))
            } else {
                Ok(None)
            }
        }

        Core::Lit(b) => match atoms {
            [Atom::Byte(x)] if x == b => {
                let th = ir::match_lit(&a)?.all_elim(Term::u8_lit(*b))?;
                Ok(Some((th, singleton_w(*b)?)))
            }
            _ => Ok(None),
        },

        Core::Alt(x, y) => {
            let xt = core_to_term(x);
            let yt = core_to_term(y);
            if let Some((thx, w)) = derive(x, atoms, vars)? {
                let th = ir::match_alt_l(&a, &xt, &yt, &w)?.imp_elim(thx)?;
                return Ok(Some((th, w)));
            }
            if let Some((thy, w)) = derive(y, atoms, vars)? {
                let th = ir::match_alt_r(&a, &xt, &yt, &w)?.imp_elim(thy)?;
                return Ok(Some((th, w)));
            }
            Ok(None)
        }

        Core::Seq(x, y) => {
            let xt = core_to_term(x);
            let yt = core_to_term(y);
            for k in 0..=atoms.len() {
                let (left, right) = atoms.split_at(k);
                if let Some((thx, w1)) = derive(x, left, vars)? {
                    if let Some((thy, w2)) = derive(y, right, vars)? {
                        let th = ir::match_seq(&a, &xt, &yt, &w1, &w2)?
                            .imp_elim(thx)?
                            .imp_elim(thy)?;
                        return Ok(Some((th, cat_w(w1, w2)?)));
                    }
                }
            }
            Ok(None)
        }

        Core::Star(x) => derive_star(x, atoms, vars),
    }
}

/// `Matches ⌜star x⌝ w` — empty word via `star-nil`, otherwise peel a
/// non-empty `x`-prefix and recurse with `star-step`.
fn derive_star(x: &Core, atoms: &[Atom], vars: &[VarInfo]) -> Result<Option<(Thm, Term)>> {
    let a = u8ty();
    let xt = core_to_term(x);

    if atoms.is_empty() {
        return Ok(Some((ir::match_star_nil(&a, &xt)?, nil_w())));
    }

    let starx = Core::Star(Box::new(x.clone()));
    // Non-empty prefix (k >= 1) keeps the recursion strictly decreasing and
    // avoids looping on a nullable `x`.
    for k in 1..=atoms.len() {
        let (left, right) = atoms.split_at(k);
        if let Some((thx, w1)) = derive(x, left, vars)? {
            if let Some((thstar, w2)) = derive(&starx, right, vars)? {
                let th = ir::match_star_step(&a, &xt, &w1, &w2)?
                    .imp_elim(thx)?
                    .imp_elim(thstar)?;
                return Ok(Some((th, cat_w(w1, w2)?)));
            }
        }
    }
    Ok(None)
}

// ============================================================================
// Public tactic surface.
// ============================================================================

/// Prove `⊢ Matches ⌜r⌝ w` for the concrete bytestring `bytes`, or `None` if
/// the bytes are not in `L(r)`. `w` is rule-shaped (byte literals + `cat` +
/// single-byte `cons` + `nil`); read it off `thm.concl()` if you need it.
pub fn prove_matches(r: &Regex<u8>, bytes: &[u8]) -> Result<Option<Thm>> {
    let core = desugar(r);
    let atoms: Vec<Atom> = bytes.iter().map(|&b| Atom::Byte(b)).collect();
    Ok(derive(&core, &atoms, &[])?.map(|(thm, _)| thm))
}

/// Prove that `bytes` is **in the language** the grammar denotes:
/// `⊢ mem w ⟦⌜r⌝⟧`. Chains [`prove_matches`] through regex *soundness*
/// ([`crate::init::regex::soundness_at`]).
pub fn prove_member(r: &Regex<u8>, bytes: &[u8]) -> Result<Option<Thm>> {
    let a = u8ty();
    let core = desugar(r);
    let rterm = core_to_term(&core);
    let atoms: Vec<Atom> = bytes.iter().map(|&b| Atom::Byte(b)).collect();
    let Some((der, w)) = derive(&core, &atoms, &[])? else {
        return Ok(None);
    };
    // Soundness lives at the denotation instance `'r := set (list u8)`; the
    // `Matches`/rule machinery is schematic in `'r`, so pin the derivation
    // there before discharging it into soundness.
    let lang_ty = ir::denote(&a, rterm.clone())?.type_of()?;
    let der = der.inst_tfree("r", lang_ty)?;
    let snd = ir::soundness_at(&a, &rterm, &w)?; // ⊢ Matches r w ⟹ mem w ⟦r⟧
    Ok(Some(snd.imp_elim(der)?))
}

/// A bytestring **expression** the matcher can prove against — byte literals,
/// concatenation, and variables carrying a "parses as this category"
/// assumption. The general (bonus) input shape: with no [`Word::Var`] it is an
/// ordinary concrete bytestring, equivalent to [`prove_matches`].
pub enum Word {
    /// The empty word.
    Nil,
    /// A single byte.
    Byte(u8),
    /// A literal block of bytes.
    Bytes(Vec<u8>),
    /// Concatenation `w₁ w₂`.
    Cat(Box<Word>, Box<Word>),
    /// A variable `X` assumed to parse as `category` (its occurrences share one
    /// free `list u8` variable, keyed by `name`).
    Var { name: String, category: Regex<u8> },
}

impl Word {
    /// `w₁ w₂`.
    pub fn cat(w1: Word, w2: Word) -> Word {
        Word::Cat(Box::new(w1), Box::new(w2))
    }
}

fn flatten(w: &Word, atoms: &mut Vec<Atom>, vars: &mut Vec<VarInfo>) {
    match w {
        Word::Nil => {}
        Word::Byte(b) => atoms.push(Atom::Byte(*b)),
        Word::Bytes(bs) => atoms.extend(bs.iter().map(|&b| Atom::Byte(b))),
        Word::Cat(l, r) => {
            flatten(l, atoms, vars);
            flatten(r, atoms, vars);
        }
        Word::Var { name, category } => {
            let idx = match vars.iter().position(|v| &v.name == name) {
                Some(i) => i,
                None => {
                    vars.push(VarInfo {
                        name: name.clone(),
                        term: Term::free(name, word_ty()),
                        category: desugar(category),
                    });
                    vars.len() - 1
                }
            };
            atoms.push(Atom::Var(idx));
        }
    }
}

/// Prove `{Matches ⌜cᵢ⌝ Xᵢ}ᵢ ⊢ Matches ⌜r⌝ w` for a word **expression** that may
/// contain variables, or `None` if no derivation exists. Each distinct
/// [`Word::Var`] contributes one `Matches ⌜category⌝ X` hypothesis.
pub fn prove_word(r: &Regex<u8>, w: &Word) -> Result<Option<Thm>> {
    let core = desugar(r);
    let mut atoms = Vec::new();
    let mut vars = Vec::new();
    flatten(w, &mut atoms, &mut vars);
    Ok(derive(&core, &atoms, &vars)?.map(|(thm, _)| thm))
}

#[cfg(test)]
mod tests {
    use super::*;
    use covalence_grammar::regex::parse_regex_u8;

    fn re(src: &str) -> Regex<u8> {
        parse_regex_u8(src).unwrap()
    }

    fn assert_genuine(thm: &Thm) {
        assert!(thm.has_no_obs(), "expected an oracle-free theorem");
    }

    #[test]
    fn matches_literal_string() {
        // `abc` matches the bytes "abc".
        let thm = prove_matches(&re("abc"), b"abc").unwrap().unwrap();
        assert!(thm.hyps().is_empty());
        assert_genuine(&thm);
        // ...and rejects "abd".
        assert!(prove_matches(&re("abc"), b"abd").unwrap().is_none());
        // ...and a prefix (must consume all input).
        assert!(prove_matches(&re("abc"), b"ab").unwrap().is_none());
    }

    #[test]
    fn matches_alternation_and_star() {
        // `(a|b)c*` against "bccc".
        let r = re("(?:a|b)c*");
        let thm = prove_matches(&r, b"bccc").unwrap().unwrap();
        assert_genuine(&thm);
        // empty star: "a".
        assert!(prove_matches(&r, b"a").unwrap().is_some());
        // "ac": one c.
        assert!(prove_matches(&r, b"ac").unwrap().is_some());
        // "cc": no leading a|b.
        assert!(prove_matches(&r, b"cc").unwrap().is_none());
    }

    #[test]
    fn matches_class_and_plus() {
        // one or more hex-ish bytes
        let r = re("[a-c]+");
        assert!(prove_matches(&r, b"abccba").unwrap().is_some());
        assert!(prove_matches(&r, b"abx").unwrap().is_none());
        assert!(prove_matches(&r, b"").unwrap().is_none()); // plus needs >= 1
    }

    #[test]
    fn matches_wasm_preamble() {
        // The real WASM magic + version, proved against the literal bytes.
        let r = covalence_spectec::grammar::simple::wasm_preamble();
        let bytes = [0x00, b'a', b's', b'm', 0x01, 0x00, 0x00, 0x00];
        let thm = prove_matches(&r, &bytes).unwrap().unwrap();
        assert!(thm.hyps().is_empty());
        assert_genuine(&thm);
        // A wrong version byte fails.
        let bad = [0x00, b'a', b's', b'm', 0x02, 0x00, 0x00, 0x00];
        assert!(prove_matches(&r, &bad).unwrap().is_none());
    }

    #[test]
    fn member_chains_soundness() {
        // `a|b` against "a" lands `⊢ mem [a] ⟦a|b⟧` — bytes are in the language.
        let thm = prove_member(&re("a|b"), b"a").unwrap().unwrap();
        assert!(thm.hyps().is_empty());
        assert_genuine(&thm);
    }

    #[test]
    fn word_with_no_vars_matches_like_bytes() {
        let w = Word::cat(Word::Bytes(b"ab".to_vec()), Word::Byte(b'c'));
        let thm = prove_word(&re("abc"), &w).unwrap().unwrap();
        assert!(thm.hyps().is_empty());
        assert_genuine(&thm);
    }

    #[test]
    fn word_with_variable_discharges_by_assumption() {
        // Goal regex: `0x00 X` where X parses as `[a-c]+`.
        // Word: byte 0x00 followed by variable X (category `[a-c]+`).
        let cat = re("[a-c]+");
        let r = Regex::concat([Regex::Lit(0x00u8), cat.clone()]);
        let w = Word::cat(
            Word::Byte(0x00),
            Word::Var {
                name: "X".into(),
                category: cat,
            },
        );
        let thm = prove_word(&r, &w).unwrap().unwrap();
        // Exactly one hypothesis: `Matches ⌜[a-c]+⌝ X`.
        assert_eq!(thm.hyps().len(), 1, "expected the parses-as assumption");
        assert_genuine(&thm);
    }

    #[test]
    fn word_variable_under_star() {
        // `(cat)*` against two variable tokens both of category `cat`.
        let cat = re("a|b");
        let r = Regex::Star(Box::new(cat.clone()));
        let w = Word::cat(
            Word::Var {
                name: "X".into(),
                category: cat.clone(),
            },
            Word::Var {
                name: "Y".into(),
                category: cat,
            },
        );
        let thm = prove_word(&r, &w).unwrap().unwrap();
        // Two distinct variables -> two assumptions.
        assert_eq!(thm.hyps().len(), 2);
        assert_genuine(&thm);
    }
}
