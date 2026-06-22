//! **Grammars → byte predicates, and a matching tactic** — the byte-parsing
//! analogue of the Metamath infrastructure ([`crate::metalogic`]).
//!
//! The north star is *verified* binary-format parsing: compile a grammar (a
//! SpecTec grammar, or any [`covalence_grammar::regex::Regex`]) into a HOL
//! predicate on `bytes`, and prove — inside the kernel — that a concrete
//! bytestring satisfies it. That is the seed for a verified WASM reader: WASM's
//! binary format is a grammar, and "these bytes are a well-formed module" is a
//! `Matches` derivation.
//!
//! # The pipeline
//!
//! ```text
//!   SpecTecSym ──sym_to_regex_u8──▶ Regex<u8> ──desugar──▶ Core ──┬─ core_to_term ─▶ ⌜r⌝ : regex u8
//!   (covalence-spectec)            (covalence-grammar)             │
//!                                                                  └─ derive ───────▶ ⊢ Matches ⌜r⌝ w
//! ```
//!
//! - [`Core`] is the six-constructor regex the reified HOL `regex u8` datatype
//!   ([`crate::init::regex`]) actually has (`empty`/`eps`/`lit`/`alt`/`seq`/
//!   `star`). [`desugar`] folds a full [`Regex<u8>`] down to it — character
//!   classes become alternations of byte literals, `+`/`?`/`{m,n}` become
//!   `seq`/`alt` combinations.
//! - [`compile`] emits the reified regex term `⌜r⌝ : regex u8`.
//! - [`predicate`] emits the *language* `⟦⌜r⌝⟧ : set (list u8)` — the byte
//!   predicate the grammar denotes (via [`crate::init::regex::denote`]).
//! - [`tactic::prove_matches`] is the tactic: given `r` and a bytestring, it
//!   backtracks over the seven matching rules to build `⊢ Matches ⌜r⌝ w`. The
//!   word `w` it produces is exactly an expression of byte literals,
//!   concatenation (`cat`), single-byte `cons`, and `nil` — the shape the
//!   matching rules compose. [`tactic::prove_member`] chains regex *soundness*
//!   to land `⊢ mem w ⟦⌜r⌝⟧`: the bytes are *in the language*.
//!
//! # Regex is the base case — the CFG stratum comes next
//!
//! A SpecTec grammar is **strictly more than a regex**: regular languages are
//! only its base case. SpecTec symbols include non-terminal *references*
//! ([`SpecTecSym::Var`]) — i.e. one grammar invoking another — which is exactly
//! the step from regular to **context-free**. The byte bridge here deliberately
//! covers only the regular fragment and returns a typed error on `Var`; the
//! reified target ([`crate::init::regex`]) is likewise a *regular*-language
//! object logic.
//!
//! The plan is to grow our **own primitive notion of CFG**, one stratum up,
//! the same way [`crate::init::regex`] is our own primitive notion of regular
//! expression: a reified grammar datatype with non-terminals, a `Derives`
//! judgement closed under the productions, and rule induction over derivation
//! trees (the same impredicative-encoding recipe [`crate::init::regex`] and
//! [`crate::init::prop`] already use). At that point a SpecTec `gram`
//! definition lowers to a set of productions over reified non-terminals, and a
//! `Var` reference becomes a non-terminal symbol rather than a bridge error.
//!
//! [`tactic::prove_word`] is the **first rung of that ladder**: a variable
//! token carrying a "parses as this category" assumption *is* a non-terminal
//! expansion, and discharging `Matches ⌜cᵢ⌝ Xᵢ` against an assumption is exactly
//! how a CFG derivation will compose sub-derivations. The regular matcher and
//! the (future) CFG deriver share that interface — see `SKELETONS.md`.
//!
//! # Trust
//!
//! Everything here is **untrusted driver code**: the backtracking matcher is a
//! search, and whatever it finds is re-checked by the kernel as it assembles
//! the `Thm` from [`crate::init::regex`]'s rule constructors. A buggy matcher
//! can only fail to find a derivation, never forge one — exactly the Metamath
//! "derive, don't trust" discipline.
//!
//! # SpecTec entry points
//!
//! [`compile_sym`] / [`prove_sym_matches`] take a [`SpecTecSym`] directly,
//! routing through `covalence-spectec`'s byte bridge. Grammar *references*
//! (`Var`) are outside the regular fragment and return a typed error — see
//! `SKELETONS.md`.

use covalence_core::{Result, Term, Type};
use covalence_grammar::regex::{Class, Regex};

use crate::init::regex as ir;

pub mod tactic;

pub use covalence_spectec::ast::SpecTecSym;

// ============================================================================
// Core — the six-constructor byte regex the reified HOL datatype mirrors.
// ============================================================================

/// A byte regex restricted to the six constructors the reified HOL `regex u8`
/// datatype ([`crate::init::regex`]) has. The full surface
/// [`Regex<u8>`] desugars into this via [`desugar`].
///
/// Keeping a distinct `Core` (rather than compiling `Regex<u8>` directly) means
/// the term compiler ([`core_to_term`]) and the matcher
/// ([`tactic`]) share *one* desugaring, so the regex term a derivation is about
/// is always exactly the one the matcher recursed over.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Core {
    /// `∅` — matches nothing.
    Empty,
    /// `ε` — matches only the empty word.
    Eps,
    /// A single byte literal.
    Lit(u8),
    /// Alternation `x | y`.
    Alt(Box<Core>, Box<Core>),
    /// Concatenation `x y`.
    Seq(Box<Core>, Box<Core>),
    /// Kleene star `x*`.
    Star(Box<Core>),
}

impl Core {
    fn alt(x: Core, y: Core) -> Core {
        Core::Alt(Box::new(x), Box::new(y))
    }
    fn seq(x: Core, y: Core) -> Core {
        Core::Seq(Box::new(x), Box::new(y))
    }
    fn star(x: Core) -> Core {
        Core::Star(Box::new(x))
    }

    /// Right-fold a list of cores into a binary [`Core::Seq`] chain, collapsing
    /// the empty list to `eps` and a singleton to itself.
    fn seq_all(items: impl DoubleEndedIterator<Item = Core>) -> Core {
        let mut items: Vec<Core> = items.collect();
        match items.len() {
            0 => Core::Eps,
            1 => items.pop().expect("len 1"),
            _ => {
                let last = items.pop().expect("len >= 2");
                items
                    .into_iter()
                    .rev()
                    .fold(last, |acc, x| Core::seq(x, acc))
            }
        }
    }

    /// Right-fold a list of cores into a binary [`Core::Alt`] chain, collapsing
    /// the empty list to `empty` and a singleton to itself.
    fn alt_all(items: impl DoubleEndedIterator<Item = Core>) -> Core {
        let mut items: Vec<Core> = items.collect();
        match items.len() {
            0 => Core::Empty,
            1 => items.pop().expect("len 1"),
            _ => {
                let last = items.pop().expect("len >= 2");
                items
                    .into_iter()
                    .rev()
                    .fold(last, |acc, x| Core::alt(x, acc))
            }
        }
    }
}

// ============================================================================
// Desugaring  Regex<u8> -> Core.
// ============================================================================

/// Desugar a full byte regex into the six-constructor [`Core`] form.
///
/// - character classes become a right-nested alternation of their member byte
///   literals (a negated class is complemented against `0x00..=0xFF` first; an
///   empty class becomes [`Core::Empty`]);
/// - `r+` becomes `r r*`, `r?` becomes `ε | r`;
/// - `r{m,m}` becomes `m` copies, `r{m,n}` becomes `m` copies then `n−m`
///   optionals, `r{m,}` becomes `m` copies then `r*`.
pub fn desugar(r: &Regex<u8>) -> Core {
    match r {
        Regex::Empty => Core::Empty,
        Regex::Eps => Core::Eps,
        Regex::Lit(b) => Core::Lit(*b),
        Regex::Class(c) => Core::alt_all(class_bytes(c).into_iter().map(Core::Lit)),
        Regex::Concat(items) => Core::seq_all(items.iter().map(desugar)),
        Regex::Alt(items) => Core::alt_all(items.iter().map(desugar)),
        Regex::Star(inner) => Core::star(desugar(inner)),
        Regex::Plus(inner) => {
            let c = desugar(inner);
            Core::seq(c.clone(), Core::star(c))
        }
        Regex::Opt(inner) => Core::alt(Core::Eps, desugar(inner)),
        Regex::Rep { inner, min, max } => desugar_rep(&desugar(inner), *min, *max),
    }
}

/// The member bytes of a (possibly negated) byte character class, ascending.
fn class_bytes(c: &Class<u8>) -> Vec<u8> {
    let mut member = [false; 256];
    for r in &c.ranges {
        for b in r.lo..=r.hi {
            member[usize::from(b)] = true;
        }
    }
    (0u16..=255)
        .map(|b| b as u8)
        .filter(|&b| member[usize::from(b)] != c.negated)
        .collect()
}

fn desugar_rep(inner: &Core, min: u32, max: Option<u32>) -> Core {
    let copies = |n: u32| (0..n).map(|_| inner.clone());
    match max {
        Some(m) if m == min => Core::seq_all(copies(min)),
        Some(m) => {
            let extra = m.saturating_sub(min);
            let opts = (0..extra).map(|_| Core::alt(Core::Eps, inner.clone()));
            Core::seq_all(copies(min).chain(opts))
        }
        None => Core::seq_all(copies(min).chain(std::iter::once(Core::star(inner.clone())))),
    }
}

// ============================================================================
// Core -> reified HOL `regex u8` term.
// ============================================================================

/// The byte alphabet `u8`.
fn u8ty() -> Type {
    ir::u8_alphabet()
}

/// Build the reified `regex u8` term `⌜c⌝` for a [`Core`].
pub fn core_to_term(c: &Core) -> Term {
    let a = u8ty();
    core_to_term_at(&a, c)
}

fn core_to_term_at(a: &Type, c: &Core) -> Term {
    match c {
        Core::Empty => ir::r_empty(a),
        Core::Eps => ir::r_eps(a),
        Core::Lit(b) => ir::r_lit(a, Term::u8_lit(*b)),
        Core::Alt(x, y) => ir::r_alt(a, core_to_term_at(a, x), core_to_term_at(a, y)),
        Core::Seq(x, y) => ir::r_seq(a, core_to_term_at(a, x), core_to_term_at(a, y)),
        Core::Star(x) => ir::r_star(a, core_to_term_at(a, x)),
    }
}

// ============================================================================
// Public compile / predicate surface.
// ============================================================================

/// Compile a byte regex to the reified HOL term `⌜r⌝ : regex u8`.
pub fn compile(r: &Regex<u8>) -> Term {
    core_to_term(&desugar(r))
}

/// The **byte predicate** the grammar denotes: the language
/// `⟦⌜r⌝⟧ : set (list u8)`. A bytestring `w` *satisfies* the grammar iff
/// `mem w ⟦⌜r⌝⟧` — which [`tactic::prove_member`] proves for concrete `w`.
pub fn predicate(r: &Regex<u8>) -> Result<Term> {
    ir::denote(&u8ty(), compile(r))
}

// ============================================================================
// SpecTec entry points.
// ============================================================================

/// Error compiling a SpecTec grammar symbol to a byte predicate: it left the
/// regular fragment (a grammar reference, capture, or parametric iteration).
pub use covalence_spectec::regex::BridgeError;

/// Desugar a [`SpecTecSym`] (over bytes) to [`Core`], via
/// `covalence-spectec`'s byte bridge.
pub fn sym_to_core(sym: &SpecTecSym) -> std::result::Result<Core, BridgeError> {
    covalence_spectec::regex::sym_to_regex_u8(sym).map(|r| desugar(&r))
}

/// Compile a [`SpecTecSym`] directly to the reified term `⌜r⌝ : regex u8`.
pub fn compile_sym(sym: &SpecTecSym) -> std::result::Result<Term, BridgeError> {
    sym_to_core(sym).map(|c| core_to_term(&c))
}

#[cfg(test)]
mod tests {
    use super::*;
    use covalence_grammar::regex::parse_regex_u8;

    fn lit(b: u8) -> Core {
        Core::Lit(b)
    }

    #[test]
    fn desugar_basics() {
        assert_eq!(desugar(&Regex::<u8>::Eps), Core::Eps);
        assert_eq!(desugar(&Regex::Lit(0x61u8)), lit(0x61));
        // `ab` -> seq a b
        assert_eq!(
            desugar(&parse_regex_u8("ab").unwrap()),
            Core::seq(lit(b'a'), lit(b'b')),
        );
        // `a+` -> a a*
        assert_eq!(
            desugar(&parse_regex_u8("a+").unwrap()),
            Core::seq(lit(b'a'), Core::star(lit(b'a'))),
        );
        // `a?` -> eps | a
        assert_eq!(
            desugar(&parse_regex_u8("a?").unwrap()),
            Core::alt(Core::Eps, lit(b'a')),
        );
    }

    #[test]
    fn desugar_class_to_alt_of_bytes() {
        // `[ac]` -> a | c
        let c = desugar(&parse_regex_u8("[ac]").unwrap());
        assert_eq!(c, Core::alt(lit(b'a'), lit(b'c')));
        // empty negated-everything class is unsatisfiable -> Empty
        assert_eq!(desugar(&parse_regex_u8("[^\\x00-\\xFF]").unwrap()), Core::Empty);
    }

    #[test]
    fn desugar_rep() {
        // `a{2}` -> a a
        assert_eq!(
            desugar(&parse_regex_u8("a{2}").unwrap()),
            Core::seq(lit(b'a'), lit(b'a')),
        );
        // `a{1,2}` -> a (eps|a)
        assert_eq!(
            desugar(&parse_regex_u8("a{1,2}").unwrap()),
            Core::seq(lit(b'a'), Core::alt(Core::Eps, lit(b'a'))),
        );
    }

    #[test]
    fn compile_is_well_typed_regex_u8() {
        for src in ["a", "ab", "a|b", "a*", "(?:ab)*", "[a-c]"] {
            let r = parse_regex_u8(src).unwrap();
            let term = compile(&r);
            assert_eq!(
                term.type_of().unwrap(),
                ir::regex(u8ty()),
                "compile({src}) should be a regex u8 term",
            );
        }
    }

    #[test]
    fn predicate_is_a_byte_language() {
        let r = parse_regex_u8("a|b").unwrap();
        let pred = predicate(&r).unwrap();
        // set (list u8)
        assert_eq!(
            pred.type_of().unwrap(),
            crate::init::lang::lang(crate::init::list::list(u8ty())),
        );
    }

    #[test]
    fn compile_sym_routes_through_byte_bridge() {
        // `(seq (num 0x61) (num 0x62))` -> reified `seq (lit a)(lit b)`.
        let sym = covalence_spectec::parse::parse_sym("(seq (num 0x61) (num 0x62))").unwrap();
        let term = compile_sym(&sym).unwrap();
        let expected = core_to_term(&Core::seq(lit(0x61), lit(0x62)));
        assert_eq!(term, expected);
    }

    #[test]
    fn compile_sym_rejects_grammar_reference() {
        let sym = covalence_spectec::parse::parse_sym("(var \"instr\")").unwrap();
        assert!(matches!(
            compile_sym(&sym),
            Err(BridgeError::GrammarRef { .. }),
        ));
    }
}
