//! **Regular expressions → byte predicates**, and the matching tactic over
//! them. A first-class, standalone module: regexes are the regular base case of
//! *every* grammar (SpecTec, BNF, S-expressions, …) and are used pervasively
//! across the byte-parsing stack, so they get top-quality support here,
//! independent of any one grammar front end.
//!
//! Relationship to [`crate::init::regex`]: that module is the **reified HOL
//! object logic** (the `regex u8` datatype, the `Matches` judgement,
//! soundness). *This* module is the **driver** — it compiles a surface
//! [`covalence_grammar::regex::Regex<u8>`] into those reified terms and runs a
//! tactic to build `Matches` derivations. The kernel re-checks everything; the
//! driver is untrusted.
//!
//! Three layers:
//!
//! - [`Core`] — the six-constructor byte regex the reified HOL `regex u8`
//!   datatype has, with [`desugar`] folding a full `Regex<u8>` down to it.
//! - [`compile`] / [`predicate`] — the reified regex term `⌜r⌝ : regex u8` and
//!   the language `⟦⌜r⌝⟧ : set (list u8)` it denotes (the byte predicate).
//! - [`tactic`] — the matcher that builds `⊢ Matches ⌜r⌝ w` and, via soundness,
//!   `⊢ mem w ⟦⌜r⌝⟧`. It separates a fast pure-Rust *recognizer* (the part to
//!   accelerate with WASM later) from kernel *proof construction*.

use std::sync::Arc;

use covalence_core::{Result, Term, Type};
use covalence_grammar::regex::{Class, Regex};

use crate::init::regex as ir;

pub mod tactic;

// ============================================================================
// Core — the six-constructor byte regex the reified HOL datatype mirrors.
// ============================================================================

/// A byte regex restricted to the six constructors the reified HOL `regex u8`
/// datatype ([`crate::init::regex`]) has. The full surface
/// [`Regex<u8>`] desugars into this via [`desugar`].
///
/// Keeping a distinct `Core` (rather than compiling `Regex<u8>` directly) means
/// the term compiler ([`core_to_term`]) and the matcher ([`tactic`]) share
/// *one* desugaring, so the regex term a derivation is about is always exactly
/// the one the matcher recursed over.
///
/// Sub-regexes are held behind [`Arc`], not `Box`, so identical subtrees can be
/// **shared** (a single allocation referenced many times) and, later,
/// hash-consed/interned. [`desugar`] already shares the obvious case — `r+`
/// reuses the same `Arc` for the `r` and the `r*` — and the matcher's memo keys
/// on the node pointer, so shared subtrees are recognised once.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Core {
    /// `∅` — matches nothing.
    Empty,
    /// `ε` — matches only the empty word.
    Eps,
    /// A single byte literal.
    Lit(u8),
    /// Alternation `x | y`.
    Alt(Arc<Core>, Arc<Core>),
    /// Concatenation `x y`.
    Seq(Arc<Core>, Arc<Core>),
    /// Kleene star `x*`.
    Star(Arc<Core>),
}

impl Core {
    /// `x | y`.
    pub fn alt(x: Core, y: Core) -> Core {
        Core::Alt(Arc::new(x), Arc::new(y))
    }
    /// `x y`.
    pub fn seq(x: Core, y: Core) -> Core {
        Core::Seq(Arc::new(x), Arc::new(y))
    }
    /// `x*`.
    pub fn star(x: Core) -> Core {
        Core::Star(Arc::new(x))
    }

    /// Right-fold a list of cores into a binary [`Core::Seq`] chain, collapsing
    /// the empty list to `eps` and a singleton to itself.
    fn seq_all(items: impl Iterator<Item = Core>) -> Core {
        let mut items: Vec<Core> = items.collect();
        match items.len() {
            0 => Core::Eps,
            1 => items.pop().expect("len 1"),
            _ => {
                let last = items.pop().expect("len >= 2");
                items.into_iter().rev().fold(last, |acc, x| Core::seq(x, acc))
            }
        }
    }

    /// Fold a list of cores into a **balanced** binary [`Core::Alt`] tree,
    /// collapsing the empty list to `empty` and a singleton to itself.
    ///
    /// Balanced (not right-nested) so that matching one alternative of a
    /// `K`-way alternation — in particular a desugared character class of `K`
    /// bytes — descends `O(log K)` `alt`-injections rather than `O(K)`. That is
    /// the difference between a 7-step and a 256-step proof for matching a byte
    /// against `.`; the matched word and language are unchanged.
    fn alt_all(items: impl Iterator<Item = Core>) -> Core {
        let items: Vec<Core> = items.collect();
        match items.len() {
            0 => Core::Empty,
            1 => items.into_iter().next().expect("len 1"),
            _ => balanced(items, Core::alt),
        }
    }
}

/// Combine a non-empty list into a balanced binary tree under `comb`.
fn balanced(mut items: Vec<Core>, comb: fn(Core, Core) -> Core) -> Core {
    while items.len() > 1 {
        let mut next = Vec::with_capacity(items.len().div_ceil(2));
        let mut it = items.into_iter();
        while let Some(a) = it.next() {
            match it.next() {
                Some(b) => next.push(comb(a, b)),
                None => next.push(a),
            }
        }
        items = next;
    }
    items.pop().expect("non-empty")
}

// ============================================================================
// Desugaring  Regex<u8> -> Core.
// ============================================================================

/// Desugar a full byte regex into the six-constructor [`Core`] form.
///
/// - character classes become a balanced alternation of their member byte
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
            // Share one `Arc` between the `r` and the `r*` of `r+ = r r*`.
            let c = Arc::new(desugar(inner));
            Core::Seq(Arc::clone(&c), Arc::new(Core::Star(c)))
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
pub(crate) fn u8ty() -> Type {
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

/// The **byte predicate** the regex denotes: the language
/// `⟦⌜r⌝⟧ : set (list u8)`. A bytestring `w` *satisfies* it iff
/// `mem w ⟦⌜r⌝⟧` — which [`tactic::prove_member`] proves for concrete `w`.
pub fn predicate(r: &Regex<u8>) -> Result<Term> {
    ir::denote(&u8ty(), compile(r))
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
        assert_eq!(
            desugar(&parse_regex_u8("[^\\x00-\\xFF]").unwrap()),
            Core::Empty
        );
    }

    #[test]
    fn desugar_rep_cases() {
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
}
