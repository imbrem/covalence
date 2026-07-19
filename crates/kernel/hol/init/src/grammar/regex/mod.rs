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

use std::sync::{Arc, LazyLock};

use covalence_core::{Result, Term, Type};
use covalence_grammar::regex::{Class, Regex as Surface};
use covalence_hol_eval::EvalThm as Thm;

use crate::init::regex as ir;
use crate::init::regex::{r_alt, r_empty, r_eps, r_lit, r_seq, r_star};

pub mod replay;
pub mod tactic;

// ============================================================================
// Core — the six-constructor byte regex the reified HOL datatype mirrors.
// ============================================================================

/// A **compiled** byte regex node: its [`CoreKind`] (the six-constructor shape
/// the reified HOL `regex u8` datatype mirrors) paired with the reified term
/// `⌜c⌝ : regex u8`, built **once** at construction. The full surface
/// [`Surface<u8>`](Surface) compiles into this via [`desugar`].
///
/// Caching `⌜c⌝` on the node avoids a separate `core_to_term` pass: the
/// matcher and soundness read `c.term()` directly instead of rebuilding the
/// reified term at every `alt`/`seq`/`star` node. The term is interned through
/// the [`HashCons`](covalence_core::term::HashCons) threaded down [`desugar`], so structurally-equal sub-terms
/// (a repeated sub-regex, the alphabet type) share one allocation.
///
/// Sub-regexes are held behind [`Arc`] so identical subtrees share (a single
/// allocation referenced many times); [`desugar`] shares the obvious case —
/// `r+` reuses one `Arc` for the `r` and the `r*` — and the matcher's memo keys
/// on the node pointer, so shared subtrees are recognised once. Equality and
/// hashing are over the [`CoreKind`] only; the cached term is a pure function
/// of it.
#[derive(Clone, Debug)]
pub struct Core {
    kind: CoreKind,
    /// The reified `regex u8` term `⌜c⌝`, interned at construction.
    term: Term,
}

/// The shape of a [`Core`] node: the six constructors the reified HOL `regex
/// u8` datatype has.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum CoreKind {
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

impl PartialEq for Core {
    fn eq(&self, other: &Self) -> bool {
        self.kind == other.kind
    }
}
impl Eq for Core {}
impl std::hash::Hash for Core {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.kind.hash(state);
    }
}

/// The reified terms of the leaf constructors, built **once**: `⌜empty⌝`,
/// `⌜eps⌝`, and `⌜lit b⌝` for every byte `b`. Each leaf's encoding is a fixed
/// six-handler Church term, so caching them globally means leaf construction is
/// a cheap `Arc` clone and every `lit b` across every regex shares one
/// allocation — without paying a per-`desugar` interner (whose per-node re-walk
/// is `O(subterm)` and goes quadratic over a 256-way class like `.`).
static R_LEAVES: LazyLock<Leaves> = LazyLock::new(|| {
    let a = u8ty();
    Leaves {
        empty: r_empty(&a),
        eps: r_eps(&a),
        lit: Box::new(std::array::from_fn(|b| {
            r_lit(&a, covalence_hol_eval::mk_u8(b as u8))
        })),
    }
});

struct Leaves {
    empty: Term,
    eps: Term,
    lit: Box<[Term; 256]>,
}

impl Core {
    /// The node's constructor shape.
    pub fn kind(&self) -> &CoreKind {
        &self.kind
    }

    /// The cached reified term `⌜c⌝ : regex u8`.
    pub fn term(&self) -> &Term {
        &self.term
    }

    fn empty() -> Arc<Core> {
        Arc::new(Core {
            kind: CoreKind::Empty,
            term: R_LEAVES.empty.clone(),
        })
    }
    fn eps() -> Arc<Core> {
        Arc::new(Core {
            kind: CoreKind::Eps,
            term: R_LEAVES.eps.clone(),
        })
    }
    fn lit(b: u8) -> Arc<Core> {
        Arc::new(Core {
            kind: CoreKind::Lit(b),
            term: R_LEAVES.lit[b as usize].clone(),
        })
    }
    /// `x | y`. The term reuses the children's cached `⌜x⌝`/`⌜y⌝` `Arc`s, so
    /// sub-tree sharing is inherited without any re-walk.
    fn alt(x: Arc<Core>, y: Arc<Core>) -> Arc<Core> {
        let term = r_alt(&u8ty(), x.term.clone(), y.term.clone());
        Arc::new(Core {
            kind: CoreKind::Alt(x, y),
            term,
        })
    }
    /// `x y`.
    fn seq(x: Arc<Core>, y: Arc<Core>) -> Arc<Core> {
        let term = r_seq(&u8ty(), x.term.clone(), y.term.clone());
        Arc::new(Core {
            kind: CoreKind::Seq(x, y),
            term,
        })
    }
    /// `x*`.
    fn star(x: Arc<Core>) -> Arc<Core> {
        let term = r_star(&u8ty(), x.term.clone());
        Arc::new(Core {
            kind: CoreKind::Star(x),
            term,
        })
    }

    /// Right-fold cores into a binary `Seq` chain, collapsing the empty list to
    /// `eps` and a singleton to itself.
    fn seq_all(mut items: Vec<Arc<Core>>) -> Arc<Core> {
        match items.len() {
            0 => Core::eps(),
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

    /// Fold cores into a **balanced** binary `Alt` tree, collapsing the empty
    /// list to `empty` and a singleton to itself.
    ///
    /// Balanced (not right-nested) so that matching one alternative of a
    /// `K`-way alternation — in particular a desugared character class of `K`
    /// bytes — descends `O(log K)` `alt`-injections rather than `O(K)`. That is
    /// the difference between a 7-step and a 256-step proof for matching a byte
    /// against `.`; the matched word and language are unchanged.
    fn alt_all(items: Vec<Arc<Core>>) -> Arc<Core> {
        match items.len() {
            0 => Core::empty(),
            1 => items.into_iter().next().expect("len 1"),
            _ => balanced(items),
        }
    }
}

/// Combine a non-empty list into a balanced binary `Alt` tree.
fn balanced(mut items: Vec<Arc<Core>>) -> Arc<Core> {
    while items.len() > 1 {
        let mut next = Vec::with_capacity(items.len().div_ceil(2));
        let mut it = items.into_iter();
        while let Some(a) = it.next() {
            match it.next() {
                Some(b) => next.push(Core::alt(a, b)),
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

/// Desugar a full byte regex into a compiled [`Core`] (each node carrying its
/// cached `⌜·⌝`; leaf terms come from the global `R_LEAVES` cache).
///
/// - character classes become a balanced alternation of their member byte
///   literals (a negated class is complemented against `0x00..=0xFF` first; an
///   empty class becomes [`CoreKind::Empty`]);
/// - `r+` becomes `r r*`, `r?` becomes `ε | r`;
/// - `r{m,m}` becomes `m` copies, `r{m,n}` becomes `m` copies then `n−m`
///   optionals, `r{m,}` becomes `m` copies then `r*`.
pub fn desugar(r: &Surface<u8>) -> Arc<Core> {
    match r {
        Surface::Empty => Core::empty(),
        Surface::Eps => Core::eps(),
        Surface::Lit(b) => Core::lit(*b),
        Surface::Class(c) => Core::alt_all(class_bytes(c).into_iter().map(Core::lit).collect()),
        Surface::Concat(items) => Core::seq_all(items.iter().map(desugar).collect()),
        Surface::Alt(items) => Core::alt_all(items.iter().map(desugar).collect()),
        Surface::Star(inner) => Core::star(desugar(inner)),
        Surface::Plus(inner) => {
            // Share one `Arc` between the `r` and the `r*` of `r+ = r r*`.
            let x = desugar(inner);
            let star = Core::star(Arc::clone(&x));
            Core::seq(x, star)
        }
        Surface::Opt(inner) => Core::alt(Core::eps(), desugar(inner)),
        Surface::Rep { inner, min, max } => desugar_rep(desugar(inner), *min, *max),
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

fn desugar_rep(inner: Arc<Core>, min: u32, max: Option<u32>) -> Arc<Core> {
    let mut items: Vec<Arc<Core>> = Vec::new();
    for _ in 0..min {
        items.push(Arc::clone(&inner));
    }
    match max {
        Some(m) if m == min => Core::seq_all(items),
        Some(m) => {
            let extra = m.saturating_sub(min);
            for _ in 0..extra {
                items.push(Core::alt(Core::eps(), Arc::clone(&inner)));
            }
            Core::seq_all(items)
        }
        None => {
            items.push(Core::star(Arc::clone(&inner)));
            Core::seq_all(items)
        }
    }
}

// ============================================================================
// Public compile / predicate surface.
// ============================================================================

/// The byte alphabet `u8`.
pub(crate) fn u8ty() -> Type {
    ir::u8_alphabet()
}

/// Compile a byte regex to the reified HOL term `⌜r⌝ : regex u8`.
pub fn compile(r: &Surface<u8>) -> Term {
    desugar(r).term().clone()
}

/// The **byte predicate** the regex denotes: the language
/// `⟦⌜r⌝⟧ : set (list u8)`. A bytestring `w` *satisfies* it iff
/// `mem w ⟦⌜r⌝⟧` — which [`tactic::prove_member`] proves for concrete `w`.
pub fn predicate(r: &Surface<u8>) -> Result<Term> {
    ir::denote(&u8ty(), compile(r))
}

// ============================================================================
// Reusable compiled object — a `Core` carries its cached `⌜c⌝`, so it *is* the
// compile-once / match-many handle (no separate wrapper needed).
// ============================================================================

impl Core {
    /// Parse and compile a regex source string (see
    /// [`covalence_grammar::regex::parse_regex_u8`]); a fresh interner is used.
    pub fn parse(
        src: &str,
    ) -> std::result::Result<Arc<Core>, covalence_grammar::regex::ParseError> {
        Ok(desugar(&covalence_grammar::regex::parse_regex_u8(src)?))
    }

    /// The byte predicate (language) `⟦⌜c⌝⟧ : set (list u8)` this regex denotes,
    /// from the cached `⌜c⌝` (cf. the free [`predicate`]).
    pub fn predicate(&self) -> Result<Term> {
        ir::denote(&u8ty(), self.term.clone())
    }

    /// Prove `⊢ Matches ⌜c⌝ w` for a concrete byte input, or `None` if it is not
    /// in `L(c)` (cf. the free [`tactic::prove_matches`]).
    pub fn prove_matches(&self, input: impl AsRef<[u8]>) -> Result<Option<Thm>> {
        tactic::matches_core(self, input.as_ref())
    }

    /// Prove `⊢ mem w ⟦⌜c⌝⟧` (membership in the denoted language) for a concrete
    /// byte input (cf. the free [`tactic::prove_member`]).
    pub fn prove_member(&self, input: impl AsRef<[u8]>) -> Result<Option<Thm>> {
        tactic::member_core(self, &self.term, input.as_ref())
    }

    /// Prove `{Matches ⌜cᵢ⌝ Xᵢ}ᵢ ⊢ Matches ⌜c⌝ w` for a word **expression** that
    /// may contain variables (cf. the free [`tactic::prove_word`]).
    pub fn prove_word(&self, w: &tactic::Word) -> Result<Option<Thm>> {
        tactic::word_core(self, w)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use covalence_grammar::regex::parse_regex_u8;

    // `Core` equality is over [`CoreKind`] only.
    fn de(src: &str) -> Arc<Core> {
        desugar(&parse_regex_u8(src).unwrap())
    }

    #[test]
    fn desugar_basics() {
        assert_eq!(desugar(&Surface::<u8>::Eps), Core::eps());
        assert_eq!(desugar(&Surface::Lit(0x61u8)), Core::lit(0x61));
        // `ab` -> seq a b
        assert_eq!(de("ab"), Core::seq(Core::lit(b'a'), Core::lit(b'b')));
        // `a+` -> a a*
        let astar = Core::star(Core::lit(b'a'));
        assert_eq!(de("a+"), Core::seq(Core::lit(b'a'), astar));
        // `a?` -> eps | a
        assert_eq!(de("a?"), Core::alt(Core::eps(), Core::lit(b'a')));
    }

    #[test]
    fn desugar_class_to_alt_of_bytes() {
        // `[ac]` -> a | c
        assert_eq!(de("[ac]"), Core::alt(Core::lit(b'a'), Core::lit(b'c')));
        // empty negated-everything class is unsatisfiable -> Empty
        assert_eq!(de("[^\\x00-\\xFF]"), Core::empty());
    }

    #[test]
    fn desugar_rep_cases() {
        // `a{2}` -> a a
        assert_eq!(de("a{2}"), Core::seq(Core::lit(b'a'), Core::lit(b'a')));
        // `a{1,2}` -> a (eps|a)
        let opt = Core::alt(Core::eps(), Core::lit(b'a'));
        assert_eq!(de("a{1,2}"), Core::seq(Core::lit(b'a'), opt));
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
