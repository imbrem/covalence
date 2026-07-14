//! Context-free grammars over a generic alphabet, with regex terminals.
//!
//! [`Cfg<T>`] is a neutral, frontend-agnostic IR: SpecTec lowering produces
//! it, and the kernel driver (`covalence-init`'s CFG stratum) consumes it.
//! It is deliberately structure-preserving — no normalisation happens here
//! beyond what the [`Regex`] smart constructors already do, so a `Cfg` is a
//! faithful record of what the frontend emitted.
//!
//! A production's right-hand side is a sequence of [`Seg`]ments: either a
//! terminal segment (a [`Regex<T>`] whose language the segment's slice of
//! the word must match) or a reference to another non-terminal.
//!
//! # Production order invariant
//!
//! [`Cfg::productions`] returns productions in **insertion order**, and
//! [`Cfg::add_prod`] returns that global index. This order is FIXED and
//! deterministic: the kernel lowering assigns clause `i` of its rule set to
//! production `i`, so reordering productions would silently change the
//! meaning of every recorded clause index. Never sort or dedupe `prods`.
//!
//! Non-terminal *names* ([`NtDef::name`]) are driver-side convenience only —
//! kernel tags are the dense [`NtId`] indices (names = efficiency, never
//! soundness).

use std::collections::{HashMap, HashSet};

use crate::regex::{Class, Regex};

/// Index of a non-terminal within its [`Cfg`]. Dense, assigned by
/// [`Cfg::add_nt`] in insertion order; the kernel lowering uses this index
/// directly as the non-terminal's nat tag.
#[derive(Copy, Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct NtId(usize);

impl NtId {
    /// The dense index (also the kernel nat tag).
    pub fn index(self) -> usize {
        self.0
    }
}

/// A non-terminal definition. The name is a driver-side label for error
/// messages and lookup; it never affects lowering or soundness.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NtDef {
    pub name: String,
}

/// One segment of a production's right-hand side.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Seg<T> {
    /// Terminal segment: the corresponding slice of the word must match
    /// this regex.
    Term(Regex<T>),
    /// Reference to a non-terminal of the same grammar.
    NonTerm(NtId),
}

impl<T> Seg<T> {
    pub fn term(r: Regex<T>) -> Self {
        Seg::Term(r)
    }

    pub fn nt(id: NtId) -> Self {
        Seg::NonTerm(id)
    }
}

/// A production `lhs → segs`. An empty `segs` is the ε-production.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Prod<T> {
    pub lhs: NtId,
    pub segs: Vec<Seg<T>>,
}

/// Structural validation errors. Raw `usize` indices (not [`NtId`]) so the
/// message can report an out-of-range value directly.
#[derive(Debug, Clone, Eq, PartialEq, thiserror::Error)]
pub enum CfgError {
    #[error("production {prod}: lhs non-terminal {nt} out of range ({len} non-terminals)")]
    LhsOutOfRange { prod: usize, nt: usize, len: usize },
    #[error(
        "production {prod}, segment {seg}: non-terminal reference {nt} out of range ({len} non-terminals)"
    )]
    NonTermOutOfRange {
        prod: usize,
        seg: usize,
        nt: usize,
        len: usize,
    },
}

/// A context-free grammar with regex terminals over alphabet `T`.
///
/// Fields are private so all construction flows through the builder API and
/// the production-order invariant (see module docs) cannot be broken from
/// outside.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Cfg<T> {
    nts: Vec<NtDef>,
    prods: Vec<Prod<T>>,
}

impl<T> Default for Cfg<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> Cfg<T> {
    pub fn new() -> Self {
        Cfg {
            nts: Vec::new(),
            prods: Vec::new(),
        }
    }

    /// Add a fresh non-terminal. Duplicate names are allowed (names are
    /// labels, not identity); [`Cfg::lookup`] returns the first match.
    pub fn add_nt(&mut self, name: impl Into<String>) -> NtId {
        let id = NtId(self.nts.len());
        self.nts.push(NtDef { name: name.into() });
        id
    }

    /// Get the first non-terminal with this name, adding it if absent.
    /// Convenience for lowerings that key non-terminals by source name.
    pub fn get_or_add_nt(&mut self, name: &str) -> NtId {
        match self.lookup(name) {
            Some(id) => id,
            None => self.add_nt(name),
        }
    }

    /// First non-terminal with the given name, if any.
    pub fn lookup(&self, name: &str) -> Option<NtId> {
        self.nts.iter().position(|d| d.name == name).map(NtId)
    }

    /// Append a production and return its global index — the kernel clause
    /// index under the production-order invariant (see module docs).
    /// Range errors are deferred to [`Cfg::validate`].
    pub fn add_prod(&mut self, lhs: NtId, segs: Vec<Seg<T>>) -> usize {
        let idx = self.prods.len();
        self.prods.push(Prod { lhs, segs });
        idx
    }

    /// Non-terminal definitions in [`NtId`] index order.
    pub fn nts(&self) -> &[NtDef] {
        &self.nts
    }

    /// Name of a non-terminal, if in range.
    pub fn nt_name(&self, nt: NtId) -> Option<&str> {
        self.nts.get(nt.0).map(|d| d.name.as_str())
    }

    pub fn num_nts(&self) -> usize {
        self.nts.len()
    }

    /// All productions, in insertion order. **This order is the kernel
    /// clause order** (see module docs); it never changes once built.
    pub fn productions(&self) -> &[Prod<T>] {
        &self.prods
    }

    /// Productions with the given left-hand side, as `(global_index, prod)`
    /// pairs in ascending global (= kernel clause) order.
    pub fn productions_of(&self, nt: NtId) -> impl Iterator<Item = (usize, &Prod<T>)> {
        self.prods
            .iter()
            .enumerate()
            .filter(move |(_, p)| p.lhs == nt)
    }

    /// Check that every [`NtId`] (lhs and `Seg::NonTerm`) is in range.
    /// Analyses and [`Cfg::naive_parse`] are total on invalid grammars
    /// (out-of-range refs simply never derive), but lowerings should
    /// `validate` first and refuse invalid input.
    pub fn validate(&self) -> Result<(), CfgError> {
        let len = self.nts.len();
        for (prod, p) in self.prods.iter().enumerate() {
            if p.lhs.0 >= len {
                return Err(CfgError::LhsOutOfRange {
                    prod,
                    nt: p.lhs.0,
                    len,
                });
            }
            for (seg, s) in p.segs.iter().enumerate() {
                if let Seg::NonTerm(nt) = s
                    && nt.0 >= len
                {
                    return Err(CfgError::NonTermOutOfRange {
                        prod,
                        seg,
                        nt: nt.0,
                        len,
                    });
                }
            }
        }
        Ok(())
    }
}

impl<T: Clone + PartialOrd> Cfg<T> {
    /// Nullable set: `result[i]` iff non-terminal `i` derives the empty
    /// word. Standard monotone fixpoint; terminal segments are nullable
    /// via [`Regex::nullable`]. Out-of-range refs count as non-nullable.
    pub fn nullable_set(&self) -> Vec<bool> {
        let mut nullable = vec![false; self.nts.len()];
        loop {
            let mut changed = false;
            for p in &self.prods {
                let Some(&lhs_nullable) = nullable.get(p.lhs.0) else {
                    continue;
                };
                if lhs_nullable {
                    continue;
                }
                let all = p.segs.iter().all(|s| match s {
                    Seg::Term(r) => r.nullable(),
                    Seg::NonTerm(nt) => nullable.get(nt.0).copied().unwrap_or(false),
                });
                if all {
                    nullable[p.lhs.0] = true;
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        nullable
    }

    /// Whether non-terminal `nt` derives the empty word.
    pub fn nullable_nt(&self, nt: NtId) -> bool {
        self.nullable_set().get(nt.0).copied().unwrap_or(false)
    }

    /// Detect left recursion (including indirect and nullable-prefix left
    /// recursion) and report one offending cycle as a path
    /// `[A, B, …, A]` whose first and last elements coincide.
    ///
    /// The left-reachability edge `A → B` exists when some production of
    /// `A` mentions `B` with every earlier segment nullable — exactly the
    /// condition under which [`Cfg::naive_parse`]'s in-progress guard could
    /// fire, so `left_recursion().is_none()` guarantees the naive
    /// recognizer is complete.
    pub fn left_recursion(&self) -> Option<Vec<NtId>> {
        let n = self.nts.len();
        let nullable = self.nullable_set();
        let mut edges: Vec<Vec<usize>> = vec![Vec::new(); n];
        for p in &self.prods {
            let Some(out) = edges.get_mut(p.lhs.0) else {
                continue;
            };
            for s in &p.segs {
                match s {
                    Seg::Term(r) => {
                        if !r.nullable() {
                            break;
                        }
                    }
                    Seg::NonTerm(nt) => {
                        if nt.0 < n {
                            out.push(nt.0);
                        }
                        if !nullable.get(nt.0).copied().unwrap_or(false) {
                            break;
                        }
                    }
                }
            }
        }
        // Iterative 3-colour DFS (untrusted grammars must not blow the
        // call stack): 0 = white, 1 = grey (on path), 2 = black.
        let mut color = vec![0u8; n];
        for start in 0..n {
            if color[start] != 0 {
                continue;
            }
            let mut path: Vec<usize> = vec![start];
            let mut next_edge: Vec<usize> = vec![0];
            color[start] = 1;
            while let Some(&v) = path.last() {
                let i = *next_edge.last().expect("parallel to path");
                if let Some(&w) = edges[v].get(i) {
                    *next_edge.last_mut().expect("parallel to path") += 1;
                    match color[w] {
                        1 => {
                            // Grey target: the cycle is the path suffix
                            // starting at `w`, closed back to `w`.
                            let pos = path
                                .iter()
                                .position(|&x| x == w)
                                .expect("grey node is on the path");
                            let mut cycle: Vec<NtId> =
                                path[pos..].iter().map(|&x| NtId(x)).collect();
                            cycle.push(NtId(w));
                            return Some(cycle);
                        }
                        0 => {
                            color[w] = 1;
                            path.push(w);
                            next_edge.push(0);
                        }
                        _ => {}
                    }
                } else {
                    color[v] = 2;
                    path.pop();
                    next_edge.pop();
                }
            }
        }
        None
    }

    /// Naive recursive recognizer: does `nt` derive exactly `input`?
    ///
    /// **Test oracle only** — deliberately independent of the proving
    /// recognizer/tactic pipeline (kernel-facing code must never call it),
    /// so differential tests compare two unrelated implementations.
    /// Exponential-time split enumeration with a `(nt, lo, hi)` memo table
    /// and an in-progress guard; it terminates on *every* grammar (keys are
    /// finite) but is complete only when [`Cfg::left_recursion`] is `None`
    /// (a guard cut can only occur under left recursion). Out-of-range
    /// `nt`s derive nothing.
    pub fn naive_parse(&self, nt: NtId, input: &[T]) -> bool {
        let mut ctx = NaiveCtx {
            cfg: self,
            input,
            memo: HashMap::new(),
            in_progress: HashSet::new(),
        };
        ctx.derives(nt, 0, input.len())
    }
}

type SpanKey = (usize, usize, usize);

struct NaiveCtx<'a, T> {
    cfg: &'a Cfg<T>,
    input: &'a [T],
    memo: HashMap<SpanKey, bool>,
    in_progress: HashSet<SpanKey>,
}

impl<'a, T: Clone + PartialOrd> NaiveCtx<'a, T> {
    fn derives(&mut self, nt: NtId, lo: usize, hi: usize) -> bool {
        let key = (nt.0, lo, hi);
        if let Some(&r) = self.memo.get(&key) {
            return r;
        }
        if !self.in_progress.insert(key) {
            // Re-entry on the same span ⇒ left recursion; cut. Only
            // reachable when `left_recursion()` is `Some` (see doc).
            return false;
        }
        let mut result = false;
        for i in 0..self.cfg.prods.len() {
            if self.cfg.prods[i].lhs == nt && self.segs_match(i, 0, lo, hi) {
                result = true;
                break;
            }
        }
        self.in_progress.remove(&key);
        self.memo.insert(key, result);
        result
    }

    /// Do segments `seg..` of production `prod` derive `input[lo..hi]`?
    fn segs_match(&mut self, prod: usize, seg: usize, lo: usize, hi: usize) -> bool {
        let Some(s) = self.cfg.prods[prod].segs.get(seg) else {
            return lo == hi;
        };
        for mid in lo..=hi {
            let head_ok = match s {
                Seg::Term(r) => regex_matches(r, &self.input[lo..mid]),
                Seg::NonTerm(nt) => {
                    let nt = *nt;
                    self.derives(nt, lo, mid)
                }
            };
            if head_ok && self.segs_match(prod, seg.saturating_add(1), mid, hi) {
                return true;
            }
        }
        false
    }
}

/// Naive whole-slice regex matcher — part of the [`Cfg::naive_parse`] test
/// oracle, deliberately independent of any derivative-based or proving
/// matcher. Exponential split enumeration; terminates because every
/// recursive call is on a strictly shorter slice or a structurally smaller
/// regex.
fn regex_matches<T: Clone + PartialOrd>(r: &Regex<T>, w: &[T]) -> bool {
    match r {
        Regex::Empty => false,
        Regex::Eps => w.is_empty(),
        Regex::Lit(a) => w.len() == 1 && w[0] == *a,
        Regex::Class(c) => w.len() == 1 && class_contains(c, &w[0]),
        Regex::Concat(items) => concat_matches(items, w),
        Regex::Alt(items) => items.iter().any(|x| regex_matches(x, w)),
        Regex::Star(inner) => star_matches(inner, w),
        Regex::Plus(inner) => {
            if w.is_empty() {
                regex_matches(inner, w)
            } else {
                (1..=w.len()).any(|k| regex_matches(inner, &w[..k]) && star_matches(inner, &w[k..]))
            }
        }
        Regex::Opt(inner) => w.is_empty() || regex_matches(inner, w),
        Regex::Rep { inner, min, max } => rep_matches(inner, *min, *max, w),
    }
}

fn concat_matches<T: Clone + PartialOrd>(items: &[Regex<T>], w: &[T]) -> bool {
    let Some((first, rest)) = items.split_first() else {
        return w.is_empty();
    };
    (0..=w.len()).any(|k| regex_matches(first, &w[..k]) && concat_matches(rest, &w[k..]))
}

fn star_matches<T: Clone + PartialOrd>(inner: &Regex<T>, w: &[T]) -> bool {
    // Non-empty chunks only: ε-chunks never extend the match and would
    // loop forever.
    w.is_empty()
        || (1..=w.len()).any(|k| regex_matches(inner, &w[..k]) && star_matches(inner, &w[k..]))
}

fn rep_matches<T: Clone + PartialOrd>(
    inner: &Regex<T>,
    min: u32,
    max: Option<u32>,
    w: &[T],
) -> bool {
    if let Some(m) = max
        && m < min
    {
        return false;
    }
    if w.is_empty() {
        // `inner` matching ε lets us pad up to any remaining `min`.
        return min == 0 || regex_matches(inner, w);
    }
    if max == Some(0) {
        return false;
    }
    (1..=w.len()).any(|k| {
        regex_matches(inner, &w[..k])
            && rep_matches(
                inner,
                min.saturating_sub(1),
                max.map(|m| m.saturating_sub(1)),
                &w[k..],
            )
    })
}

fn class_contains<T: PartialOrd>(c: &Class<T>, x: &T) -> bool {
    let inside = c.ranges.iter().any(|r| r.lo <= *x && *x <= r.hi);
    inside != c.negated
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn lit(b: u8) -> Regex<u8> {
        Regex::Lit(b)
    }

    /// S → a S b | ε — the classic aⁿbⁿ grammar over bytes.
    fn anbn() -> (Cfg<u8>, NtId) {
        let mut cfg = Cfg::new();
        let s = cfg.add_nt("S");
        cfg.add_prod(
            s,
            vec![Seg::term(lit(b'a')), Seg::nt(s), Seg::term(lit(b'b'))],
        );
        cfg.add_prod(s, vec![]);
        (cfg, s)
    }

    /// A → a B | ε ; B → b A. L(A) = (ab)*, L(B) = b(ab)*.
    fn mutual() -> (Cfg<u8>, NtId, NtId) {
        let mut cfg = Cfg::new();
        let a = cfg.add_nt("A");
        let b = cfg.add_nt("B");
        cfg.add_prod(a, vec![Seg::term(lit(b'a')), Seg::nt(b)]);
        cfg.add_prod(a, vec![]);
        cfg.add_prod(b, vec![Seg::term(lit(b'b')), Seg::nt(a)]);
        (cfg, a, b)
    }

    #[test]
    fn builder_and_lookup() {
        let (cfg, s) = anbn();
        assert_eq!(cfg.validate(), Ok(()));
        assert_eq!(cfg.lookup("S"), Some(s));
        assert_eq!(cfg.lookup("T"), None);
        assert_eq!(cfg.nt_name(s), Some("S"));
        assert_eq!(cfg.num_nts(), 1);

        let mut cfg = cfg;
        assert_eq!(cfg.get_or_add_nt("S"), s);
        let t = cfg.get_or_add_nt("T");
        assert_ne!(t, s);
        assert_eq!(cfg.lookup("T"), Some(t));
    }

    #[test]
    fn validate_rejects_out_of_range_refs() {
        let mut cfg: Cfg<u8> = Cfg::new();
        let s = cfg.add_nt("S");
        cfg.add_prod(s, vec![Seg::nt(NtId(7))]);
        assert_eq!(
            cfg.validate(),
            Err(CfgError::NonTermOutOfRange {
                prod: 0,
                seg: 0,
                nt: 7,
                len: 1,
            }),
        );

        let mut cfg: Cfg<u8> = Cfg::new();
        cfg.add_nt("S");
        cfg.add_prod(NtId(3), vec![]);
        assert_eq!(
            cfg.validate(),
            Err(CfgError::LhsOutOfRange {
                prod: 0,
                nt: 3,
                len: 1,
            }),
        );
    }

    #[test]
    fn production_order_is_insertion_order() {
        // The global production order becomes the kernel clause order, so
        // pin that add_prod indices and productions() agree and interleaved
        // lhs values do not get grouped.
        let mut cfg: Cfg<u8> = Cfg::new();
        let a = cfg.add_nt("A");
        let b = cfg.add_nt("B");
        let i0 = cfg.add_prod(a, vec![Seg::term(lit(b'x'))]);
        let i1 = cfg.add_prod(b, vec![Seg::term(lit(b'y'))]);
        let i2 = cfg.add_prod(a, vec![]);
        assert_eq!((i0, i1, i2), (0, 1, 2));
        let lhss: Vec<NtId> = cfg.productions().iter().map(|p| p.lhs).collect();
        assert_eq!(lhss, vec![a, b, a]);
        let of_a: Vec<usize> = cfg.productions_of(a).map(|(i, _)| i).collect();
        assert_eq!(of_a, vec![0, 2]);
        let of_b: Vec<usize> = cfg.productions_of(b).map(|(i, _)| i).collect();
        assert_eq!(of_b, vec![1]);
    }

    #[test]
    fn nullable_set_basics() {
        let (cfg, s) = anbn();
        assert_eq!(cfg.nullable_set(), vec![true]);
        assert!(cfg.nullable_nt(s));

        let (cfg, a, b) = mutual();
        // A has the ε-production; B always consumes a `b`.
        assert_eq!(cfg.nullable_set(), vec![true, false]);
        assert!(cfg.nullable_nt(a));
        assert!(!cfg.nullable_nt(b));
    }

    #[test]
    fn nullable_via_term_regex_and_propagation() {
        // C → (a*) D ; D → ε: nullable through both a nullable Term
        // segment and a nullable NonTerm segment.
        let mut cfg: Cfg<u8> = Cfg::new();
        let c = cfg.add_nt("C");
        let d = cfg.add_nt("D");
        cfg.add_prod(c, vec![Seg::term(lit(b'a').star()), Seg::nt(d)]);
        cfg.add_prod(d, vec![]);
        assert_eq!(cfg.nullable_set(), vec![true, true]);

        // E → a: not nullable.
        let mut cfg: Cfg<u8> = Cfg::new();
        let e = cfg.add_nt("E");
        cfg.add_prod(e, vec![Seg::term(lit(b'a'))]);
        assert_eq!(cfg.nullable_set(), vec![false]);
    }

    #[test]
    fn left_recursion_direct() {
        // E → E + T | T ; T → x.
        let mut cfg: Cfg<u8> = Cfg::new();
        let e = cfg.add_nt("E");
        let t = cfg.add_nt("T");
        cfg.add_prod(e, vec![Seg::nt(e), Seg::term(lit(b'+')), Seg::nt(t)]);
        cfg.add_prod(e, vec![Seg::nt(t)]);
        cfg.add_prod(t, vec![Seg::term(lit(b'x'))]);
        let cycle = cfg.left_recursion().expect("E is left-recursive");
        assert_eq!(cycle, vec![e, e]);
    }

    #[test]
    fn left_recursion_indirect_through_nullable_prefix() {
        // A → N B x ; B → A ; N → ε: A reaches itself leftmost because N
        // is nullable. Cycle closes through A and B.
        let mut cfg: Cfg<u8> = Cfg::new();
        let a = cfg.add_nt("A");
        let b = cfg.add_nt("B");
        let n = cfg.add_nt("N");
        cfg.add_prod(a, vec![Seg::nt(n), Seg::nt(b), Seg::term(lit(b'x'))]);
        cfg.add_prod(b, vec![Seg::nt(a)]);
        cfg.add_prod(n, vec![]);
        let cycle = cfg
            .left_recursion()
            .expect("nullable-prefix left recursion");
        assert_eq!(cycle.first(), cycle.last());
        let names: Vec<&str> = cycle.iter().map(|&x| cfg.nt_name(x).unwrap()).collect();
        assert!(names.contains(&"A") && names.contains(&"B"), "{names:?}");
    }

    #[test]
    fn left_recursion_absent_on_right_recursion() {
        let (cfg, _) = anbn();
        assert_eq!(cfg.left_recursion(), None);
        let (cfg, _, _) = mutual();
        assert_eq!(cfg.left_recursion(), None);
        // A non-nullable leading Term blocks the edge: A → x A is fine.
        let mut cfg: Cfg<u8> = Cfg::new();
        let a = cfg.add_nt("A");
        cfg.add_prod(a, vec![Seg::term(lit(b'x')), Seg::nt(a)]);
        cfg.add_prod(a, vec![]);
        assert_eq!(cfg.left_recursion(), None);
    }

    #[test]
    fn naive_parse_anbn() {
        let (cfg, s) = anbn();
        for w in [&b""[..], b"ab", b"aabb", b"aaabbb"] {
            assert!(cfg.naive_parse(s, w), "expected accept: {w:?}");
        }
        for w in [&b"a"[..], b"b", b"ba", b"aab", b"abb", b"abab", b"aabbb"] {
            assert!(!cfg.naive_parse(s, w), "expected reject: {w:?}");
        }
    }

    #[test]
    fn naive_parse_mutual_recursion() {
        let (cfg, a, b) = mutual();
        for w in [&b""[..], b"ab", b"abab", b"ababab"] {
            assert!(cfg.naive_parse(a, w), "A should accept {w:?}");
        }
        for w in [&b"a"[..], b"b", b"ba", b"aba"] {
            assert!(!cfg.naive_parse(a, w), "A should reject {w:?}");
        }
        for w in [&b"b"[..], b"bab", b"babab"] {
            assert!(cfg.naive_parse(b, w), "B should accept {w:?}");
        }
        for w in [&b""[..], b"a", b"ab", b"bb"] {
            assert!(!cfg.naive_parse(b, w), "B should reject {w:?}");
        }
    }

    #[test]
    fn naive_parse_multi_letter_terminal_segments() {
        // Magic → \0asm Ver ; Ver → \x01\0\0\0 — regex terminals spanning
        // several bytes, WASM-preamble shaped.
        let mut cfg: Cfg<u8> = Cfg::new();
        let magic = cfg.add_nt("Magic");
        let ver = cfg.add_nt("Ver");
        cfg.add_prod(
            magic,
            vec![
                Seg::term(Regex::concat([lit(0x00), lit(b'a'), lit(b's'), lit(b'm')])),
                Seg::nt(ver),
            ],
        );
        cfg.add_prod(
            ver,
            vec![Seg::term(Regex::concat([
                lit(0x01),
                lit(0x00),
                lit(0x00),
                lit(0x00),
            ]))],
        );
        assert!(cfg.naive_parse(magic, b"\0asm\x01\0\0\0"));
        assert!(!cfg.naive_parse(magic, b"\0asm"));
        assert!(!cfg.naive_parse(magic, b"\0asm\x02\0\0\0"));
        assert!(cfg.naive_parse(ver, b"\x01\0\0\0"));
    }

    #[test]
    fn naive_parse_regex_operators_in_terminals() {
        // L → [0-9]+ (';' L)? — classes, plus, opt inside Term segments.
        let mut cfg: Cfg<u8> = Cfg::new();
        let l = cfg.add_nt("L");
        let digits =
            Regex::Class(Class::new(vec![crate::regex::ClassRange::new(b'0', b'9')])).plus();
        cfg.add_prod(l, vec![Seg::term(digits.clone())]);
        cfg.add_prod(l, vec![Seg::term(digits), Seg::term(lit(b';')), Seg::nt(l)]);
        for w in [&b"1"[..], b"42", b"1;2", b"10;20;30"] {
            assert!(cfg.naive_parse(l, w), "expected accept: {w:?}");
        }
        for w in [&b""[..], b";", b"1;", b";2", b"1;;2", b"a"] {
            assert!(!cfg.naive_parse(l, w), "expected reject: {w:?}");
        }
    }

    #[test]
    fn naive_parse_terminates_under_left_recursion() {
        // The in-progress guard makes the oracle total even on the
        // grammars it is documented as incomplete for.
        let mut cfg: Cfg<u8> = Cfg::new();
        let e = cfg.add_nt("E");
        cfg.add_prod(e, vec![Seg::nt(e), Seg::term(lit(b'+')), Seg::nt(e)]);
        cfg.add_prod(e, vec![Seg::term(lit(b'x'))]);
        assert!(cfg.left_recursion().is_some());
        assert!(cfg.naive_parse(e, b"x"));
        // No completeness claim on `x+x` here — just termination.
        let _ = cfg.naive_parse(e, b"x+x");
    }

    #[test]
    fn naive_parse_out_of_range_nt_rejects() {
        let (cfg, _) = anbn();
        assert!(!cfg.naive_parse(NtId(9), b""));
    }
}
