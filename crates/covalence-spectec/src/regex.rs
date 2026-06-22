//! Partial bridge between the SpecTec grammar AST and the
//! `covalence-grammar` proper-regex AST.
//!
//! The source language here is the **elaborated** SpecTec grammar
//! ([`spectec_ast::SpecTecSym`]) — the form emitted by the upstream OCaml
//! SpecTec compiler's S-expression backend, not the surface syntax in our
//! native parser.
//!
//! `SpecTecSym` is more general than a regular language: it has named
//! references ([`Var`](spectec_ast::SpecTecSym::Var)), attribute / capture
//! brackets ([`Attr`](spectec_ast::SpecTecSym::Attr)), and a parametric
//! length-iteration form ([`ListN`](spectec_ast::SpecTecIter::ListN)) whose
//! count is an arbitrary expression. None of those fit a proper regex.
//!
//! The two functions here handle that mismatch explicitly:
//!
//! - [`sym_to_regex`] returns a [`BridgeError`] for any construct outside
//!   the proper-regex subset.
//! - [`regex_to_sym`] also returns a [`BridgeError`] — it is total on
//!   positive regexes but rejects negated character classes, which
//!   `SpecTecSym` has no direct representation for.
//!
//! Character-class ranges round-trip through `SpecTecSym::Range`; positive
//! `Class` values with multiple ranges round-trip through `SpecTecSym::Alt`.
//! Bounded repetition `r{m,n}` is desugared into a sequence rather than
//! routed through `ListN`, because `ListN` carries a SpecTec expression
//! payload that has no obvious meaning when produced from a regex.
//!
//! When [`covalence-grammar`] grows other classes of grammar (CFGs, etc.),
//! the converse — accepting `Var` as a non-terminal reference — is the
//! natural next step. Until then, all bridges live here in this file.

use covalence_grammar::regex::{Class, ClassRange, Regex};
use spectec_ast::{SpecTecIter, SpecTecNum, SpecTecSym};

/// Reason a [`SpecTecSym`] sits outside the proper-regex subset, or a
/// [`Regex<char>`] outside the SpecTec subset.
#[derive(Debug, Clone, Eq, PartialEq, thiserror::Error)]
pub enum BridgeError {
    /// `SpecTecSym::Var` — a grammar reference. Not a regular construct;
    /// will be handled when CFG support lands.
    #[error("grammar reference `{name}` is not a regular construct")]
    GrammarRef { name: String },

    /// `SpecTecSym::Attr` — attaches a value to a sub-grammar. Captures
    /// are out of scope for proper regexes.
    #[error("attribute / capture is not a proper-regex construct")]
    Attr,

    /// `SpecTecIter::ListN` — parametric length iteration whose count is
    /// an arbitrary `SpecTecExp`. We don't try to interpret expressions
    /// here.
    #[error("`listn` (parametric length iteration) is not supported")]
    ListN,

    /// `SpecTecSym::Iter` with a non-empty `xes` (iteration-binding
    /// `dom` list). Those bind names visible in the surrounding rule and
    /// are not a regex feature.
    #[error("iteration with implicit `dom` bindings is not supported")]
    IterWithDom,

    /// A `SpecTecSym::Range` endpoint that isn't a scalar character.
    #[error("range endpoint is not a scalar character: {detail}")]
    BadRangeEndpoint { detail: String },

    /// A numeric literal that doesn't sit in the Unicode scalar value range.
    #[error("numeric literal {value} is not a Unicode scalar value")]
    BadNumLiteral { value: i64 },

    /// A numeric literal kind (rat / real) that isn't a character.
    #[error("non-integer numeric literal is not a character: {kind}")]
    BadNumKind { kind: &'static str },

    /// A `Text` literal used as a single-character endpoint (e.g. inside
    /// a `Range`) that does not contain exactly one character.
    #[error("text literal {value:?} cannot be used as a single character (length {len})")]
    NonScalarText { value: String, len: usize },

    /// A `Regex::Class` is negated; SpecTec has no direct negated-class
    /// form, so we refuse to invent one.
    #[error("negated character classes have no SpecTec representation")]
    NegatedClass,

    /// A numeric literal outside the byte range `0..=255`, encountered while
    /// reading a grammar over the **byte** alphabet.
    #[error("numeric literal {value} is not a byte (0..=255)")]
    BadByteLiteral { value: i64 },
}

// ============================================================================
// SpecTecSym → Regex<char>
// ============================================================================

/// Convert a `SpecTecSym` into a [`Regex<char>`] when it falls inside the
/// proper-regex subset. Returns a [`BridgeError`] otherwise.
pub fn sym_to_regex(sym: &SpecTecSym) -> Result<Regex<char>, BridgeError> {
    match sym {
        SpecTecSym::Var { x, .. } => Err(BridgeError::GrammarRef { name: x.clone() }),
        SpecTecSym::Num { n } => Ok(Regex::Lit(i64_to_char(*n)?)),
        SpecTecSym::Text { t } => Ok(text_to_regex(t)),
        SpecTecSym::Eps => Ok(Regex::Eps),
        SpecTecSym::Seq { gs } => {
            let mut items = Vec::with_capacity(gs.len());
            for g in gs {
                items.push(sym_to_regex(g)?);
            }
            Ok(Regex::concat(items))
        }
        SpecTecSym::Alt { gs } => {
            let mut items = Vec::with_capacity(gs.len());
            for g in gs {
                items.push(sym_to_regex(g)?);
            }
            Ok(Regex::alt(items))
        }
        SpecTecSym::Range { g1, g2 } => {
            let lo = endpoint_char(g1)?;
            let hi = endpoint_char(g2)?;
            let (lo, hi) = if lo <= hi { (lo, hi) } else { (hi, lo) };
            Ok(Regex::Class(Class::new(vec![ClassRange { lo, hi }])))
        }
        SpecTecSym::Iter { g1, it, xes } => {
            if !xes.is_empty() {
                return Err(BridgeError::IterWithDom);
            }
            let inner = sym_to_regex(g1)?;
            match it {
                SpecTecIter::Opt => Ok(inner.opt()),
                SpecTecIter::List => Ok(inner.star()),
                SpecTecIter::List1 => Ok(inner.plus()),
                SpecTecIter::ListN { .. } => Err(BridgeError::ListN),
            }
        }
        SpecTecSym::Attr { .. } => Err(BridgeError::Attr),
    }
}

fn i64_to_char(n: i64) -> Result<char, BridgeError> {
    let raw = u32::try_from(n).map_err(|_| BridgeError::BadNumLiteral { value: n })?;
    char::from_u32(raw).ok_or(BridgeError::BadNumLiteral { value: n })
}

fn text_to_regex(t: &str) -> Regex<char> {
    Regex::concat(t.chars().map(Regex::Lit))
}

/// Extract a single character from a `SpecTecSym` used as an endpoint of
/// a `Range`. Accepts `Num` (numeric codepoint) and `Text` of exactly one
/// character.
fn endpoint_char(sym: &SpecTecSym) -> Result<char, BridgeError> {
    match sym {
        SpecTecSym::Num { n } => i64_to_char(*n),
        SpecTecSym::Text { t } => {
            let mut iter = t.chars();
            let first = iter.next();
            let rest = iter.next();
            match (first, rest) {
                (Some(c), None) => Ok(c),
                _ => Err(BridgeError::NonScalarText {
                    value: t.clone(),
                    len: t.chars().count(),
                }),
            }
        }
        SpecTecSym::Var { x, .. } => Err(BridgeError::BadRangeEndpoint {
            detail: format!("grammar reference `{}`", x),
        }),
        other => Err(BridgeError::BadRangeEndpoint {
            detail: format!("{:?}", std::mem::discriminant(other)),
        }),
    }
}

// ============================================================================
// SpecTecSym → Regex<u8>  (the byte / binary-grammar reading)
// ============================================================================

/// Convert a `SpecTecSym` into a [`Regex<u8>`] when it falls inside the
/// proper-regex subset, reading it as a grammar over **bytes** — the natural
/// interpretation of WASM's *binary* (`B*`) grammars and the form that feeds
/// `covalence-hol`'s grammar → bytes-predicate compiler.
///
/// The differences from [`sym_to_regex`] (the `char` path) are exactly where
/// the alphabet bites:
///
/// - `Num { n }` must lie in `0..=255` (a single byte), else
///   [`BridgeError::BadByteLiteral`].
/// - `Text { t }` is expanded to its **UTF-8 byte sequence**, one `Lit` per
///   byte — so a multi-byte scalar becomes several byte literals (the right
///   thing for a binary format).
/// - `Range` endpoints are bytes (`0..=255`).
///
/// Everything else (`Eps`/`Seq`/`Alt`/`Iter`) maps structurally, and the same
/// non-regular constructs (`Var`/`Attr`/`ListN`/dom-binding iteration) are
/// rejected.
pub fn sym_to_regex_u8(sym: &SpecTecSym) -> Result<Regex<u8>, BridgeError> {
    match sym {
        SpecTecSym::Var { x, .. } => Err(BridgeError::GrammarRef { name: x.clone() }),
        SpecTecSym::Num { n } => Ok(Regex::Lit(i64_to_byte(*n)?)),
        SpecTecSym::Text { t } => Ok(Regex::concat(t.bytes().map(Regex::Lit))),
        SpecTecSym::Eps => Ok(Regex::Eps),
        SpecTecSym::Seq { gs } => {
            let mut items = Vec::with_capacity(gs.len());
            for g in gs {
                items.push(sym_to_regex_u8(g)?);
            }
            Ok(Regex::concat(items))
        }
        SpecTecSym::Alt { gs } => {
            let mut items = Vec::with_capacity(gs.len());
            for g in gs {
                items.push(sym_to_regex_u8(g)?);
            }
            Ok(Regex::alt(items))
        }
        SpecTecSym::Range { g1, g2 } => {
            let lo = endpoint_byte(g1)?;
            let hi = endpoint_byte(g2)?;
            let (lo, hi) = if lo <= hi { (lo, hi) } else { (hi, lo) };
            Ok(Regex::Class(Class::new(vec![ClassRange { lo, hi }])))
        }
        SpecTecSym::Iter { g1, it, xes } => {
            if !xes.is_empty() {
                return Err(BridgeError::IterWithDom);
            }
            let inner = sym_to_regex_u8(g1)?;
            match it {
                SpecTecIter::Opt => Ok(inner.opt()),
                SpecTecIter::List => Ok(inner.star()),
                SpecTecIter::List1 => Ok(inner.plus()),
                SpecTecIter::ListN { .. } => Err(BridgeError::ListN),
            }
        }
        SpecTecSym::Attr { .. } => Err(BridgeError::Attr),
    }
}

fn i64_to_byte(n: i64) -> Result<u8, BridgeError> {
    u8::try_from(n).map_err(|_| BridgeError::BadByteLiteral { value: n })
}

/// Extract a single byte from a `SpecTecSym` used as a `Range` endpoint.
/// Accepts `Num` in `0..=255` and `Text` of exactly one ASCII byte.
fn endpoint_byte(sym: &SpecTecSym) -> Result<u8, BridgeError> {
    match sym {
        SpecTecSym::Num { n } => i64_to_byte(*n),
        SpecTecSym::Text { t } if t.len() == 1 => Ok(t.as_bytes()[0]),
        SpecTecSym::Text { t } => Err(BridgeError::NonScalarText {
            value: t.clone(),
            len: t.len(),
        }),
        SpecTecSym::Var { x, .. } => Err(BridgeError::BadRangeEndpoint {
            detail: format!("grammar reference `{}`", x),
        }),
        other => Err(BridgeError::BadRangeEndpoint {
            detail: format!("{:?}", std::mem::discriminant(other)),
        }),
    }
}

// ============================================================================
// Regex<char> → SpecTecSym
// ============================================================================

/// Convert a [`Regex<char>`] into a `SpecTecSym`. Total except for
/// negated character classes, which `SpecTecSym` has no representation for.
///
/// The chosen encoding for each variant:
///
/// - `Empty` → empty `Alt { gs: [] }` (the empty disjunction).
/// - `Eps` → `Eps`.
/// - `Lit(c)` → `Num { n: c as u32 as i64 }`.
/// - `Class` → `Alt` of `Range`s (single-char ranges collapse to `Num`).
///   Negated classes are rejected.
/// - `Concat` / `Alt` → `Seq` / `Alt` recursively.
/// - `Star` / `Plus` / `Opt` → `Iter` with the matching `SpecTecIter`.
/// - `Rep { min, max }` → desugared to a sequence rather than `ListN`:
///   - `r{m,m}` → `Seq` of `m` copies of `r`.
///   - `r{m,n}` for `n > m` → `m` copies followed by `n − m` `Opt`s.
///   - `r{m,}` → `m` copies followed by `Star(r)`.
pub fn regex_to_sym(r: &Regex<char>) -> Result<SpecTecSym, BridgeError> {
    match r {
        Regex::Empty => Ok(SpecTecSym::Alt { gs: Vec::new() }),
        Regex::Eps => Ok(SpecTecSym::Eps),
        Regex::Lit(c) => Ok(char_to_num(*c)),
        Regex::Class(c) => class_to_sym(c),
        Regex::Concat(items) => {
            let mut gs = Vec::with_capacity(items.len());
            for it in items {
                gs.push(regex_to_sym(it)?);
            }
            Ok(SpecTecSym::Seq { gs })
        }
        Regex::Alt(items) => {
            let mut gs = Vec::with_capacity(items.len());
            for it in items {
                gs.push(regex_to_sym(it)?);
            }
            Ok(SpecTecSym::Alt { gs })
        }
        Regex::Star(inner) => Ok(SpecTecSym::Iter {
            g1: Box::new(regex_to_sym(inner)?),
            it: SpecTecIter::List,
            xes: Vec::new(),
        }),
        Regex::Plus(inner) => Ok(SpecTecSym::Iter {
            g1: Box::new(regex_to_sym(inner)?),
            it: SpecTecIter::List1,
            xes: Vec::new(),
        }),
        Regex::Opt(inner) => Ok(SpecTecSym::Iter {
            g1: Box::new(regex_to_sym(inner)?),
            it: SpecTecIter::Opt,
            xes: Vec::new(),
        }),
        Regex::Rep { inner, min, max } => rep_to_sym(inner, *min, *max),
    }
}

fn char_to_num(c: char) -> SpecTecSym {
    SpecTecSym::Num {
        n: i64::from(c as u32),
    }
}

fn class_to_sym(c: &Class<char>) -> Result<SpecTecSym, BridgeError> {
    if c.negated {
        return Err(BridgeError::NegatedClass);
    }
    let parts: Vec<SpecTecSym> = c
        .ranges
        .iter()
        .map(|r| {
            if r.lo == r.hi {
                char_to_num(r.lo)
            } else {
                SpecTecSym::Range {
                    g1: Box::new(char_to_num(r.lo)),
                    g2: Box::new(char_to_num(r.hi)),
                }
            }
        })
        .collect();
    match parts.len() {
        0 => Ok(SpecTecSym::Alt { gs: Vec::new() }),
        1 => Ok(parts.into_iter().next().expect("len == 1")),
        _ => Ok(SpecTecSym::Alt { gs: parts }),
    }
}

fn rep_to_sym(inner: &Regex<char>, min: u32, max: Option<u32>) -> Result<SpecTecSym, BridgeError> {
    let inner_sym = regex_to_sym(inner)?;
    let copies = |n: u32| -> Vec<SpecTecSym> { (0..n).map(|_| inner_sym.clone()).collect() };
    let opts = |n: u32| -> Vec<SpecTecSym> {
        (0..n)
            .map(|_| SpecTecSym::Iter {
                g1: Box::new(inner_sym.clone()),
                it: SpecTecIter::Opt,
                xes: Vec::new(),
            })
            .collect()
    };
    match max {
        Some(m) if m == min => Ok(seq_or_single(copies(min))),
        Some(m) => {
            let extra = m.checked_sub(min).expect("max >= min by smart ctor");
            let mut gs = copies(min);
            gs.extend(opts(extra));
            Ok(seq_or_single(gs))
        }
        None => {
            let mut gs = copies(min);
            gs.push(SpecTecSym::Iter {
                g1: Box::new(inner_sym),
                it: SpecTecIter::List,
                xes: Vec::new(),
            });
            Ok(seq_or_single(gs))
        }
    }
}

fn seq_or_single(gs: Vec<SpecTecSym>) -> SpecTecSym {
    match gs.len() {
        0 => SpecTecSym::Eps,
        1 => gs.into_iter().next().expect("len == 1"),
        _ => SpecTecSym::Seq { gs },
    }
}

/// Numeric-literal kind tag for diagnostics. (Used when `SpecTecExp::Num`
/// carries something other than an integer — not reachable from
/// `SpecTecSym::Num`, which is i64, but kept for parity with the error
/// variants the type can hold.)
#[allow(dead_code)]
const _: fn(&SpecTecNum) -> &'static str = num_kind;

fn num_kind(n: &SpecTecNum) -> &'static str {
    match n {
        SpecTecNum::Nat(_) => "nat",
        SpecTecNum::Int(_) => "int",
        SpecTecNum::Rat(_) => "rat",
        SpecTecNum::Real(_) => "real",
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use covalence_grammar::regex::parse_regex;

    fn lit(c: char) -> Regex<char> {
        Regex::Lit(c)
    }

    fn num(c: char) -> SpecTecSym {
        SpecTecSym::Num {
            n: i64::from(c as u32),
        }
    }

    // ---- sym_to_regex ----

    #[test]
    fn sym_eps_and_num() {
        assert_eq!(sym_to_regex(&SpecTecSym::Eps).unwrap(), Regex::Eps);
        assert_eq!(sym_to_regex(&num('a')).unwrap(), lit('a'));
    }

    #[test]
    fn sym_text_is_concat() {
        let sym = SpecTecSym::Text { t: "abc".into() };
        let r = sym_to_regex(&sym).unwrap();
        assert_eq!(r, Regex::Concat(vec![lit('a'), lit('b'), lit('c')]));
    }

    #[test]
    fn sym_alt_and_seq() {
        let sym = SpecTecSym::Alt {
            gs: vec![num('a'), num('b'), num('c')],
        };
        assert_eq!(
            sym_to_regex(&sym).unwrap(),
            Regex::Alt(vec![lit('a'), lit('b'), lit('c')]),
        );

        let sym = SpecTecSym::Seq {
            gs: vec![num('a'), num('b')],
        };
        assert_eq!(
            sym_to_regex(&sym).unwrap(),
            Regex::Concat(vec![lit('a'), lit('b')]),
        );
    }

    #[test]
    fn sym_range() {
        let sym = SpecTecSym::Range {
            g1: Box::new(num('a')),
            g2: Box::new(num('z')),
        };
        assert_eq!(
            sym_to_regex(&sym).unwrap(),
            Regex::Class(Class::new(vec![ClassRange { lo: 'a', hi: 'z' }])),
        );
    }

    #[test]
    fn sym_iter_kinds() {
        let base = || num('a');
        let star = SpecTecSym::Iter {
            g1: Box::new(base()),
            it: SpecTecIter::List,
            xes: Vec::new(),
        };
        assert_eq!(
            sym_to_regex(&star).unwrap(),
            Regex::Star(Box::new(lit('a')))
        );

        let plus = SpecTecSym::Iter {
            g1: Box::new(base()),
            it: SpecTecIter::List1,
            xes: Vec::new(),
        };
        assert_eq!(
            sym_to_regex(&plus).unwrap(),
            Regex::Plus(Box::new(lit('a')))
        );

        let opt = SpecTecSym::Iter {
            g1: Box::new(base()),
            it: SpecTecIter::Opt,
            xes: Vec::new(),
        };
        assert_eq!(sym_to_regex(&opt).unwrap(), Regex::Opt(Box::new(lit('a'))));
    }

    #[test]
    fn sym_rejects_var_attr_listn() {
        let sym = SpecTecSym::Var {
            x: "instr".into(),
            as1: vec![],
        };
        assert!(matches!(
            sym_to_regex(&sym),
            Err(BridgeError::GrammarRef { .. }),
        ));

        let sym = SpecTecSym::Attr {
            e: spectec_ast::SpecTecExp::Bool { b: true },
            g1: Box::new(num('a')),
        };
        assert!(matches!(sym_to_regex(&sym), Err(BridgeError::Attr)));

        let sym = SpecTecSym::Iter {
            g1: Box::new(num('a')),
            it: SpecTecIter::ListN {
                e: vec![],
                xo: vec![],
            },
            xes: Vec::new(),
        };
        assert!(matches!(sym_to_regex(&sym), Err(BridgeError::ListN)));
    }

    #[test]
    fn sym_rejects_iter_with_dom() {
        let sym = SpecTecSym::Iter {
            g1: Box::new(num('a')),
            it: SpecTecIter::List,
            xes: vec![spectec_ast::SpecTecIterExp::Dom {
                x: "i".into(),
                e: spectec_ast::SpecTecExp::Var { id: "n".into() },
            }],
        };
        assert!(matches!(sym_to_regex(&sym), Err(BridgeError::IterWithDom)));
    }

    // ---- regex_to_sym ----

    #[test]
    fn regex_to_sym_basic() {
        assert_eq!(regex_to_sym(&Regex::Eps).unwrap(), SpecTecSym::Eps);
        assert_eq!(regex_to_sym(&lit('a')).unwrap(), num('a'));
        assert_eq!(
            regex_to_sym(&Regex::Empty).unwrap(),
            SpecTecSym::Alt { gs: vec![] },
        );
    }

    #[test]
    fn regex_to_sym_iter() {
        let r = lit('a').star();
        let sym = regex_to_sym(&r).unwrap();
        assert_eq!(
            sym,
            SpecTecSym::Iter {
                g1: Box::new(num('a')),
                it: SpecTecIter::List,
                xes: vec![],
            },
        );
    }

    #[test]
    fn regex_to_sym_class() {
        let c = Class::new(vec![
            ClassRange { lo: 'a', hi: 'z' },
            ClassRange { lo: '_', hi: '_' },
        ]);
        let sym = regex_to_sym(&Regex::Class(c)).unwrap();
        assert_eq!(
            sym,
            SpecTecSym::Alt {
                gs: vec![
                    SpecTecSym::Range {
                        g1: Box::new(num('a')),
                        g2: Box::new(num('z')),
                    },
                    num('_'),
                ],
            },
        );
    }

    #[test]
    fn regex_to_sym_rejects_negated_class() {
        let c = Class::negated(vec![ClassRange { lo: 'a', hi: 'z' }]);
        assert!(matches!(
            regex_to_sym(&Regex::Class(c)),
            Err(BridgeError::NegatedClass),
        ));
    }

    #[test]
    fn regex_to_sym_rep_fixed() {
        let r = lit('a').rep(3, Some(3));
        let sym = regex_to_sym(&r).unwrap();
        assert_eq!(
            sym,
            SpecTecSym::Seq {
                gs: vec![num('a'), num('a'), num('a')],
            },
        );
    }

    #[test]
    fn regex_to_sym_rep_open() {
        let r = lit('a').rep(2, None);
        let sym = regex_to_sym(&r).unwrap();
        assert_eq!(
            sym,
            SpecTecSym::Seq {
                gs: vec![
                    num('a'),
                    num('a'),
                    SpecTecSym::Iter {
                        g1: Box::new(num('a')),
                        it: SpecTecIter::List,
                        xes: vec![],
                    },
                ],
            },
        );
    }

    #[test]
    fn regex_to_sym_rep_bounded() {
        let r = lit('a').rep(1, Some(3));
        let sym = regex_to_sym(&r).unwrap();
        let opt_a = SpecTecSym::Iter {
            g1: Box::new(num('a')),
            it: SpecTecIter::Opt,
            xes: vec![],
        };
        assert_eq!(
            sym,
            SpecTecSym::Seq {
                gs: vec![num('a'), opt_a.clone(), opt_a],
            },
        );
    }

    // ---- round-trip ----

    #[test]
    fn round_trip_supported_subset() {
        for src in ["abc", "a|b|c", "a*", "a+", "a?", "(?:ab)*", "[a-z]"] {
            let r1 = parse_regex(src).unwrap();
            let sym = regex_to_sym(&r1).unwrap();
            let r2 = sym_to_regex(&sym).unwrap();
            assert_eq!(r1, r2, "round-trip failed for {:?}", src);
        }
    }

    // ---- sym_to_regex_u8 (the byte path) ----
    //
    // These drive off the S-expression parser (`crate::parse::parse_sym`), so
    // the SpecTec grammar symbols read the way the OCaml backend dumps them.

    fn u8_of(sexpr: &str) -> Result<Regex<u8>, BridgeError> {
        let sym = crate::parse::parse_sym(sexpr).expect("parse sym");
        sym_to_regex_u8(&sym)
    }

    #[test]
    fn sym_u8_num_byte_and_range() {
        assert_eq!(u8_of("(num 0x0B)").unwrap(), Regex::Lit(0x0Bu8));
        assert_eq!(
            u8_of("(range (num 0x00) (num 0x7F))").unwrap(),
            Regex::Class(Class::new(vec![ClassRange { lo: 0x00, hi: 0x7F }])),
        );
    }

    #[test]
    fn sym_u8_text_is_utf8_bytes() {
        // A multi-letter terminal expands to one byte literal per byte —
        // "abc" => byte 'a', byte 'b', byte 'c'. This is the common case:
        // WASM grammars use multi-char `(text ...)` terminals throughout
        // (e.g. "align=", "array.copy").
        assert_eq!(
            u8_of(r#"(text "abc")"#).unwrap(),
            Regex::concat([Regex::Lit(b'a'), Regex::Lit(b'b'), Regex::Lit(b'c')]),
        );
        // A two-byte UTF-8 scalar likewise expands to its two byte literals.
        assert_eq!(
            u8_of(r#"(text "é")"#).unwrap(),
            Regex::concat([Regex::Lit(0xC3u8), Regex::Lit(0xA9u8)]),
        );
    }

    #[test]
    fn sym_u8_rejects_out_of_byte_range() {
        assert!(matches!(
            u8_of("(num 256)"),
            Err(BridgeError::BadByteLiteral { value: 256 }),
        ));
    }

    #[test]
    fn sym_u8_iter_and_seq() {
        // `0x80* 0x0B` — a star of one byte followed by a literal byte.
        assert_eq!(
            u8_of("(seq (iter (num 0x80) list) (num 0x0B))").unwrap(),
            Regex::concat([Regex::Lit(0x80u8).star(), Regex::Lit(0x0Bu8)]),
        );
    }
}
