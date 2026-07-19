//! The SKI combinator calculus.
//!
//! Closed terms have a canonical prefix bit encoding chosen for this crate:
//! `S = 00`, `K = 01`, `I = 10`, and `Apply(x, y) = 11 encode(x) encode(y)`.
//! This is deliberately a simple independently decodable representation, not
//! a claim about a unique standard SKI encoding.

use core::fmt;

use crate::encoding::{BitDecode, BitEncode, DecodeError as CodecError, Decoder};
use crate::execution::TransitionSystem;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Term {
    S,
    K,
    I,
    Apply(Box<Term>, Box<Term>),
}

impl BitEncode for Term {
    fn encode_bits(&self) -> Vec<bool> {
        self.encode()
    }
}

impl BitDecode for Term {
    fn decode_bits_from(input: &mut Decoder<'_, bool>) -> Result<Self, CodecError> {
        let offset = input.offset();
        let (term, suffix) =
            Self::decode_prefix(input.remaining()).map_err(|error| match error {
                DecodeError::UnexpectedEnd { offset: inner } => CodecError::UnexpectedEnd {
                    offset: offset + inner,
                    needed: 1,
                },
                DecodeError::TrailingBits { .. } => {
                    unreachable!("prefix decoding permits a suffix")
                }
            })?;
        let consumed = input.remaining_len() - suffix.len();
        input.take_exact(consumed)?;
        Ok(term)
    }
}

/// Leftmost-outermost SKI contraction as a deterministic transition system.
#[derive(Clone, Copy, Debug, Default)]
pub struct Reduction;

impl TransitionSystem for Reduction {
    type State = Term;
    type Outcome = Term;
    type Error = core::convert::Infallible;

    fn halted(&self, state: &Term) -> Result<Option<Term>, Self::Error> {
        Ok(state.step().is_none().then(|| state.clone()))
    }

    fn transition(&self, state: Term) -> Result<Term, Self::Error> {
        Ok(state.step().unwrap_or(state))
    }
}

impl Term {
    pub fn apply(function: Self, argument: Self) -> Self {
        Self::Apply(Box::new(function), Box::new(argument))
    }

    pub fn encode(&self) -> Vec<bool> {
        let mut output = Vec::new();
        self.encode_into(&mut output);
        output
    }

    pub fn encode_into(&self, output: &mut Vec<bool>) {
        match self {
            Self::S => output.extend([false, false]),
            Self::K => output.extend([false, true]),
            Self::I => output.extend([true, false]),
            Self::Apply(function, argument) => {
                output.extend([true, true]);
                function.encode_into(output);
                argument.encode_into(output);
            }
        }
    }

    pub fn decode_prefix(bits: &[bool]) -> Result<(Self, &[bool]), DecodeError> {
        let mut cursor = 0;
        let term = decode_at(bits, &mut cursor)?;
        Ok((term, &bits[cursor..]))
    }

    pub fn decode(bits: &[bool]) -> Result<Self, DecodeError> {
        let (term, remainder) = Self::decode_prefix(bits)?;
        if remainder.is_empty() {
            Ok(term)
        } else {
            Err(DecodeError::TrailingBits {
                count: remainder.len(),
            })
        }
    }

    /// Performs one leftmost-outermost `S`, `K`, or `I` contraction.
    pub fn step(&self) -> Option<Self> {
        if let Some(contracted) = contract_root(self) {
            return Some(contracted);
        }
        match self {
            Self::Apply(function, argument) => function
                .step()
                .map(|next| Self::apply(next, argument.as_ref().clone()))
                .or_else(|| {
                    argument
                        .step()
                        .map(|next| Self::apply(function.as_ref().clone(), next))
                }),
            Self::S | Self::K | Self::I => None,
        }
    }
}

fn contract_root(term: &Term) -> Option<Term> {
    let Term::Apply(function, z) = term else {
        return None;
    };
    if matches!(function.as_ref(), Term::I) {
        return Some(z.as_ref().clone());
    }
    let Term::Apply(function, y) = function.as_ref() else {
        return None;
    };
    if matches!(function.as_ref(), Term::K) {
        return Some(y.as_ref().clone());
    }
    let Term::Apply(function, x) = function.as_ref() else {
        return None;
    };
    if matches!(function.as_ref(), Term::S) {
        return Some(Term::apply(
            Term::apply(x.as_ref().clone(), z.as_ref().clone()),
            Term::apply(y.as_ref().clone(), z.as_ref().clone()),
        ));
    }
    None
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DecodeError {
    UnexpectedEnd { offset: usize },
    TrailingBits { count: usize },
}

impl fmt::Display for DecodeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnexpectedEnd { offset } => {
                write!(f, "unexpected end of SKI code at bit {offset}")
            }
            Self::TrailingBits { count } => write!(f, "{count} trailing bit(s) after term"),
        }
    }
}

impl std::error::Error for DecodeError {}

fn decode_at(bits: &[bool], cursor: &mut usize) -> Result<Term, DecodeError> {
    let first = *bits
        .get(*cursor)
        .ok_or(DecodeError::UnexpectedEnd { offset: *cursor })?;
    *cursor += 1;
    let second = *bits
        .get(*cursor)
        .ok_or(DecodeError::UnexpectedEnd { offset: *cursor })?;
    *cursor += 1;
    match (first, second) {
        (false, false) => Ok(Term::S),
        (false, true) => Ok(Term::K),
        (true, false) => Ok(Term::I),
        (true, true) => Ok(Term::apply(
            decode_at(bits, cursor)?,
            decode_at(bits, cursor)?,
        )),
    }
}

/// An expression accepted by one-variable bracket abstraction.
///
/// `Bound` denotes the variable being abstracted. `Constant` can contain an
/// already-translated closed SKI term. Applying `abstract_bound` implements
/// `[x]x = I`, `[x]c = K c`, and `[x](p q) = S ([x]p) ([x]q)`. Repeated use
/// supplies a small, representation-independent seam for lambda-to-SKI
/// translation without coupling this module to a particular lambda AST.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BracketExpr {
    Bound,
    Constant(Term),
    Apply(Box<BracketExpr>, Box<BracketExpr>),
}

impl BracketExpr {
    pub fn apply(function: Self, argument: Self) -> Self {
        Self::Apply(Box::new(function), Box::new(argument))
    }
}

pub fn abstract_bound(expression: &BracketExpr) -> Term {
    match expression {
        BracketExpr::Bound => Term::I,
        BracketExpr::Constant(term) => Term::apply(Term::K, term.clone()),
        BracketExpr::Apply(function, argument) => Term::apply(
            Term::apply(Term::S, abstract_bound(function)),
            abstract_bound(argument),
        ),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn bits(text: &str) -> Vec<bool> {
        text.bytes().map(|byte| byte == b'1').collect()
    }

    #[test]
    fn canonical_encoding_round_trips() {
        let term = Term::apply(Term::apply(Term::S, Term::K), Term::I);
        assert_eq!(term.encode(), bits("1111000110"));
        assert_eq!(Term::decode(&term.encode()), Ok(term));
    }

    #[test]
    fn exact_decoder_rejects_suffix() {
        assert_eq!(
            Term::decode(&bits("0010")),
            Err(DecodeError::TrailingBits { count: 2 })
        );
        assert_eq!(
            Term::decode(&bits("11")),
            Err(DecodeError::UnexpectedEnd { offset: 2 })
        );
    }

    #[test]
    fn contracts_i_k_and_s() {
        let x = Term::K;
        let y = Term::S;
        let z = Term::I;
        assert_eq!(Term::apply(Term::I, x.clone()).step(), Some(x.clone()));
        assert_eq!(
            Term::apply(Term::apply(Term::K, x.clone()), y.clone()).step(),
            Some(x.clone())
        );
        assert_eq!(
            Term::apply(
                Term::apply(Term::apply(Term::S, x.clone()), y.clone()),
                z.clone()
            )
            .step(),
            Some(Term::apply(Term::apply(x, z.clone()), Term::apply(y, z)))
        );
    }

    #[test]
    fn reduction_is_leftmost_outermost() {
        let inner = Term::apply(Term::I, Term::S);
        let term = Term::apply(Term::I, inner.clone());
        assert_eq!(term.step(), Some(inner));
    }

    #[test]
    fn bracket_abstraction_builds_identity_and_application_law() {
        assert_eq!(abstract_bound(&BracketExpr::Bound), Term::I);
        let expression = BracketExpr::apply(BracketExpr::Bound, BracketExpr::Constant(Term::K));
        assert_eq!(
            abstract_bound(&expression),
            Term::apply(Term::apply(Term::S, Term::I), Term::apply(Term::K, Term::K))
        );
    }
}
