//! Tromp's binary lambda calculus.
//!
//! Terms use zero-based de Bruijn indices. Their wire representation is the
//! prefix-free code `00 M` for abstraction, `01 M N` for application, and
//! `1^(n+1) 0` for variable `n`.

use core::fmt;

use crate::encoding::{BitDecode, BitEncode, DecodeError as CodecError, Decoder};
use crate::execution::TransitionSystem;

/// An untyped lambda term using zero-based de Bruijn indices.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Term {
    Var(usize),
    Abs(Box<Term>),
    App(Box<Term>, Box<Term>),
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
                DecodeError::VariableIndexOverflow { offset: inner } => CodecError::Overflow {
                    offset: offset + inner,
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

/// Leftmost-outermost beta reduction as a deterministic transition system.
#[derive(Clone, Copy, Debug, Default)]
pub struct NormalOrder;

impl TransitionSystem for NormalOrder {
    type State = Term;
    type Outcome = Term;
    type Error = core::convert::Infallible;

    fn halted(&self, state: &Term) -> Result<Option<Term>, Self::Error> {
        Ok(state.beta_step().is_none().then(|| state.clone()))
    }

    fn transition(&self, state: Term) -> Result<Term, Self::Error> {
        Ok(state.beta_step().unwrap_or(state))
    }
}

impl Term {
    pub fn var(index: usize) -> Self {
        Self::Var(index)
    }

    pub fn abs(body: Self) -> Self {
        Self::Abs(Box::new(body))
    }

    pub fn app(function: Self, argument: Self) -> Self {
        Self::App(Box::new(function), Box::new(argument))
    }

    /// Encodes this term using Tromp's binary lambda calculus code.
    pub fn encode(&self) -> Vec<bool> {
        let mut bits = Vec::new();
        self.encode_into(&mut bits);
        bits
    }

    pub fn encode_into(&self, output: &mut Vec<bool>) {
        match self {
            Self::Abs(body) => {
                output.extend([false, false]);
                body.encode_into(output);
            }
            Self::App(function, argument) => {
                output.extend([false, true]);
                function.encode_into(output);
                argument.encode_into(output);
            }
            Self::Var(index) => {
                output.extend(core::iter::repeat_n(true, index.saturating_add(1)));
                output.push(false);
            }
        }
    }

    /// Decodes one term, returning it and the unused suffix.
    pub fn decode_prefix(bits: &[bool]) -> Result<(Self, &[bool]), DecodeError> {
        let mut cursor = 0;
        let term = decode_at(bits, &mut cursor)?;
        Ok((term, &bits[cursor..]))
    }

    /// Decodes exactly one term and rejects trailing bits.
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

    /// Performs one leftmost-outermost beta-reduction.
    pub fn beta_step(&self) -> Option<Self> {
        match self {
            Self::App(function, argument) => {
                if let Self::Abs(body) = function.as_ref() {
                    return Some(substitute_top(argument, body));
                }
                function
                    .beta_step()
                    .map(|next| Self::app(next, argument.as_ref().clone()))
                    .or_else(|| {
                        argument
                            .beta_step()
                            .map(|next| Self::app(function.as_ref().clone(), next))
                    })
            }
            Self::Abs(body) => body.beta_step().map(Self::abs),
            Self::Var(_) => None,
        }
    }

    /// Tests whether every variable is bound by an enclosing abstraction.
    pub fn is_closed(&self) -> bool {
        fn go(term: &Term, depth: usize) -> bool {
            match term {
                Term::Var(index) => *index < depth,
                Term::Abs(body) => go(body, depth.saturating_add(1)),
                Term::App(function, argument) => go(function, depth) && go(argument, depth),
            }
        }
        go(self, 0)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DecodeError {
    UnexpectedEnd { offset: usize },
    VariableIndexOverflow { offset: usize },
    TrailingBits { count: usize },
}

impl fmt::Display for DecodeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnexpectedEnd { offset } => {
                write!(f, "unexpected end of binary lambda code at bit {offset}")
            }
            Self::VariableIndexOverflow { offset } => {
                write!(f, "variable index overflows usize at bit {offset}")
            }
            Self::TrailingBits { count } => write!(f, "{count} trailing bit(s) after term"),
        }
    }
}

impl std::error::Error for DecodeError {}

fn decode_at(bits: &[bool], cursor: &mut usize) -> Result<Term, DecodeError> {
    let first_offset = *cursor;
    let first = *bits
        .get(*cursor)
        .ok_or(DecodeError::UnexpectedEnd { offset: *cursor })?;
    *cursor += 1;
    if !first {
        let second = *bits
            .get(*cursor)
            .ok_or(DecodeError::UnexpectedEnd { offset: *cursor })?;
        *cursor += 1;
        if second {
            Ok(Term::app(
                decode_at(bits, cursor)?,
                decode_at(bits, cursor)?,
            ))
        } else {
            Ok(Term::abs(decode_at(bits, cursor)?))
        }
    } else {
        let mut ones = 1usize;
        loop {
            let bit = *bits
                .get(*cursor)
                .ok_or(DecodeError::UnexpectedEnd { offset: *cursor })?;
            *cursor += 1;
            if !bit {
                return Ok(Term::Var(ones - 1));
            }
            ones = ones
                .checked_add(1)
                .ok_or(DecodeError::VariableIndexOverflow {
                    offset: first_offset,
                })?;
        }
    }
}

fn shift(term: &Term, amount: isize, cutoff: usize) -> Term {
    match term {
        Term::Var(index) if *index >= cutoff => {
            let shifted = index
                .checked_add_signed(amount)
                .expect("capture-avoiding substitution preserves valid indices");
            Term::Var(shifted)
        }
        Term::Var(index) => Term::Var(*index),
        Term::Abs(body) => Term::abs(shift(body, amount, cutoff.saturating_add(1))),
        Term::App(function, argument) => Term::app(
            shift(function, amount, cutoff),
            shift(argument, amount, cutoff),
        ),
    }
}

fn substitute(term: &Term, variable: usize, replacement: &Term, depth: usize) -> Term {
    match term {
        Term::Var(index) if *index == variable.saturating_add(depth) => {
            shift(replacement, depth as isize, 0)
        }
        Term::Var(index) => Term::Var(*index),
        Term::Abs(body) => Term::abs(substitute(
            body,
            variable,
            replacement,
            depth.saturating_add(1),
        )),
        Term::App(function, argument) => Term::app(
            substitute(function, variable, replacement, depth),
            substitute(argument, variable, replacement, depth),
        ),
    }
}

fn substitute_top(argument: &Term, body: &Term) -> Term {
    let lifted = shift(argument, 1, 0);
    shift(&substitute(body, 0, &lifted, 0), -1, 0)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn bits(text: &str) -> Vec<bool> {
        text.bytes().map(|byte| byte == b'1').collect()
    }

    #[test]
    fn known_tromp_codes() {
        let identity = Term::abs(Term::var(0));
        let constant = Term::abs(Term::abs(Term::var(1)));
        assert_eq!(identity.encode(), bits("0010"));
        assert_eq!(constant.encode(), bits("0000110"));
        assert_eq!(
            Term::app(identity.clone(), identity).encode(),
            bits("0100100010")
        );
    }

    #[test]
    fn round_trips_nested_term() {
        let term = Term::abs(Term::app(
            Term::var(0),
            Term::abs(Term::app(Term::var(1), Term::var(0))),
        ));
        assert_eq!(Term::decode(&term.encode()), Ok(term));
    }

    #[test]
    fn prefix_and_full_decoding_differ_on_suffix() {
        let code = bits("001011");
        let (term, suffix) = Term::decode_prefix(&code).unwrap();
        assert_eq!(term, Term::abs(Term::var(0)));
        assert_eq!(suffix, &[true, true]);
        assert_eq!(
            Term::decode(&code),
            Err(DecodeError::TrailingBits { count: 2 })
        );
    }

    #[test]
    fn truncated_codes_are_rejected() {
        assert_eq!(
            Term::decode(&bits("00")),
            Err(DecodeError::UnexpectedEnd { offset: 2 })
        );
        assert_eq!(
            Term::decode(&bits("111")),
            Err(DecodeError::UnexpectedEnd { offset: 3 })
        );
    }

    #[test]
    fn beta_reduction_is_leftmost_outermost() {
        let identity = Term::abs(Term::var(0));
        let value = Term::abs(Term::abs(Term::var(0)));
        assert_eq!(Term::app(identity, value.clone()).beta_step(), Some(value));
    }

    #[test]
    fn beta_reduction_avoids_capture() {
        // (λ. λ. 1) 0 → λ. 1: the free variable remains free.
        let term = Term::app(Term::abs(Term::abs(Term::var(1))), Term::var(0));
        assert_eq!(term.beta_step(), Some(Term::abs(Term::var(1))));
    }

    #[test]
    fn closedness_accounts_for_depth() {
        assert!(Term::abs(Term::var(0)).is_closed());
        assert!(!Term::abs(Term::var(1)).is_closed());
    }
}
