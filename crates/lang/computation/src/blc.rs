//! Tromp's binary lambda calculus.
//!
//! Terms use zero-based de Bruijn indices. Their wire representation is the
//! prefix-free code `00 M` for abstraction, `01 M N` for application, and
//! `1^(n+1) 0` for variable `n`.
//!
//! @covalence-api {"id":"A0012","title":"Binary lambda calculus","status":"experimental","dependsOn":["A0009","A0010"]}

use core::fmt;

use crate::encoding::{BitDecode, BitEncode, DecodeError as CodecError, Decoder};
use crate::execution::TransitionSystem;
use covalence_kernel_data::BitsSyntax;

/// Representation-independent BLC operations.
///
/// The v1 backend is [`DeBruijn`]. This trait keeps consumers independent of
/// that choice while preserving the distinction between host reference
/// computation and proof-bearing laws (none are supplied here).
pub trait BlcModel {
    type Term: Clone + PartialEq + Eq;
    type DecodeError;

    fn variable(&self, index: usize) -> Self::Term;
    fn abstraction(&self, body: Self::Term) -> Self::Term;
    fn application(&self, function: Self::Term, argument: Self::Term) -> Self::Term;
    fn decode(&self, code: &[bool]) -> Result<Self::Term, Self::DecodeError>;
    fn encode(&self, term: &Self::Term) -> Vec<bool>;
    fn is_closed(&self, term: &Self::Term) -> bool;
    fn shift(&self, term: &Self::Term, amount: isize, cutoff: usize) -> Self::Term;
    fn substitute(
        &self,
        term: &Self::Term,
        variable: usize,
        replacement: &Self::Term,
    ) -> Self::Term;
    fn normal_order_step(&self, term: &Self::Term) -> Option<Self::Term>;

    fn is_well_formed_code(&self, code: &[bool]) -> bool {
        self.decode(code).is_ok()
    }
}

/// Capability for lowering a BLC model's canonical code through A0010.
pub trait BlcBitsEncoding<L: BitsSyntax>: BlcModel {
    fn encode_in(&self, logic: &L, term: &Self::Term) -> Result<L::Term, L::Error> {
        logic.bits_literal(&self.encode(term))
    }
}

impl<L: BitsSyntax, M: BlcModel> BlcBitsEncoding<L> for M {}

/// Zero-based de Bruijn reference backend with Tromp's canonical encoding.
#[derive(Clone, Copy, Debug, Default)]
pub struct DeBruijn;

impl BlcModel for DeBruijn {
    type Term = Term;
    type DecodeError = DecodeError;

    fn variable(&self, index: usize) -> Term {
        Term::var(index)
    }

    fn abstraction(&self, body: Term) -> Term {
        Term::abs(body)
    }

    fn application(&self, function: Term, argument: Term) -> Term {
        Term::app(function, argument)
    }

    fn decode(&self, code: &[bool]) -> Result<Term, DecodeError> {
        Term::decode(code)
    }

    fn encode(&self, term: &Term) -> Vec<bool> {
        term.encode()
    }

    fn is_closed(&self, term: &Term) -> bool {
        term.is_closed()
    }

    fn shift(&self, term: &Term, amount: isize, cutoff: usize) -> Term {
        term.shift(amount, cutoff)
    }

    fn substitute(&self, term: &Term, variable: usize, replacement: &Term) -> Term {
        term.substitute(variable, replacement)
    }

    fn normal_order_step(&self, term: &Term) -> Option<Term> {
        term.beta_step()
    }
}

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

    /// Shifts free de Bruijn indices at or above `cutoff`.
    ///
    /// A negative amount is accepted only when every affected index remains
    /// nonnegative. This precondition is maintained by [`Self::substitute_top`].
    pub fn shift(&self, amount: isize, cutoff: usize) -> Self {
        shift(self, amount, cutoff)
    }

    /// Capture-avoiding substitution for a free de Bruijn variable.
    pub fn substitute(&self, variable: usize, replacement: &Self) -> Self {
        substitute(self, variable, replacement, 0)
    }

    /// Substitutes an argument for index zero in an abstraction body.
    pub fn substitute_top(argument: &Self, body: &Self) -> Self {
        substitute_top(argument, body)
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
    use covalence_hol_logic::Logic;
    use covalence_kernel_data::BitSyntax;

    fn bits(text: &str) -> Vec<bool> {
        text.bytes().map(|byte| byte == b'1').collect()
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    struct TestLogic;

    impl Logic for TestLogic {
        type Kind = ();
        type Type = &'static str;
        type Term = Vec<bool>;
        type Thm = ();
        type Error = core::convert::Infallible;
    }

    impl BitSyntax for TestLogic {
        fn bit_type(&self) -> &'static str {
            "bit"
        }
        fn bit_false(&self) -> Vec<bool> {
            vec![false]
        }
        fn bit_true(&self) -> Vec<bool> {
            vec![true]
        }
    }

    impl BitsSyntax for TestLogic {
        fn bits_type(&self) -> &'static str {
            "bits"
        }
        fn bits_empty(&self) -> Vec<bool> {
            vec![]
        }
        fn bits_literal(&self, bits: &[bool]) -> Result<Vec<bool>, Self::Error> {
            Ok(bits.to_vec())
        }
    }

    #[test]
    fn model_api_stacks_encoding_over_a0010() {
        let model = DeBruijn;
        let identity = model.abstraction(model.variable(0));
        assert!(model.is_closed(&identity));
        assert_eq!(
            model.encode_in(&TestLogic, &identity).unwrap(),
            bits("0010")
        );
        assert_eq!(model.decode(&model.encode(&identity)).unwrap(), identity);
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
