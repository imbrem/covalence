//! Deterministic, single-tape Turing machines.
//!
//! The tape is bi-infinite. `left` and `right` store cells nearest the head
//! last, so moving the head uses only `push` and `pop`.

use crate::encoding::{ByteDecode, ByteEncode, DecodeError as CodecError, Decoder};
use crate::execution::TransitionSystem;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Direction {
    Left,
    Right,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Transition<S, A> {
    pub state: S,
    pub read: A,
    pub write: A,
    pub direction: Direction,
    pub next: S,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Machine<S, A> {
    pub initial: S,
    pub halting: Vec<S>,
    pub blank: A,
    pub transitions: Vec<Transition<S, A>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Configuration<S, A> {
    pub state: S,
    pub left: Vec<A>,
    pub head: A,
    pub right: Vec<A>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Step {
    Advanced,
    Halted,
    Stuck,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MachineError {
    DuplicateTransition,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ExecutionFault {
    Stuck,
}

impl<S: Eq, A: Eq> Machine<S, A> {
    pub fn validate(&self) -> Result<(), MachineError> {
        for (index, transition) in self.transitions.iter().enumerate() {
            if self.transitions[..index]
                .iter()
                .any(|other| other.state == transition.state && other.read == transition.read)
            {
                return Err(MachineError::DuplicateTransition);
            }
        }
        Ok(())
    }
}

impl<S: Clone + Eq, A: Clone + Eq> Machine<S, A> {
    pub fn initial_configuration(&self, input: impl IntoIterator<Item = A>) -> Configuration<S, A> {
        let mut input = input.into_iter();
        let head = input.next().unwrap_or_else(|| self.blank.clone());
        let mut right: Vec<_> = input.collect();
        right.reverse();
        let mut configuration = Configuration {
            state: self.initial.clone(),
            left: Vec::new(),
            head,
            right,
        };
        configuration.normalize(&self.blank);
        configuration
    }

    /// Executes one transition. A halting state is distinct from a non-halting
    /// state for which no transition is defined.
    pub fn step(&self, configuration: &mut Configuration<S, A>) -> Step {
        if self.halting.contains(&configuration.state) {
            return Step::Halted;
        }
        let Some(transition) = self.transitions.iter().find(|transition| {
            transition.state == configuration.state && transition.read == configuration.head
        }) else {
            return Step::Stuck;
        };

        configuration.head = transition.write.clone();
        configuration.state = transition.next.clone();
        match transition.direction {
            Direction::Left => {
                configuration.right.push(configuration.head.clone());
                configuration.head = configuration
                    .left
                    .pop()
                    .unwrap_or_else(|| self.blank.clone());
            }
            Direction::Right => {
                configuration.left.push(configuration.head.clone());
                configuration.head = configuration
                    .right
                    .pop()
                    .unwrap_or_else(|| self.blank.clone());
            }
        }
        configuration.normalize(&self.blank);
        if self.halting.contains(&configuration.state) {
            Step::Halted
        } else {
            Step::Advanced
        }
    }
}

impl<S, A: Eq> Configuration<S, A> {
    pub fn normalize(&mut self, blank: &A) {
        while self.left.first() == Some(blank) {
            self.left.remove(0);
        }
        while self.right.first() == Some(blank) {
            self.right.remove(0);
        }
    }
}

/// Errors produced by the canonical `u64` machine/configuration codec.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DecodeError {
    UnexpectedEnd,
    Overflow,
    NonCanonicalVarint,
    InvalidTag,
    TrailingBytes,
    DuplicateTransition,
    NonCanonicalTape,
}

fn put_u64(mut value: u64, bytes: &mut Vec<u8>) {
    loop {
        let byte = (value & 0x7f) as u8;
        value >>= 7;
        bytes.push(byte | if value == 0 { 0 } else { 0x80 });
        if value == 0 {
            break;
        }
    }
}

fn get_u64(bytes: &[u8], cursor: &mut usize) -> Result<u64, DecodeError> {
    let start = *cursor;
    let mut value = 0_u64;
    for shift in (0..=63).step_by(7) {
        let byte = *bytes.get(*cursor).ok_or(DecodeError::UnexpectedEnd)?;
        *cursor += 1;
        if shift == 63 && byte > 1 {
            return Err(DecodeError::Overflow);
        }
        value |= u64::from(byte & 0x7f) << shift;
        if byte & 0x80 == 0 {
            let mut canonical = Vec::new();
            put_u64(value, &mut canonical);
            if &bytes[start..*cursor] != canonical.as_slice() {
                return Err(DecodeError::NonCanonicalVarint);
            }
            return Ok(value);
        }
    }
    Err(DecodeError::Overflow)
}

fn put_values(values: &[u64], bytes: &mut Vec<u8>) {
    put_u64(values.len() as u64, bytes);
    for &value in values {
        put_u64(value, bytes);
    }
}

fn get_values(bytes: &[u8], cursor: &mut usize) -> Result<Vec<u64>, DecodeError> {
    let length = usize::try_from(get_u64(bytes, cursor)?).map_err(|_| DecodeError::Overflow)?;
    let mut values = Vec::new();
    values
        .try_reserve(length)
        .map_err(|_| DecodeError::Overflow)?;
    for _ in 0..length {
        values.push(get_u64(bytes, cursor)?);
    }
    Ok(values)
}

impl Machine<u64, u64> {
    pub fn encode(&self) -> Vec<u8> {
        let mut bytes = Vec::new();
        put_u64(self.initial, &mut bytes);
        put_u64(self.blank, &mut bytes);
        put_values(&self.halting, &mut bytes);
        put_u64(self.transitions.len() as u64, &mut bytes);
        for transition in &self.transitions {
            put_u64(transition.state, &mut bytes);
            put_u64(transition.read, &mut bytes);
            put_u64(transition.write, &mut bytes);
            bytes.push(match transition.direction {
                Direction::Left => 0,
                Direction::Right => 1,
            });
            put_u64(transition.next, &mut bytes);
        }
        bytes
    }

    pub fn decode(bytes: &[u8]) -> Result<Self, DecodeError> {
        let mut cursor = 0;
        let initial = get_u64(bytes, &mut cursor)?;
        let blank = get_u64(bytes, &mut cursor)?;
        let halting = get_values(bytes, &mut cursor)?;
        let length =
            usize::try_from(get_u64(bytes, &mut cursor)?).map_err(|_| DecodeError::Overflow)?;
        let mut transitions = Vec::new();
        transitions
            .try_reserve(length)
            .map_err(|_| DecodeError::Overflow)?;
        for _ in 0..length {
            let state = get_u64(bytes, &mut cursor)?;
            let read = get_u64(bytes, &mut cursor)?;
            let write = get_u64(bytes, &mut cursor)?;
            let direction = match bytes.get(cursor) {
                Some(0) => Direction::Left,
                Some(1) => Direction::Right,
                Some(_) => return Err(DecodeError::InvalidTag),
                None => return Err(DecodeError::UnexpectedEnd),
            };
            cursor += 1;
            let next = get_u64(bytes, &mut cursor)?;
            transitions.push(Transition {
                state,
                read,
                write,
                direction,
                next,
            });
        }
        if cursor != bytes.len() {
            return Err(DecodeError::TrailingBytes);
        }
        let machine = Self {
            initial,
            halting,
            blank,
            transitions,
        };
        machine
            .validate()
            .map_err(|_| DecodeError::DuplicateTransition)?;
        Ok(machine)
    }
}

impl ByteEncode for Machine<u64, u64> {
    fn encode_bytes(&self) -> Vec<u8> {
        self.encode()
    }
}

impl ByteDecode for Machine<u64, u64> {
    fn decode_bytes_from(input: &mut Decoder<'_, u8>) -> Result<Self, CodecError> {
        let offset = input.offset();
        let machine = Self::decode(input.remaining()).map_err(|_| CodecError::NonCanonical {
            offset,
            reason: "invalid Turing machine encoding",
        })?;
        let remaining = input.remaining_len();
        input.take_exact(remaining)?;
        Ok(machine)
    }
}

impl Configuration<u64, u64> {
    pub fn encode(&self) -> Vec<u8> {
        let mut bytes = Vec::new();
        put_u64(self.state, &mut bytes);
        put_values(&self.left, &mut bytes);
        put_u64(self.head, &mut bytes);
        put_values(&self.right, &mut bytes);
        bytes
    }

    pub fn decode(bytes: &[u8], blank: u64) -> Result<Self, DecodeError> {
        let mut cursor = 0;
        let configuration = Self {
            state: get_u64(bytes, &mut cursor)?,
            left: get_values(bytes, &mut cursor)?,
            head: get_u64(bytes, &mut cursor)?,
            right: get_values(bytes, &mut cursor)?,
        };
        if cursor != bytes.len() {
            return Err(DecodeError::TrailingBytes);
        }
        if configuration.left.first() == Some(&blank) || configuration.right.first() == Some(&blank)
        {
            return Err(DecodeError::NonCanonicalTape);
        }
        Ok(configuration)
    }
}

impl<S: Clone + Eq, A: Clone + Eq> TransitionSystem for Machine<S, A> {
    type State = Configuration<S, A>;
    type Outcome = Configuration<S, A>;
    type Error = ExecutionFault;

    fn halted(&self, state: &Self::State) -> Result<Option<Self::Outcome>, Self::Error> {
        Ok(self.halting.contains(&state.state).then(|| state.clone()))
    }

    fn transition(&self, mut state: Self::State) -> Result<Self::State, Self::Error> {
        match self.step(&mut state) {
            Step::Advanced | Step::Halted => Ok(state),
            Step::Stuck => Err(ExecutionFault::Stuck),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn unary_increment() -> Machine<u64, u64> {
        Machine {
            initial: 0,
            halting: vec![1],
            blank: 0,
            transitions: vec![
                Transition {
                    state: 0,
                    read: 1,
                    write: 1,
                    direction: Direction::Right,
                    next: 0,
                },
                Transition {
                    state: 0,
                    read: 0,
                    write: 1,
                    direction: Direction::Right,
                    next: 1,
                },
            ],
        }
    }

    #[test]
    fn increments_unary_input() {
        let machine = unary_increment();
        let mut configuration = machine.initial_configuration([1, 1, 1]);
        assert_eq!(machine.step(&mut configuration), Step::Advanced);
        assert_eq!(machine.step(&mut configuration), Step::Advanced);
        assert_eq!(machine.step(&mut configuration), Step::Advanced);
        assert_eq!(machine.step(&mut configuration), Step::Halted);
        assert_eq!(configuration.left, vec![1, 1, 1, 1]);
        assert_eq!(machine.step(&mut configuration), Step::Halted);
    }

    #[test]
    fn distinguishes_stuck_and_halted() {
        let machine = unary_increment();
        let mut stuck = Configuration {
            state: 9,
            left: vec![],
            head: 0,
            right: vec![],
        };
        assert_eq!(machine.step(&mut stuck), Step::Stuck);
    }

    #[test]
    fn codecs_are_round_trip_and_strict() {
        let machine = unary_increment();
        assert_eq!(Machine::decode(&machine.encode()), Ok(machine));
        assert_eq!(
            Machine::decode(&[0x80, 0, 0, 0, 0]),
            Err(DecodeError::NonCanonicalVarint)
        );

        let configuration = Configuration {
            state: 2,
            left: vec![1],
            head: 0,
            right: vec![1, 2],
        };
        assert_eq!(
            Configuration::decode(&configuration.encode(), 0),
            Ok(configuration)
        );
    }
}
