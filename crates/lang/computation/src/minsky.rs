//! Deterministic counter (Minsky) machines over natural-number registers.

use crate::encoding::{ByteDecode, ByteEncode, DecodeError as CodecError, Decoder};
use crate::execution::TransitionSystem;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Instruction {
    Increment {
        register: usize,
        next: usize,
    },
    Decrement {
        register: usize,
        if_positive: usize,
        if_zero: usize,
    },
    Halt,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Machine {
    pub initial: usize,
    pub program: Vec<Instruction>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Configuration {
    pub pc: usize,
    pub registers: Vec<u64>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Fault {
    ProgramCounterOutOfBounds,
    RegisterOutOfBounds,
    CounterOverflow,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Step {
    Advanced,
    Halted,
    Stuck(Fault),
}

impl Machine {
    pub fn initial_configuration(&self, registers: Vec<u64>) -> Configuration {
        Configuration {
            pc: self.initial,
            registers,
        }
    }

    /// Executes one instruction. `Halt` is a successful terminal instruction;
    /// malformed control flow, register access, and arithmetic are stuck.
    pub fn step(&self, configuration: &mut Configuration) -> Step {
        let Some(instruction) = self.program.get(configuration.pc) else {
            return Step::Stuck(Fault::ProgramCounterOutOfBounds);
        };
        match *instruction {
            Instruction::Halt => Step::Halted,
            Instruction::Increment { register, next } => {
                let Some(value) = configuration.registers.get_mut(register) else {
                    return Step::Stuck(Fault::RegisterOutOfBounds);
                };
                let Some(incremented) = value.checked_add(1) else {
                    return Step::Stuck(Fault::CounterOverflow);
                };
                *value = incremented;
                configuration.pc = next;
                if matches!(self.program.get(next), Some(Instruction::Halt)) {
                    Step::Halted
                } else {
                    Step::Advanced
                }
            }
            Instruction::Decrement {
                register,
                if_positive,
                if_zero,
            } => {
                let Some(value) = configuration.registers.get_mut(register) else {
                    return Step::Stuck(Fault::RegisterOutOfBounds);
                };
                configuration.pc = if *value == 0 {
                    if_zero
                } else {
                    *value -= 1;
                    if_positive
                };
                if matches!(self.program.get(configuration.pc), Some(Instruction::Halt)) {
                    Step::Halted
                } else {
                    Step::Advanced
                }
            }
        }
    }
}

impl TransitionSystem for Machine {
    type State = Configuration;
    type Outcome = Configuration;
    type Error = Fault;

    fn halted(&self, state: &Configuration) -> Result<Option<Configuration>, Fault> {
        match self.program.get(state.pc) {
            Some(Instruction::Halt) => Ok(Some(state.clone())),
            Some(_) => Ok(None),
            None => Err(Fault::ProgramCounterOutOfBounds),
        }
    }

    fn transition(&self, mut state: Configuration) -> Result<Configuration, Fault> {
        match self.step(&mut state) {
            Step::Advanced | Step::Halted => Ok(state),
            Step::Stuck(fault) => Err(fault),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DecodeError {
    UnexpectedEnd,
    Overflow,
    NonCanonicalVarint,
    InvalidTag,
    TrailingBytes,
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

fn put_usize(value: usize, bytes: &mut Vec<u8>) {
    put_u64(value as u64, bytes);
}

fn get_usize(bytes: &[u8], cursor: &mut usize) -> Result<usize, DecodeError> {
    usize::try_from(get_u64(bytes, cursor)?).map_err(|_| DecodeError::Overflow)
}

impl Machine {
    pub fn encode(&self) -> Vec<u8> {
        let mut bytes = Vec::new();
        put_usize(self.initial, &mut bytes);
        put_usize(self.program.len(), &mut bytes);
        for instruction in &self.program {
            match *instruction {
                Instruction::Halt => bytes.push(0),
                Instruction::Increment { register, next } => {
                    bytes.push(1);
                    put_usize(register, &mut bytes);
                    put_usize(next, &mut bytes);
                }
                Instruction::Decrement {
                    register,
                    if_positive,
                    if_zero,
                } => {
                    bytes.push(2);
                    put_usize(register, &mut bytes);
                    put_usize(if_positive, &mut bytes);
                    put_usize(if_zero, &mut bytes);
                }
            }
        }
        bytes
    }

    pub fn decode(bytes: &[u8]) -> Result<Self, DecodeError> {
        let mut cursor = 0;
        let initial = get_usize(bytes, &mut cursor)?;
        let length = get_usize(bytes, &mut cursor)?;
        let mut program = Vec::new();
        program
            .try_reserve(length)
            .map_err(|_| DecodeError::Overflow)?;
        for _ in 0..length {
            let tag = *bytes.get(cursor).ok_or(DecodeError::UnexpectedEnd)?;
            cursor += 1;
            program.push(match tag {
                0 => Instruction::Halt,
                1 => Instruction::Increment {
                    register: get_usize(bytes, &mut cursor)?,
                    next: get_usize(bytes, &mut cursor)?,
                },
                2 => Instruction::Decrement {
                    register: get_usize(bytes, &mut cursor)?,
                    if_positive: get_usize(bytes, &mut cursor)?,
                    if_zero: get_usize(bytes, &mut cursor)?,
                },
                _ => return Err(DecodeError::InvalidTag),
            });
        }
        if cursor != bytes.len() {
            return Err(DecodeError::TrailingBytes);
        }
        Ok(Self { initial, program })
    }
}

impl ByteEncode for Machine {
    fn encode_bytes(&self) -> Vec<u8> {
        self.encode()
    }
}

impl ByteDecode for Machine {
    fn decode_bytes_from(input: &mut Decoder<'_, u8>) -> Result<Self, CodecError> {
        let offset = input.offset();
        let machine = Self::decode(input.remaining()).map_err(|_| CodecError::NonCanonical {
            offset,
            reason: "invalid Minsky machine encoding",
        })?;
        let remaining = input.remaining_len();
        input.take_exact(remaining)?;
        Ok(machine)
    }
}

impl Configuration {
    pub fn encode(&self) -> Vec<u8> {
        let mut bytes = Vec::new();
        put_usize(self.pc, &mut bytes);
        put_usize(self.registers.len(), &mut bytes);
        for &register in &self.registers {
            put_u64(register, &mut bytes);
        }
        bytes
    }

    pub fn decode(bytes: &[u8]) -> Result<Self, DecodeError> {
        let mut cursor = 0;
        let pc = get_usize(bytes, &mut cursor)?;
        let length = get_usize(bytes, &mut cursor)?;
        let mut registers = Vec::new();
        registers
            .try_reserve(length)
            .map_err(|_| DecodeError::Overflow)?;
        for _ in 0..length {
            registers.push(get_u64(bytes, &mut cursor)?);
        }
        if cursor != bytes.len() {
            return Err(DecodeError::TrailingBytes);
        }
        Ok(Self { pc, registers })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Moves register 0 into register 1, preserving neither the source nor
    // auxiliary storage: while r0 > 0 { r0 -= 1; r1 += 1 }.
    fn add_into_second() -> Machine {
        Machine {
            initial: 0,
            program: vec![
                Instruction::Decrement {
                    register: 0,
                    if_positive: 1,
                    if_zero: 2,
                },
                Instruction::Increment {
                    register: 1,
                    next: 0,
                },
                Instruction::Halt,
            ],
        }
    }

    #[test]
    fn transfers_counter() {
        let machine = add_into_second();
        let mut configuration = machine.initial_configuration(vec![3, 4]);
        while machine.step(&mut configuration) == Step::Advanced {}
        assert_eq!(machine.step(&mut configuration), Step::Halted);
        assert_eq!(configuration.registers, vec![0, 7]);
    }

    #[test]
    fn distinguishes_faults_from_halt() {
        let machine = add_into_second();
        let mut bad_register = machine.initial_configuration(vec![]);
        assert_eq!(
            machine.step(&mut bad_register),
            Step::Stuck(Fault::RegisterOutOfBounds)
        );
        let mut bad_pc = Configuration {
            pc: 99,
            registers: vec![],
        };
        assert_eq!(
            machine.step(&mut bad_pc),
            Step::Stuck(Fault::ProgramCounterOutOfBounds)
        );
    }

    #[test]
    fn codecs_are_round_trip_and_strict() {
        let machine = add_into_second();
        assert_eq!(Machine::decode(&machine.encode()), Ok(machine));
        let configuration = Configuration {
            pc: 2,
            registers: vec![0, 7],
        };
        assert_eq!(
            Configuration::decode(&configuration.encode()),
            Ok(configuration)
        );
        assert_eq!(
            Configuration::decode(&[0x80, 0, 0]),
            Err(DecodeError::NonCanonicalVarint)
        );
    }
}
