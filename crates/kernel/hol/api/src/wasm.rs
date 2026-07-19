//! First-class WebAssembly syntax, typing, and execution facts.
//!
//! This is deliberately a WebAssembly API, not a SpecTec API.  Public values
//! describe WebAssembly concepts and public facts identify the WebAssembly
//! relation they inhabit.  The native adapter owns the current SpecTec-derived
//! HOL environment privately; a future K-WASM adapter can implement the same
//! traits over these values without translating through SpecTec's AST.
//!
//! Host-side selection of a rule is not proof authority.  A successful method
//! returns the theorem produced by checked NativeHol replay, and every public
//! fact constructor rejects hypotheses.  There are no admitted rules here.

use covalence_core::{Error, Result, Term};
use covalence_hol_eval::EvalThm as Thm;
use covalence_init::metalogic::RuleSet;
use covalence_init::wasm::encode::{app, con};
use covalence_init::wasm::lower::official::normative_witnesses;
use covalence_init::wasm::lower::slice::{SliceEnv, wasm1_slice};
use covalence_init::wasm::lower::total::{ClauseMeta, total_spec_clauses, with_total_stack};
use covalence_init::wasm::lower::trace::{Config as NativeConfig, TraceEnv, const_fold_drop_trace};
use covalence_init::wasm::lower::{Clause, rule_set_of};
use covalence_init::wasm::spec::wasm_spec;

/// Numeric value types in the core WebAssembly semantics.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum NumType {
    I32,
    I64,
    F32,
    F64,
}

/// Value types currently represented by the facade.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ValueType {
    Num(NumType),
}

/// A scalar WebAssembly numeric value.
///
/// Floating-point values retain their exact IEEE payload. This preserves
/// signed zero and NaN payloads without asking the host floating-point runtime
/// to interpret them.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum NumericValue {
    I32(u32),
    I64(u64),
    F32(u32),
    F64(u64),
}

impl NumericValue {
    pub const fn value_type(self) -> ValueType {
        ValueType::Num(match self {
            Self::I32(_) => NumType::I32,
            Self::I64(_) => NumType::I64,
            Self::F32(_) => NumType::F32,
            Self::F64(_) => NumType::F64,
        })
    }
}

/// Scalar WebAssembly binary operators.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BinaryOp {
    Add,
    Sub,
    Mul,
    DivSigned,
    DivUnsigned,
    RemSigned,
    RemUnsigned,
    And,
    Or,
    Xor,
    ShiftLeft,
    ShiftRightSigned,
    ShiftRightUnsigned,
    RotateLeft,
    RotateRight,
    FloatDiv,
    Min,
    Max,
    CopySign,
}

impl BinaryOp {
    const fn supports(self, ty: NumType) -> bool {
        let integer = matches!(ty, NumType::I32 | NumType::I64);
        match self {
            Self::Add | Self::Sub | Self::Mul => true,
            Self::DivSigned
            | Self::DivUnsigned
            | Self::RemSigned
            | Self::RemUnsigned
            | Self::And
            | Self::Or
            | Self::Xor
            | Self::ShiftLeft
            | Self::ShiftRightSigned
            | Self::ShiftRightUnsigned
            | Self::RotateLeft
            | Self::RotateRight => integer,
            Self::FloatDiv | Self::Min | Self::Max | Self::CopySign => !integer,
        }
    }

    const fn constructor(self) -> &'static str {
        match self {
            Self::Add => "ADD",
            Self::Sub => "SUB",
            Self::Mul => "MUL",
            Self::DivSigned => "DIV_S",
            Self::DivUnsigned => "DIV_U",
            Self::RemSigned => "REM_S",
            Self::RemUnsigned => "REM_U",
            Self::And => "AND",
            Self::Or => "OR",
            Self::Xor => "XOR",
            Self::ShiftLeft => "SHL",
            Self::ShiftRightSigned => "SHR_S",
            Self::ShiftRightUnsigned => "SHR_U",
            Self::RotateLeft => "ROTL",
            Self::RotateRight => "ROTR",
            Self::FloatDiv => "DIV",
            Self::Min => "MIN",
            Self::Max => "MAX",
            Self::CopySign => "COPYSIGN",
        }
    }
}

/// The exact input/output stack effect of an instruction typing.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct InstructionType {
    pub inputs: Vec<ValueType>,
    pub outputs: Vec<ValueType>,
}

impl InstructionType {
    pub fn new(
        inputs: impl IntoIterator<Item = ValueType>,
        outputs: impl IntoIterator<Item = ValueType>,
    ) -> Self {
        Self {
            inputs: inputs.into_iter().collect(),
            outputs: outputs.into_iter().collect(),
        }
    }
}

/// The small instruction vocabulary currently proved through this facade.
///
/// This is intentionally extensible. Unsupported instructions are refused,
/// rather than encoded approximately.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Instruction {
    Nop,
    Const(NumericValue),
    Binary { ty: NumType, op: BinaryOp },
    Drop,
}

/// A straight-line core-WebAssembly instruction sequence.
#[derive(Debug, Clone, Default, PartialEq, Eq, Hash)]
pub struct Program(Vec<Instruction>);

impl Program {
    pub fn new(instructions: impl IntoIterator<Item = Instruction>) -> Self {
        Self(instructions.into_iter().collect())
    }

    pub fn empty() -> Self {
        Self::default()
    }

    pub fn instructions(&self) -> &[Instruction] {
        &self.0
    }
}

/// A validation context.
///
/// `Empty` is the ordinary empty context. A named context is an uninterpreted
/// but injectively encoded context constant, useful for context-polymorphic
/// instruction rules.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ValidationContext {
    Empty,
    Named(String),
}

/// The machine-state fragment currently needed by pure instruction examples.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum MachineState {
    Empty,
}

/// A concrete execution configuration.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Configuration {
    pub state: MachineState,
    pub program: Program,
}

/// Stable identities of the semantic relations exposed by this API.
///
/// `as_spec_name` is an interoperability identifier, not an AST dependency:
/// it records the exact relation whose checked clause produced a fact.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum RelationIdentity {
    NumericTypeValid,
    InstructionValid,
    ProgramValid,
    OneStep,
    MultiStep,
}

impl RelationIdentity {
    pub const fn as_spec_name(self) -> &'static str {
        match self {
            Self::NumericTypeValid => "Numtype_ok",
            Self::InstructionValid => "Instr_ok",
            Self::ProgramValid => "Instrs_ok",
            Self::OneStep => "Step",
            Self::MultiStep => "Steps",
        }
    }
}

/// A neutral statement of a checked typing fact.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypingStatement {
    NumericType {
        context: ValidationContext,
        ty: NumType,
    },
    Instruction {
        context: ValidationContext,
        instruction: Instruction,
        instruction_type: InstructionType,
    },
    Program {
        context: ValidationContext,
        program: Program,
        instruction_type: InstructionType,
    },
}

/// A neutral statement of a checked execution fact.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExecutionStatement {
    MultiStep {
        from: Configuration,
        to: Configuration,
        steps: usize,
    },
}

/// Hypothesis-free NativeHol evidence for a [`TypingStatement`].
#[derive(Debug, Clone)]
pub struct CheckedTypingFact {
    relation: RelationIdentity,
    statement: TypingStatement,
    theorem: Thm,
}

impl CheckedTypingFact {
    fn new(relation: RelationIdentity, statement: TypingStatement, theorem: Thm) -> Result<Self> {
        if !theorem.hyps().is_empty() {
            return Err(facade_error("typing replay left hypotheses"));
        }
        Ok(Self {
            relation,
            statement,
            theorem,
        })
    }

    pub fn relation(&self) -> RelationIdentity {
        self.relation
    }

    pub fn statement(&self) -> &TypingStatement {
        &self.statement
    }

    /// The checked NativeHol theorem. The facade never fabricates this value.
    pub fn theorem(&self) -> &Thm {
        &self.theorem
    }

    pub fn into_theorem(self) -> Thm {
        self.theorem
    }
}

/// Hypothesis-free NativeHol evidence for an [`ExecutionStatement`].
#[derive(Debug, Clone)]
pub struct CheckedExecutionFact {
    relation: RelationIdentity,
    statement: ExecutionStatement,
    theorem: Thm,
}

/// Source provenance for a normative rule used by a checked example.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct NormativeSource {
    pub path: &'static str,
    pub rule: &'static str,
}

/// One source-neutral typing fact and the pinned normative rule it instantiates.
#[derive(Debug, Clone)]
pub struct NormativeTypingFact {
    pub fact: CheckedTypingFact,
    pub source: NormativeSource,
}

/// A checked, source-attributed WebAssembly example through the full relation.
#[derive(Debug, Clone)]
pub struct NormativeExample {
    pub id: &'static str,
    pub typing: Vec<NormativeTypingFact>,
    /// Complete-sequence typing, where the exact `Instrs_ok` driver has been
    /// replayed. Absence means no sequence theorem is claimed.
    pub program_typing: Option<CheckedTypingFact>,
    pub execution: CheckedExecutionFact,
    pub execution_sources: Vec<NormativeSource>,
}

impl CheckedExecutionFact {
    fn new(
        relation: RelationIdentity,
        statement: ExecutionStatement,
        theorem: Thm,
    ) -> Result<Self> {
        if !theorem.hyps().is_empty() {
            return Err(facade_error("execution replay left hypotheses"));
        }
        Ok(Self {
            relation,
            statement,
            theorem,
        })
    }

    pub fn relation(&self) -> RelationIdentity {
        self.relation
    }

    pub fn statement(&self) -> &ExecutionStatement {
        &self.statement
    }

    pub fn theorem(&self) -> &Thm {
        &self.theorem
    }

    pub fn into_theorem(self) -> Thm {
        self.theorem
    }
}

/// Backend-independent WebAssembly typing capability.
pub trait WasmTyping {
    type Error;
    type Fact;

    fn prove_numeric_type(
        &self,
        context: &ValidationContext,
        ty: NumType,
    ) -> std::result::Result<Self::Fact, Self::Error>;

    fn prove_instruction(
        &self,
        context: &ValidationContext,
        instruction: &Instruction,
        instruction_type: &InstructionType,
    ) -> std::result::Result<Self::Fact, Self::Error>;

    fn prove_program(
        &self,
        context: &ValidationContext,
        program: &Program,
        instruction_type: &InstructionType,
    ) -> std::result::Result<Self::Fact, Self::Error>;
}

/// Backend-independent WebAssembly execution capability.
pub trait WasmExecution {
    type Error;
    type Fact;

    fn execute(&self, from: &Configuration) -> std::result::Result<Self::Fact, Self::Error>;
}

/// NativeHol realization of the first-class WebAssembly semantics API.
///
/// The SpecTec-derived slice is private. Construction checks that it has no
/// opaque premises; all later facts are produced by ordinary rule replay in
/// that exact, order-preserving slice.
pub struct NativeWasmSemantics {
    clauses: Vec<Clause>,
    metas: Vec<ClauseMeta>,
    total_clause_count: usize,
}

impl NativeWasmSemantics {
    /// Build the execution-capable, premise-closed semantics slice.
    pub fn execution() -> Result<Self> {
        let (clauses, metas) = with_total_stack(|| {
            let definitions = wasm_spec();
            let (clauses, report) = total_spec_clauses(&definitions)?;
            if clauses.len() < 7_393 || clauses.len() != report.total_clauses {
                return Err(facade_error(format!(
                    "combined-set coverage regressed: {} clauses",
                    clauses.len()
                )));
            }
            let slice = wasm1_slice(&clauses, &report.metas)?;
            if slice.report().opaque_total() != 0 {
                return Err(facade_error("execution slice contains opaque premises"));
            }
            Ok((clauses, report.metas))
        })?;
        let total_clause_count = clauses.len();
        Ok(Self {
            clauses,
            metas,
            total_clause_count,
        })
    }

    /// Clauses in the full combined semantics into which every returned fact
    /// is transported.
    pub fn total_clause_count(&self) -> usize {
        self.total_clause_count
    }

    /// Derive the pinned normative MVP example family and return only neutral
    /// WebAssembly statements, provenance, and full-relation theorems.
    pub fn normative_examples(&self) -> Result<Vec<NormativeExample>> {
        self.replay(|env, full| {
            let state = encode_state(MachineState::Empty)?;
            normative_witnesses(env, full, &state)?
                .into_iter()
                .map(wrap_normative_witness)
                .collect()
        })
    }

    fn replay<T: Send + 'static>(
        &self,
        f: impl FnOnce(&SliceEnv, &RuleSet<'static>) -> Result<T> + Send + 'static,
    ) -> Result<T> {
        let clauses = self.clauses.clone();
        let metas = self.metas.clone();
        with_total_stack(move || {
            let slice = wasm1_slice(&clauses, &metas)?;
            let env = SliceEnv::new(slice);
            let full = rule_set_of(clauses);
            f(&env, &full)
        })
    }
}

fn rule(env: &SliceEnv, relation: &str, name: &str) -> Result<usize> {
    env.rule_index(Some(relation), name).ok_or_else(|| {
        let available = env
            .rules()
            .iter()
            .filter(|rule| rule.relation == relation)
            .map(|rule| rule.name.as_str())
            .collect::<Vec<_>>();
        facade_error(format!(
            "missing exact rule {relation}/{name}; available: {available:?}"
        ))
    })
}

fn nth_rule(env: &SliceEnv, relation: &str, name: &str, occurrence: usize) -> Result<usize> {
    env.rules()
        .iter()
        .enumerate()
        .filter(|(_, meta)| meta.relation == relation && meta.name == name)
        .nth(occurrence)
        .map(|(index, _)| index)
        .ok_or_else(|| {
            facade_error(format!(
                "missing exact rule {relation}/{name} occurrence {occurrence}"
            ))
        })
}

impl WasmTyping for NativeWasmSemantics {
    type Error = Error;
    type Fact = CheckedTypingFact;

    fn prove_numeric_type(&self, context: &ValidationContext, ty: NumType) -> Result<Self::Fact> {
        let context = context.clone();
        self.replay(move |env, full| {
            let small = env.derive(
                rule(env, "Numtype_ok", "")?,
                &[encode_context(&context), encode_num_type(ty)?],
                vec![],
            )?;
            CheckedTypingFact::new(
                RelationIdentity::NumericTypeValid,
                TypingStatement::NumericType { context, ty },
                env.transport(full, &small)?,
            )
        })
    }

    fn prove_instruction(
        &self,
        context: &ValidationContext,
        instruction: &Instruction,
        instruction_type: &InstructionType,
    ) -> Result<Self::Fact> {
        let context = context.clone();
        let instruction = instruction.clone();
        let instruction_type = instruction_type.clone();
        self.replay(move |env, full| {
            if !instruction_type_matches(&instruction, &instruction_type) {
                return Err(facade_error(format!(
                    "stack effect does not match instruction: {instruction_type:?}"
                )));
            }
            let context_term = encode_context(&context);
            let (rule_name, args, premises) = match &instruction {
                Instruction::Nop => ("nop", vec![context_term], vec![]),
                Instruction::Const(value) => {
                    let ValueType::Num(ty) = value.value_type();
                    (
                        "const",
                        vec![
                            context_term,
                            encode_num_type(ty)?,
                            encode_numeric_value(*value)?,
                        ],
                        vec![],
                    )
                }
                Instruction::Binary { ty, op } => (
                    "binop",
                    vec![
                        context_term,
                        encode_num_type(*ty)?,
                        nullary_case(op.constructor())?,
                    ],
                    vec![],
                ),
                Instruction::Drop => {
                    let [ValueType::Num(drop_ty)] = instruction_type.inputs.as_slice() else {
                        unreachable!("validated above")
                    };
                    let ty = encode_num_type(*drop_ty)?;
                    let num = env.derive(
                        rule(env, "Numtype_ok", "")?,
                        &[context_term.clone(), ty.clone()],
                        vec![],
                    )?;
                    let sort = env.derive(
                        nth_rule(env, "ev.sort.numtype", "", num_type_index(*drop_ty))?,
                        &[],
                        vec![],
                    )?;
                    let val = env.derive(
                        rule(env, "Valtype_ok", "num")?,
                        &[context_term.clone(), ty.clone()],
                        vec![
                            covalence_init::metalogic::Premise::Derivation(num),
                            covalence_init::metalogic::Premise::Derivation(sort),
                        ],
                    )?;
                    (
                        "drop",
                        vec![context_term, ty],
                        vec![covalence_init::metalogic::Premise::Derivation(val)],
                    )
                }
            };
            let small = env.derive(rule(env, "Instr_ok", rule_name)?, &args, premises)?;
            CheckedTypingFact::new(
                RelationIdentity::InstructionValid,
                TypingStatement::Instruction {
                    context,
                    instruction,
                    instruction_type,
                },
                env.transport(full, &small)?,
            )
        })
    }

    fn prove_program(
        &self,
        context: &ValidationContext,
        program: &Program,
        instruction_type: &InstructionType,
    ) -> Result<Self::Fact> {
        let context = context.clone();
        let program = program.clone();
        let instruction_type = instruction_type.clone();
        self.replay(move |env, full| {
            if context != ValidationContext::Empty
                || instruction_type != InstructionType::new([], [])
            {
                return Err(facade_error(
                    "no exact checked Instrs_ok driver for this program typing",
                ));
            }
            let witness_id = match program.instructions() {
                [Instruction::Nop] => "mvp.nop",
                [Instruction::Const(NumericValue::I32(5)), Instruction::Drop] => "mvp.const-drop",
                _ => {
                    return Err(facade_error(
                        "no exact checked Instrs_ok driver for this program typing",
                    ));
                }
            };
            let state = encode_state(MachineState::Empty)?;
            let theorem = normative_witnesses(env, full, &state)?
                .into_iter()
                .find(|witness| witness.id == witness_id)
                .and_then(|witness| witness.program_typing)
                .ok_or_else(|| {
                    facade_error(format!("{witness_id} has no checked Instrs_ok theorem"))
                })?;
            CheckedTypingFact::new(
                RelationIdentity::ProgramValid,
                TypingStatement::Program {
                    context,
                    program,
                    instruction_type,
                },
                theorem,
            )
        })
    }
}

impl WasmExecution for NativeWasmSemantics {
    type Error = Error;
    type Fact = CheckedExecutionFact;

    fn execute(&self, from: &Configuration) -> Result<Self::Fact> {
        let from = from.clone();
        self.replay(move |env, full| {
            if from.state != MachineState::Empty {
                return Err(facade_error("unsupported machine state"));
            }
            if matches!(
                from.program.instructions(),
                [Instruction::Const(NumericValue::I32(5)), Instruction::Drop,]
            ) {
                let state = encode_state(from.state)?;
                let witness = normative_witnesses(env, full, &state)?
                    .into_iter()
                    .find(|witness| witness.id == "mvp.const-drop")
                    .ok_or_else(|| facade_error("missing checked mvp.const-drop witness"))?;
                ensure_native_endpoints(&from, &witness.from, &witness.to)?;
                return CheckedExecutionFact::new(
                    RelationIdentity::MultiStep,
                    ExecutionStatement::MultiStep {
                        from,
                        to: Configuration {
                            state: MachineState::Empty,
                            program: Program::empty(),
                        },
                        steps: witness.n_steps,
                    },
                    witness.execution,
                );
            }
            let trace = TraceEnv::for_slice(env)?;
            let (small, to, steps) = match from.program.instructions() {
                [Instruction::Nop] => {
                    let nop = env.derive(rule(env, "Step_pure", "nop")?, &[], vec![])?;
                    let state = encode_state(from.state)?;
                    let before = encode_program(&from.program)?;
                    let after = encode_program(&Program::empty())?;
                    let step = trace.lift_pure(&state, &before, &after, nop)?;
                    (
                        trace.chain(&[step])?,
                        Configuration {
                            state: from.state,
                            program: Program::empty(),
                        },
                        1,
                    )
                }
                [
                    Instruction::Const(NumericValue::I32(a)),
                    Instruction::Const(NumericValue::I32(b)),
                    Instruction::Binary {
                        ty: NumType::I32,
                        op: BinaryOp::Add,
                    },
                    Instruction::Drop,
                ] if (*a, *b) == (2, 3) => {
                    let state = encode_state(from.state)?;
                    let (theorem, native_from, native_to, steps) =
                        const_fold_drop_trace(&trace, &state)?;
                    ensure_native_endpoints(&from, &native_from, &native_to)?;
                    (
                        theorem,
                        Configuration {
                            state: from.state,
                            program: Program::empty(),
                        },
                        steps,
                    )
                }
                _ => {
                    return Err(facade_error(
                        "no exact checked execution driver for this program",
                    ));
                }
            };
            CheckedExecutionFact::new(
                RelationIdentity::MultiStep,
                ExecutionStatement::MultiStep { from, to, steps },
                env.transport(full, &small)?,
            )
        })
    }
}

fn instruction_type_matches(instruction: &Instruction, actual: &InstructionType) -> bool {
    match instruction {
        Instruction::Nop => *actual == InstructionType::new([], []),
        Instruction::Const(value) => *actual == InstructionType::new([], [value.value_type()]),
        Instruction::Binary { ty, op } => {
            let value = ValueType::Num(*ty);
            op.supports(*ty) && *actual == InstructionType::new([value, value], [value])
        }
        Instruction::Drop => {
            matches!(actual.inputs.as_slice(), [ValueType::Num(_)]) && actual.outputs.is_empty()
        }
    }
}

const fn num_type_index(ty: NumType) -> usize {
    match ty {
        NumType::I32 => 0,
        NumType::I64 => 1,
        NumType::F32 => 2,
        NumType::F64 => 3,
    }
}

fn facade_error(message: impl Into<String>) -> Error {
    Error::ConnectiveRule(format!("wasm facade: {}", message.into()))
}

fn wrap_normative_witness(
    witness: covalence_init::wasm::lower::official::NormativeWitness,
) -> Result<NormativeExample> {
    let program = Program::new(
        witness
            .program
            .iter()
            .map(|instruction| parse_normative_instruction(instruction))
            .collect::<Result<Vec<_>>>()?,
    );
    let from = Configuration {
        state: MachineState::Empty,
        program,
    };
    ensure_native_endpoints(&from, &witness.from, &witness.to)?;
    let to = Configuration {
        state: MachineState::Empty,
        program: Program::empty(),
    };

    let typing = witness
        .typing
        .into_iter()
        .map(|typing| {
            let instruction = parse_normative_instruction(typing.instruction)?;
            let instruction_type = match instruction {
                Instruction::Drop => InstructionType::new([ValueType::Num(NumType::I32)], []),
                _ => canonical_closed_instruction_type(&instruction),
            };
            Ok(NormativeTypingFact {
                fact: CheckedTypingFact::new(
                    RelationIdentity::InstructionValid,
                    TypingStatement::Instruction {
                        context: ValidationContext::Empty,
                        instruction,
                        instruction_type,
                    },
                    typing.theorem,
                )?,
                source: NormativeSource {
                    path: typing.source.path,
                    rule: typing.source.rule,
                },
            })
        })
        .collect::<Result<Vec<_>>>()?;

    let program_typing = witness
        .program_typing
        .map(|theorem| {
            CheckedTypingFact::new(
                RelationIdentity::ProgramValid,
                TypingStatement::Program {
                    context: ValidationContext::Empty,
                    program: from.program.clone(),
                    instruction_type: InstructionType::new([], []),
                },
                theorem,
            )
        })
        .transpose()?;
    let execution = CheckedExecutionFact::new(
        RelationIdentity::MultiStep,
        ExecutionStatement::MultiStep {
            from,
            to,
            steps: witness.n_steps,
        },
        witness.execution,
    )?;
    Ok(NormativeExample {
        id: witness.id,
        typing,
        program_typing,
        execution,
        execution_sources: witness
            .execution_sources
            .iter()
            .map(|source| NormativeSource {
                path: source.path,
                rule: source.rule,
            })
            .collect(),
    })
}

fn parse_normative_instruction(instruction: &str) -> Result<Instruction> {
    match instruction {
        "nop" => Ok(Instruction::Nop),
        "i32.const 2" => Ok(Instruction::Const(NumericValue::I32(2))),
        "i32.const 3" => Ok(Instruction::Const(NumericValue::I32(3))),
        "i32.const 5" => Ok(Instruction::Const(NumericValue::I32(5))),
        "i32.add" => Ok(Instruction::Binary {
            ty: NumType::I32,
            op: BinaryOp::Add,
        }),
        "drop" => Ok(Instruction::Drop),
        other => Err(facade_error(format!(
            "unknown normative instruction `{other}`"
        ))),
    }
}

fn canonical_closed_instruction_type(instruction: &Instruction) -> InstructionType {
    match instruction {
        Instruction::Nop => InstructionType::new([], []),
        Instruction::Const(value) => InstructionType::new([], [value.value_type()]),
        Instruction::Binary { ty, .. } => {
            let value = ValueType::Num(*ty);
            InstructionType::new([value, value], [value])
        }
        Instruction::Drop => unreachable!("DROP is polymorphic"),
    }
}

fn nullary_case(name: &str) -> Result<Term> {
    app(con(format!("case.{name}")), con("tup"))
}

fn encode_num_type(ty: NumType) -> Result<Term> {
    nullary_case(match ty {
        NumType::I32 => "I32",
        NumType::I64 => "I64",
        NumType::F32 => "F32",
        NumType::F64 => "F64",
    })
}

fn encode_context(context: &ValidationContext) -> Term {
    match context {
        ValidationContext::Empty => con("struct"),
        ValidationContext::Named(name) => {
            let encoded = name
                .as_bytes()
                .iter()
                .map(|b| format!("{b:02x}"))
                .collect::<String>();
            con(format!("api.context.named.{encoded}"))
        }
    }
}

fn encode_unsigned_integer_value(value: u64) -> Result<Term> {
    let payload = app(
        con("tup"),
        app(con("num.nat"), covalence_hol_eval::mk_nat(value))?,
    )?;
    app(con("case.%"), payload)
}

fn encode_float_value(width: u32, bits: u64) -> Result<Term> {
    let (exponent_bits, significand_bits) = match width {
        32 => (8, 23),
        64 => (11, 52),
        _ => unreachable!("WebAssembly has only f32 and f64"),
    };
    let sign = bits >> (width - 1);
    let significand_mask = (1u64 << significand_bits) - 1;
    let exponent_mask = (1u64 << exponent_bits) - 1;
    let significand = bits & significand_mask;
    let encoded_exponent = (bits >> significand_bits) & exponent_mask;
    let magnitude = if encoded_exponent == 0 {
        app(
            con("case.SUBNORM"),
            app(
                con("tup"),
                app(con("num.nat"), covalence_hol_eval::mk_nat(significand))?,
            )?,
        )?
    } else if encoded_exponent == exponent_mask {
        if significand == 0 {
            nullary_case("INF")?
        } else {
            app(
                con("case.NAN"),
                app(
                    con("tup"),
                    app(con("num.nat"), covalence_hol_eval::mk_nat(significand))?,
                )?,
            )?
        }
    } else {
        let bias = (1u64 << (exponent_bits - 1)) - 1;
        let exponent = encoded_exponent as i64 - bias as i64;
        let encoded_integer = app(
            app(
                con("num.int"),
                covalence_hol_eval::mk_nat(u64::from(exponent < 0)),
            )?,
            covalence_hol_eval::mk_nat(exponent.unsigned_abs()),
        )?;
        app(
            con("case.NORM"),
            app(
                app(
                    con("tup"),
                    app(con("num.nat"), covalence_hol_eval::mk_nat(significand))?,
                )?,
                encoded_integer,
            )?,
        )?
    };
    app(
        con(if sign == 0 { "case.POS" } else { "case.NEG" }),
        magnitude,
    )
}

fn encode_numeric_value(value: NumericValue) -> Result<Term> {
    match value {
        NumericValue::I32(value) => encode_unsigned_integer_value(value as u64),
        NumericValue::I64(value) => encode_unsigned_integer_value(value),
        NumericValue::F32(bits) => encode_float_value(32, bits as u64),
        NumericValue::F64(bits) => encode_float_value(64, bits),
    }
}

fn encode_instruction(instruction: &Instruction) -> Result<Term> {
    match instruction {
        Instruction::Nop => nullary_case("NOP"),
        Instruction::Const(value) => {
            let ValueType::Num(ty) = value.value_type();
            app(
                con("case.CONST"),
                app(
                    app(con("tup"), encode_num_type(ty)?)?,
                    encode_numeric_value(*value)?,
                )?,
            )
        }
        Instruction::Binary { ty, op } => app(
            con("case.BINOP"),
            app(
                app(con("tup"), encode_num_type(*ty)?)?,
                nullary_case(op.constructor())?,
            )?,
        ),
        Instruction::Drop => nullary_case("DROP"),
    }
}

fn encode_program(program: &Program) -> Result<Term> {
    program
        .instructions()
        .iter()
        .try_fold(con("list"), |list, instruction| {
            app(list, encode_instruction(instruction)?)
        })
}

fn encode_state(state: MachineState) -> Result<Term> {
    match state {
        MachineState::Empty => app(
            con("case.%;%"),
            app(app(con("tup"), con("struct"))?, con("struct"))?,
        ),
    }
}

fn ensure_native_endpoints(
    from: &Configuration,
    native_from: &NativeConfig,
    native_to: &NativeConfig,
) -> Result<()> {
    let state = encode_state(from.state)?;
    if native_from.z != state
        || native_from.instrs != encode_program(&from.program)?
        || native_to.z != state
        || native_to.instrs != encode_program(&Program::empty())?
    {
        return Err(facade_error(
            "native replay endpoints do not match the public statement",
        ));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn facade_produces_checked_typing_and_execution_without_ast_values() {
        let semantics = NativeWasmSemantics::execution().unwrap();
        assert!(semantics.total_clause_count() >= 3_766);

        for (instruction, instruction_type) in [
            (Instruction::Nop, InstructionType::new([], [])),
            (
                Instruction::Const(NumericValue::I32(7)),
                InstructionType::new([], [ValueType::Num(NumType::I32)]),
            ),
            (
                Instruction::Const(NumericValue::I64(u64::MAX)),
                InstructionType::new([], [ValueType::Num(NumType::I64)]),
            ),
            (
                Instruction::Const(NumericValue::F32(0x8000_0000)),
                InstructionType::new([], [ValueType::Num(NumType::F32)]),
            ),
            (
                Instruction::Const(NumericValue::F64(0x7ff8_0000_0000_0042)),
                InstructionType::new([], [ValueType::Num(NumType::F64)]),
            ),
            (
                Instruction::Binary {
                    ty: NumType::I32,
                    op: BinaryOp::Add,
                },
                InstructionType::new(
                    [ValueType::Num(NumType::I32), ValueType::Num(NumType::I32)],
                    [ValueType::Num(NumType::I32)],
                ),
            ),
            (
                Instruction::Binary {
                    ty: NumType::I64,
                    op: BinaryOp::Xor,
                },
                InstructionType::new(
                    [ValueType::Num(NumType::I64), ValueType::Num(NumType::I64)],
                    [ValueType::Num(NumType::I64)],
                ),
            ),
            (
                Instruction::Binary {
                    ty: NumType::F64,
                    op: BinaryOp::CopySign,
                },
                InstructionType::new(
                    [ValueType::Num(NumType::F64), ValueType::Num(NumType::F64)],
                    [ValueType::Num(NumType::F64)],
                ),
            ),
            (
                Instruction::Drop,
                InstructionType::new([ValueType::Num(NumType::I32)], []),
            ),
        ] {
            let fact = semantics
                .prove_instruction(&ValidationContext::Empty, &instruction, &instruction_type)
                .unwrap();
            assert_eq!(fact.relation(), RelationIdentity::InstructionValid);
            assert!(fact.theorem().hyps().is_empty());
            assert_eq!(
                fact.statement(),
                &TypingStatement::Instruction {
                    context: ValidationContext::Empty,
                    instruction,
                    instruction_type,
                }
            );
        }
        assert!(
            semantics
                .prove_instruction(
                    &ValidationContext::Empty,
                    &Instruction::Binary {
                        ty: NumType::F32,
                        op: BinaryOp::And,
                    },
                    &InstructionType::new(
                        [ValueType::Num(NumType::F32), ValueType::Num(NumType::F32)],
                        [ValueType::Num(NumType::F32)],
                    ),
                )
                .is_err()
        );

        let numeric = semantics
            .prove_numeric_type(&ValidationContext::Empty, NumType::I32)
            .unwrap();
        assert_eq!(numeric.relation(), RelationIdentity::NumericTypeValid);

        let from = Configuration {
            state: MachineState::Empty,
            program: Program::new([Instruction::Nop]),
        };
        let fact = semantics.execute(&from).unwrap();
        assert_eq!(fact.relation(), RelationIdentity::MultiStep);
        assert_eq!(
            fact.statement(),
            &ExecutionStatement::MultiStep {
                from: from.clone(),
                to: Configuration {
                    state: MachineState::Empty,
                    program: Program::empty(),
                },
                steps: 1,
            }
        );
        let program_typing = semantics
            .prove_program(
                &ValidationContext::Empty,
                &from.program,
                &InstructionType::new([], []),
            )
            .unwrap();
        assert_eq!(
            program_typing.statement(),
            &TypingStatement::Program {
                context: ValidationContext::Empty,
                program: from.program,
                instruction_type: InstructionType::new([], []),
            }
        );
        assert_eq!(program_typing.relation(), RelationIdentity::ProgramValid);
    }

    #[test]
    fn facade_executes_exact_integer_example_and_refuses_unknown_search() {
        let semantics = NativeWasmSemantics::execution().unwrap();
        assert_eq!(semantics.total_clause_count(), 7_393);
        let examples = semantics.normative_examples().unwrap();
        assert_eq!(
            examples
                .iter()
                .map(|example| example.id)
                .collect::<Vec<_>>(),
            ["mvp.nop", "mvp.const-drop", "mvp.i32-add-drop"]
        );
        assert!(examples.iter().all(|example| {
            example.execution.theorem().hyps().is_empty()
                && example
                    .typing
                    .iter()
                    .all(|typing| typing.fact.theorem().hyps().is_empty())
        }));
        assert!(examples[0].program_typing.is_some());
        assert!(examples[1].program_typing.is_some());
        assert!(examples[2].program_typing.is_none());
        let const_drop =
            Program::new([Instruction::Const(NumericValue::I32(5)), Instruction::Drop]);
        let const_drop_typing = semantics
            .prove_program(
                &ValidationContext::Empty,
                &const_drop,
                &InstructionType::new([], []),
            )
            .unwrap();
        assert_eq!(
            const_drop_typing.statement(),
            &TypingStatement::Program {
                context: ValidationContext::Empty,
                program: const_drop,
                instruction_type: InstructionType::new([], []),
            }
        );
        let const_drop_from = match const_drop_typing.statement() {
            TypingStatement::Program { program, .. } => Configuration {
                state: MachineState::Empty,
                program: program.clone(),
            },
            _ => unreachable!(),
        };
        let const_drop_execution = semantics.execute(&const_drop_from).unwrap();
        assert!(matches!(
            const_drop_execution.statement(),
            ExecutionStatement::MultiStep { steps: 1, .. }
        ));
        assert!(const_drop_execution.theorem().hyps().is_empty());

        let from = Configuration {
            state: MachineState::Empty,
            program: Program::new([
                Instruction::Const(NumericValue::I32(2)),
                Instruction::Const(NumericValue::I32(3)),
                Instruction::Binary {
                    ty: NumType::I32,
                    op: BinaryOp::Add,
                },
                Instruction::Drop,
            ]),
        };
        let fact = semantics.execute(&from).unwrap();
        assert_eq!(
            fact.statement(),
            &ExecutionStatement::MultiStep {
                from,
                to: Configuration {
                    state: MachineState::Empty,
                    program: Program::empty(),
                },
                steps: 2,
            }
        );
        assert!(
            semantics
                .prove_program(
                    &ValidationContext::Empty,
                    match fact.statement() {
                        ExecutionStatement::MultiStep { from, .. } => &from.program,
                    },
                    &InstructionType::new([], []),
                )
                .is_err(),
            "do not claim whole-program typing until exact stack framing is replayable"
        );

        let unsupported = Configuration {
            state: MachineState::Empty,
            program: Program::new([Instruction::Const(NumericValue::I32(9))]),
        };
        assert!(semantics.execute(&unsupported).is_err());
    }
}
