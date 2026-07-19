//! Proof-search translation from closed BLC terms to SKI HOL programs.
//!
//! The host translation is intentionally only a compiler candidate. This
//! module implements [`Compiler`] and returns a HOL `bool list` artifact, but
//! does not implement `CompilerLaws`: preservation must be established by a
//! later replay proof over the general BLC and SKI reduction relations.

use core::fmt;

use covalence_computation::{
    blc,
    compiler::{CompiledTerm, DomainDecision, PartialCompiler},
    ski,
    theory::Theory,
};
use covalence_core::{Term, Type};
use covalence_hol_eval::EvalThm as Thm;

use super::concrete::bit_list;
use crate::init::inductive::hol::{Hol, NativeHol};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LambdaToSkiMetadata {
    pub source_bits: Vec<bool>,
    pub target_bits: Vec<bool>,
}

pub type LambdaToSkiArtifact = CompiledTerm<NativeHol, LambdaToSkiMetadata>;

/// A compiler instance is scoped to one source program. This makes the
/// connection between the plain-data candidate and its HOL source term
/// explicit and checkable.
#[derive(Clone, Debug)]
pub struct LambdaToSki {
    source: blc::Term,
    domain_predicate: Term,
}

impl LambdaToSki {
    pub fn new(source: blc::Term) -> Result<Self, LambdaToSkiError> {
        if !source.is_closed() {
            return Err(LambdaToSkiError::OpenSource);
        }
        let bits = covalence_hol_eval::defs::list(Type::bool());
        let encoded = bit_list(source.encode())?;
        let hol = NativeHol;
        let candidate = hol.var("__lambda_to_ski_source", bits.clone());
        let domain_predicate = hol.lam("__lambda_to_ski_source", bits, hol.eq(candidate, encoded)?);
        Ok(Self {
            source,
            domain_predicate,
        })
    }

    pub fn translate(&self) -> Result<ski::Term, LambdaToSkiError> {
        let open = translate_open(&self.source);
        into_closed(open)
    }
}

#[derive(Clone, Debug)]
pub enum LambdaToSkiError {
    OpenSource,
    SourceRepresentationMismatch,
    InternalOpenResult,
    Kernel(covalence_core::Error),
}

impl fmt::Display for LambdaToSkiError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::OpenSource => f.write_str("lambda-to-SKI requires a closed BLC term"),
            Self::SourceRepresentationMismatch => {
                f.write_str("source HOL term is not this compiler's BLC encoding")
            }
            Self::InternalOpenResult => {
                f.write_str("closed BLC translation unexpectedly retained a free variable")
            }
            Self::Kernel(error) => write!(f, "HOL construction failed: {error}"),
        }
    }
}

impl std::error::Error for LambdaToSkiError {}

impl From<covalence_core::Error> for LambdaToSkiError {
    fn from(error: covalence_core::Error) -> Self {
        Self::Kernel(error)
    }
}

#[derive(Clone, Debug)]
pub struct ClosedSourceCertificate {
    /// `⊢ encoded_source = encoded_source`.
    pub theorem: Thm,
    pub source_bits: Vec<bool>,
}

impl PartialCompiler<NativeHol, NativeHol> for LambdaToSki {
    type Artifact = LambdaToSkiArtifact;
    type DomainCertificate = ClosedSourceCertificate;
    type OutsideDomainCertificate = core::convert::Infallible;
    type Error = LambdaToSkiError;

    fn domain_predicate(&self) -> &Term {
        &self.domain_predicate
    }

    fn certify_domain(
        &self,
        _source_logic: &NativeHol,
        _source_theory: &Theory<NativeHol>,
        source_program: &Term,
    ) -> Result<DomainDecision<Self::DomainCertificate, Self::OutsideDomainCertificate>, Self::Error>
    {
        let source_bits = self.source.encode();
        let encoded = bit_list(source_bits.iter().copied())?;
        if source_program != &encoded {
            // Producing `Outside` would require a kernel disequality theorem.
            return Err(LambdaToSkiError::SourceRepresentationMismatch);
        }
        Ok(DomainDecision::Inside(ClosedSourceCertificate {
            theorem: Thm::refl(encoded)?,
            source_bits,
        }))
    }

    fn compile_in_domain(
        &self,
        _source_logic: &NativeHol,
        _source_theory: &Theory<NativeHol>,
        _target_logic: &NativeHol,
        _target_theory: &Theory<NativeHol>,
        source_program: &Term,
        domain: &Self::DomainCertificate,
    ) -> Result<Self::Artifact, Self::Error> {
        let source_bits = self.source.encode();
        let expected_domain = NativeHol.eq(source_program.clone(), source_program.clone())?;
        if source_program != &bit_list(source_bits.iter().copied())?
            || domain.source_bits != source_bits
            || Hol::concl(&NativeHol, &domain.theorem) != expected_domain
        {
            return Err(LambdaToSkiError::SourceRepresentationMismatch);
        }
        let target = self.translate()?;
        let target_bits = target.encode();
        Ok(CompiledTerm {
            term: bit_list(target_bits.iter().copied())?,
            metadata: LambdaToSkiMetadata {
                source_bits,
                target_bits,
            },
        })
    }
}

// TODO(cov:computation.lambda-ski-preservation, major): Define general BLC/SKI
// reduction relations in HOL and implement PartialCompilerLaws by replaying a
// bracket-abstraction preservation proof.

#[derive(Clone, Debug)]
enum Open {
    Variable(usize),
    Closed(ski::Term),
    Apply(Box<Open>, Box<Open>),
}

fn translate_open(term: &blc::Term) -> Open {
    match term {
        blc::Term::Var(index) => Open::Variable(*index),
        blc::Term::App(function, argument) => Open::Apply(
            Box::new(translate_open(function)),
            Box::new(translate_open(argument)),
        ),
        blc::Term::Abs(body) => abstract_bound(translate_open(body)),
    }
}

fn abstract_bound(term: Open) -> Open {
    match term {
        Open::Variable(0) => Open::Closed(ski::Term::I),
        Open::Variable(index) => Open::Apply(
            Box::new(Open::Closed(ski::Term::K)),
            Box::new(Open::Variable(index - 1)),
        ),
        Open::Closed(term) => Open::Closed(ski::Term::apply(ski::Term::K, term)),
        Open::Apply(function, argument) => Open::Apply(
            Box::new(Open::Apply(
                Box::new(Open::Closed(ski::Term::S)),
                Box::new(abstract_bound(*function)),
            )),
            Box::new(abstract_bound(*argument)),
        ),
    }
}

fn into_closed(term: Open) -> Result<ski::Term, LambdaToSkiError> {
    match term {
        Open::Variable(_) => Err(LambdaToSkiError::InternalOpenResult),
        Open::Closed(term) => Ok(term),
        Open::Apply(function, argument) => Ok(ski::Term::apply(
            into_closed(*function)?,
            into_closed(*argument)?,
        )),
    }
}

#[cfg(test)]
mod tests {
    use covalence_computation::compiler::{CompilationArtifact, PartialCompiler};

    use super::*;

    #[test]
    fn identity_translates_to_i() {
        let source = blc::Term::abs(blc::Term::var(0));
        assert_eq!(
            LambdaToSki::new(source).unwrap().translate().unwrap(),
            ski::Term::I
        );
    }

    #[test]
    fn compiler_checks_and_reifies_both_representations() {
        let source = blc::Term::abs(blc::Term::var(0));
        let compiler = LambdaToSki::new(source.clone()).unwrap();
        let source_realization = super::super::blc::realize(&source).unwrap();
        let target = ski::Term::I;
        let target_realization = super::super::ski::realize(&target).unwrap();
        let domain = match compiler
            .certify_domain(
                &NativeHol,
                &source_realization.theory,
                &source_realization.theory.machine,
            )
            .unwrap()
        {
            DomainDecision::Inside(domain) => domain,
            DomainDecision::Outside(never) => match never {},
        };
        let artifact = compiler
            .compile_in_domain(
                &NativeHol,
                &source_realization.theory,
                &NativeHol,
                &target_realization.theory,
                &source_realization.theory.machine,
                &domain,
            )
            .unwrap();
        assert_eq!(artifact.metadata.target_bits, target.encode());
        assert_eq!(artifact.target_program(), &artifact.term);
    }
}
