//! Native HOL terms for concrete SKI configurations.
//!
//! SKI's canonical prefix encoding is represented by `bool list`. As with the
//! BLC backend, host reduction only selects a candidate endpoint; the exposed
//! transition predicate itself is a typed HOL term.

use covalence_computation::{
    ski,
    theory::{Realization, Theory},
};

use super::concrete::{bit_list, bounded_realization};
use super::{NativeTheoryError, ValidatedTransitionFacts};
use crate::init::inductive::hol::NativeHol;

pub fn realize(
    term: &ski::Term,
) -> Result<Realization<Theory<NativeHol>, ValidatedTransitionFacts>, NativeTheoryError> {
    let initial = bit_list(term.encode())?;
    let next = term
        .step()
        .map(|next| bit_list(next.encode()))
        .transpose()?;
    bounded_realization(initial, next)
}

#[cfg(test)]
mod tests {
    use covalence_computation::theory::{TheoremCertificate, TransitionLaws};

    use super::*;

    #[test]
    fn realizes_i_contraction_with_a_closed_certificate() {
        let redex = ski::Term::apply(ski::Term::I, ski::Term::K);
        let realized = realize(&redex).unwrap();
        let certificate = realized.facts.step_closed().unwrap();
        assert!(certificate.theorem().hyps().is_empty());
    }
}
