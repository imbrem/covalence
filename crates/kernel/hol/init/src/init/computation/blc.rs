//! Native HOL terms for concrete Binary Lambda Calculus configurations.
//!
//! The serialized BLC term is represented by `bool list` in HOL. Reduction
//! performed in Rust is untrusted search: [`realize`] reifies both endpoints
//! into HOL and exposes only a bounded relation for that exact configuration.

use covalence_computation::{
    blc,
    theory::{Realization, Theory},
};

use super::concrete::{bit_list, bounded_realization};
use super::{NativeTheoryError, ValidatedTransitionFacts};
use crate::init::inductive::hol::NativeHol;

pub fn realize(
    term: &blc::Term,
) -> Result<Realization<Theory<NativeHol>, ValidatedTransitionFacts>, NativeTheoryError> {
    let initial = bit_list(term.encode())?;
    let next = term
        .beta_step()
        .map(|next| bit_list(next.encode()))
        .transpose()?;
    bounded_realization(initial, next)
}

#[cfg(test)]
mod tests {
    use covalence_computation::theory::{TheoremCertificate, TransitionLaws};
    use covalence_hol_eval::defs::list;

    use super::*;

    #[test]
    fn realizes_beta_redex_as_hol_bit_lists() {
        let id = blc::Term::abs(blc::Term::var(0));
        let redex = blc::Term::app(id.clone(), id);
        let realized = realize(&redex).unwrap();
        assert_eq!(
            realized.theory.state_type,
            list(covalence_core::Type::bool())
        );
        let certificate = realized.facts.step_closed().unwrap();
        assert!(certificate.theorem().hyps().is_empty());
    }
}
