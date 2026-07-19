//! Native HOL reflection of checked raw-byte parser witnesses.
//!
//! Reflection validates the host witness and constructs closed byte terms. It
//! does not turn a successful host computation into a theorem or add a mint
//! site.
//!
//! @covalence-api-impl {"api":"A0013","name":"NativeHol closed-byte witness reflection","representation":"A0003 native byte-string leaves"}

use covalence_core::Term;
use covalence_kernel_data::BytesSyntax;
use covalence_parsing_api::{
    ByteParseError, ByteParseOutcome, ByteParser, LiteralBytes, ParseBudget,
};

use super::inductive::hol::NativeHol;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NativeLiteralParse {
    pub source: Term,
    pub consumed: Term,
    pub remainder: Term,
    pub value: Term,
}

/// Recompute a literal-prefix parse and reflect its closed data into A0003.
///
/// `Ok(None)` is a computational no-match, not negative proof evidence.
pub fn reflect_literal_parse(
    parser: &LiteralBytes,
    input: &[u8],
    budget: ParseBudget,
) -> Result<Option<NativeLiteralParse>, ByteParseError> {
    let ByteParseOutcome::Match { value, witness } = parser.parse_bytes(input, budget)? else {
        return Ok(None);
    };
    assert!(witness.is_valid_for(input.len()));
    let logic = NativeHol;
    Ok(Some(NativeLiteralParse {
        source: logic.bytes_literal(input),
        consumed: logic.bytes_literal(&input[witness.consumed.start..witness.consumed.end]),
        remainder: logic.bytes_literal(&input[witness.remainder.start..witness.remainder.end]),
        value: logic.bytes_literal(&value),
    }))
}

#[cfg(test)]
mod tests {
    use covalence_hol_eval::as_blob;

    use super::*;

    #[test]
    fn reflects_only_recomputed_closed_witness_data() {
        let reflected = reflect_literal_parse(
            &LiteralBytes::new(b"ok".to_vec()),
            b"okay",
            ParseBudget::new(4, 2, 1),
        )
        .unwrap()
        .unwrap();
        assert_eq!(as_blob(&reflected.source).as_deref(), Some(&b"okay"[..]));
        assert_eq!(as_blob(&reflected.consumed).as_deref(), Some(&b"ok"[..]));
        assert_eq!(as_blob(&reflected.remainder).as_deref(), Some(&b"ay"[..]));
        assert_eq!(as_blob(&reflected.value).as_deref(), Some(&b"ok"[..]));
    }

    #[test]
    fn no_match_reflects_no_term_or_theorem() {
        assert!(
            reflect_literal_parse(
                &LiteralBytes::new(b"ok".to_vec()),
                b"no",
                ParseBudget::new(2, 2, 1),
            )
            .unwrap()
            .is_none()
        );
    }
}
