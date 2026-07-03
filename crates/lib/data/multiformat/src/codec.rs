//! Multicodec content-type codes and logic tags.
//!
//! `0x55` is the registered multicodec 'raw' code. The covalence/Coln-specific
//! codes live in the multicodec **private-use range** (`>= 0x30_0000`) for the
//! alpha; real registration comes later. Keeping payloads self-describing is the
//! whole point: a reader that does not understand a payload codec can still
//! verify the hash and follow links.

/// Multicodec content-type code: identifies *what* a content-addressed object is.
pub type Codec = u64;

/// Raw bytes (registered multicodec `raw`).
pub const RAW: Codec = 0x55;
/// An axiom-set / theory object.
pub const AXIOM_SET: Codec = 0x30_0101;
/// covalence: a classical HOL theorem payload.
pub const COV_HOL_THM: Codec = 0x30_0110;
/// Coln: a geometric-logic sequent payload.
pub const COLN_GEOM_SEQ: Codec = 0x30_0120;
/// A neutral "waist" derivation witness (proof-irrelevant; bytes never inspected).
pub const MM_DERIVATION: Codec = 0x30_0130;
/// The interchange envelope itself (a [`DerivationFact`](crate::DerivationFact)).
pub const DERIVATION_FACT: Codec = 0x30_01f0;

/// Human label for a codec, or `unknown(0x..)` for codes outside the registry.
pub fn name(c: Codec) -> String {
    match c {
        RAW => "raw".into(),
        AXIOM_SET => "axiom-set".into(),
        COV_HOL_THM => "covalence/hol-theorem".into(),
        COLN_GEOM_SEQ => "coln/geometric-sequent".into(),
        MM_DERIVATION => "metamath/derivation-witness".into(),
        DERIVATION_FACT => "derivation-fact".into(),
        other => format!("unknown(0x{other:x})"),
    }
}

/// The logic a statement lives in.
pub mod logic {
    /// Logic tag code.
    pub type Logic = u64;

    /// Classical higher-order logic (covalence kernel).
    pub const HOL: Logic = 1;
    /// Geometric logic (Coln kernel).
    pub const GEOMETRIC: Logic = 2;
    /// The neutral metamath waist.
    pub const METAMATH: Logic = 3;

    /// Human label for a logic tag.
    pub fn name(l: Logic) -> &'static str {
        match l {
            HOL => "HOL (classical)",
            GEOMETRIC => "geometric",
            METAMATH => "metamath-waist",
            _ => "unknown",
        }
    }
}
