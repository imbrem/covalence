//! The kernel-agnostic literal value + the backend / grammar traits.
//!
//! A [`Lit`] is the *parsed* numeral value, tagged by which rung of the ladder
//! `Nat ⊂ Int ⊂ Decimal ⊂ Rat` it landed on (plus a raw-bits float leaf). It is
//! produced by a [`LiteralGrammar`] and consumed by a [`NumeralBackend`] — the
//! two seams the whole crate turns on. Neither trait mentions the kernel, so the
//! default build is kernel-independent; the kernel backends live behind `hol`.

use covalence_grammar::NatBase;
use covalence_types::{Decimal, Int, Nat, Rat};

/// A parsed numeral literal — one rung of the ladder, carrying the surface base
/// it was written in (for `Nat`/`Int`) so a deparser can reproduce the prefix.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Lit {
    /// A natural-number literal (`2748`, `0xABC`, `0b1011`).
    Nat { value: Nat, base: NatBase },
    /// A signed-integer literal (`-42`, `+7`, `-0xABC`).
    Int {
        value: Int,
        base: NatBase,
        explicit_sign: bool,
    },
    /// A finite decimal (`1.5`, `-0.75`, `1.5e3`).
    Decimal(Decimal),
    /// A rational fraction (`3/4`, `-1/2`).
    Rat(Rat),
}

impl Lit {
    /// The value as a [`Rat`] — the canonical injection down the ladder into the
    /// rationals (`Nat`/`Int`/`Decimal`/`Rat` all embed).
    pub fn to_rat(&self) -> Rat {
        match self {
            Lit::Nat { value, .. } => Rat::from(Int::from(value.clone())),
            Lit::Int { value, .. } => Rat::from(value.clone()),
            Lit::Decimal(d) => d.to_rat(),
            Lit::Rat(r) => r.clone(),
        }
    }
}

/// How a [`LiteralGrammar`] should render a [`Lit`] back to surface text.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Style {
    /// Reproduce the literal's own recorded surface base (round-trip).
    Native,
    /// Force plain base-ten rendering regardless of the recorded base.
    Decimal,
}

/// A pluggable literal grammar: parse a numeral off the front of a byte slice,
/// and deparse a [`Lit`] back to surface bytes.
///
/// The default impl ([`crate::NumeralGrammar`]) wraps the compositional parsers
/// in [`covalence_grammar`]; alternative front ends (a different alphabet, a
/// restricted subset) implement the same two methods.
pub trait LiteralGrammar {
    /// Parse a numeral literal off the front of `src`, returning the value and
    /// the unconsumed suffix, or `None` if `src` does not start with one.
    fn parse<'a>(&self, src: &'a [u8]) -> Option<(Lit, &'a [u8])>;

    /// Render `lit` back to surface bytes in the requested [`Style`].
    fn deparse(&self, lit: &Lit, style: Style) -> Vec<u8>;
}

/// A pluggable numeral *backend*: turn a parsed [`Lit`] into the backend's own
/// representation, and (optionally) PROVE relationships between built values.
///
/// This is the point of the crate. `Symbolic` builds real kernel `Term`s and
/// proves `0xABC = 2748` structurally with no new TCB; `Builtin` does the same
/// through the fast CanonRule arithmetic families; `Wasm` (a skeleton) would
/// certify a verified evaluation trace. A kernel-free backend (`type Repr =
/// Rat; type Thm = ()`) is equally valid.
pub trait NumeralBackend {
    /// The backend's representation of a built numeral.
    type Repr;
    /// The backend's proof object.
    type Thm;

    /// Build a natural-number value.
    fn nat(&self, value: &Nat) -> Self::Repr;
    /// Build a signed-integer value.
    fn int(&self, value: &Int) -> Self::Repr;
    /// Build a finite-decimal value.
    fn decimal(&self, value: &Decimal) -> Self::Repr;
    /// Build a rational value.
    fn rat(&self, value: &Rat) -> Self::Repr;
    /// Build a float from raw IEEE-754 single-precision bits.
    fn f32_bits(&self, bits: u32) -> Self::Repr;

    /// Prove `a = b`, if the backend can. Returns `None` when it cannot (rather
    /// than fabricating a proof).
    fn prove_eq(&self, a: &Self::Repr, b: &Self::Repr) -> Option<Self::Thm>;
    /// Prove `a < b`, if the backend can.
    fn prove_lt(&self, a: &Self::Repr, b: &Self::Repr) -> Option<Self::Thm>;
    /// Prove `toRat a = r` (the canonical rational a value denotes), if the
    /// backend can.
    fn prove_to_rat(&self, a: &Self::Repr, r: &Self::Repr) -> Option<Self::Thm>;

    /// Ground a decimal to a single-precision float with an enclosure
    /// certificate. Defaults to [`FloatCert32::Unproven`]; a backend that can
    /// prove the rounding enclosure overrides this.
    fn ground_f32(&self, _value: &Decimal) -> FloatCert32<Self::Thm> {
        FloatCert32::Unproven
    }
}

/// The result of grounding a decimal to a single-precision float: the chosen
/// bit pattern, and — when the backend can prove it — an enclosure certificate
/// witnessing that the rounded value is the nearest representable float.
pub enum FloatCert32<Thm> {
    /// The rounding enclosure is proved; the float bits and its witness.
    Proved { bits: u32, cert: Thm },
    /// The backend computed the bits but has no enclosure proof yet.
    Bits(u32),
    /// The backend produced nothing (no rounding performed).
    Unproven,
}

/// Parse `src` with grammar `g`, then build the value with backend `b` —
/// generic over both seams. Returns the built [`NumeralBackend::Repr`] and the
/// unconsumed suffix, or `None` if `src` does not start with a numeral.
pub fn lower<'a, G: LiteralGrammar, B: NumeralBackend>(
    g: &G,
    b: &B,
    src: &'a [u8],
) -> Option<(B::Repr, &'a [u8])> {
    let (lit, rest) = g.parse(src)?;
    let repr = build(b, &lit);
    Some((repr, rest))
}

/// Build a [`Lit`] with a backend, dispatching on its rung.
pub fn build<B: NumeralBackend>(b: &B, lit: &Lit) -> B::Repr {
    match lit {
        Lit::Nat { value, .. } => b.nat(value),
        Lit::Int { value, .. } => b.int(value),
        Lit::Decimal(d) => b.decimal(d),
        Lit::Rat(r) => b.rat(r),
    }
}
