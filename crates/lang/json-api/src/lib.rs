//! RFC 8259 JSON value vocabulary.
//!
//! This crate intentionally contains no byte parser. Numbers are exact finite
//! decimals, never binary floating-point values. Parsed object member
//! sequences are distinct from semantic JSON objects: sequence order and
//! duplicate names are syntax observations, not silently chosen value
//! semantics.
//!
//! @covalence-api {"id":"A0007","title":"RFC JSON with exact decimals","status":"experimental","dependsOn":["A0004","A0006"]}

use covalence_decimal_api::CanonicalDecimal;
use covalence_inductive::DatatypeFamilyExpr;
use covalence_parsing_api::{
    InterpretationPer, ParseAttempt, PartialExactParser, PartialParser, PartialPrefixParser,
    PrefixAdapterError, PrefixInterpretation, SameInterpretation, Span, exact_from_prefix,
    same_interpretation_by,
};
use covalence_types::Int;
use std::{collections::HashMap, collections::HashSet, convert::Infallible};

pub mod corpus;

/// A JSON string code point.
///
/// RFC 8259's ABNF permits escaped unpaired UTF-16 surrogates, so using Rust
/// `String` alone would reject syntactically permitted JSON strings.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum JsonCodePoint {
    Scalar(char),
    UnpairedSurrogate(JsonSurrogate),
}

/// A UTF-16 surrogate code unit that was not paired during JSON decoding.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct JsonSurrogate(u16);

impl JsonSurrogate {
    pub fn new(code_unit: u16) -> Option<Self> {
        (0xd800..=0xdfff)
            .contains(&code_unit)
            .then_some(Self(code_unit))
    }

    pub fn code_unit(self) -> u16 {
        self.0
    }
}

/// A sequence of JSON string code points.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Default)]
pub struct JsonString(pub Vec<JsonCodePoint>);

impl From<&str> for JsonString {
    fn from(value: &str) -> Self {
        Self(value.chars().map(JsonCodePoint::Scalar).collect())
    }
}

/// An object member as it occurs in parsed syntax.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct JsonMember<D = CanonicalDecimal> {
    pub name: JsonString,
    pub value: JsonValue<D>,
}

/// Ordered parsed members. Duplicate names are retained.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct JsonMemberSequence<D = CanonicalDecimal>(pub Vec<JsonMember<D>>);

/// A semantic object with unique names.
///
/// Storage order is retained for deterministic traversal, but equality ignores
/// member order. Construction rejects duplicate names.
#[derive(Clone, Debug)]
pub struct JsonObject<D = CanonicalDecimal>(Vec<JsonMember<D>>);

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DuplicateName(pub JsonString);

impl<D> JsonObject<D> {
    pub fn new(members: Vec<JsonMember<D>>) -> Result<Self, DuplicateName> {
        let mut names = HashSet::with_capacity(members.len());
        for member in &members {
            if !names.insert(&member.name) {
                return Err(DuplicateName(member.name.clone()));
            }
        }
        Ok(Self(members))
    }

    pub fn members(&self) -> &[JsonMember<D>] {
        &self.0
    }
}

impl<D: PartialEq> PartialEq for JsonObject<D> {
    fn eq(&self, other: &Self) -> bool {
        if self.0.len() != other.0.len() {
            return false;
        }
        let by_name = other
            .0
            .iter()
            .map(|member| (&member.name, &member.value))
            .collect::<HashMap<_, _>>();
        self.0.iter().all(|member| {
            by_name
                .get(&member.name)
                .is_some_and(|value| **value == member.value)
        })
    }
}

impl<D: Eq> Eq for JsonObject<D> {}

/// A semantic JSON value, parameterized by an exact decimal representation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum JsonValue<D = CanonicalDecimal> {
    Null,
    Bool(bool),
    Number(D),
    String(JsonString),
    Array(Vec<JsonValue<D>>),
    Object(JsonObject<D>),
}

/// JSON syntax after decoding strings and numbers, but before choosing an
/// object-member policy.
///
/// Unlike [`JsonValue`], object members remain ordered and may contain
/// duplicate names. This makes the parse result lossless with respect to the
/// object observations relevant to RFC 8259.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ParsedJsonValue<D = CanonicalDecimal> {
    Null,
    Bool(bool),
    Number(D),
    String(JsonString),
    Array(Vec<ParsedJsonValue<D>>),
    Object(Vec<ParsedJsonMember<D>>),
}

/// An object member in decoded JSON syntax.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParsedJsonMember<D = CanonicalDecimal> {
    pub name: JsonString,
    pub value: ParsedJsonValue<D>,
}

/// Failure to interpret decoded syntax as semantic JSON.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum JsonInterpretationError {
    DuplicateName(DuplicateName),
}

impl ParsedJsonValue {
    /// Interpret syntax using the canonical semantic policy: duplicate object
    /// names are rejected at every nesting depth.
    pub fn into_semantic(self) -> Result<JsonValue, JsonInterpretationError> {
        Ok(match self {
            Self::Null => JsonValue::Null,
            Self::Bool(value) => JsonValue::Bool(value),
            Self::Number(value) => JsonValue::Number(value),
            Self::String(value) => JsonValue::String(value),
            Self::Array(values) => JsonValue::Array(
                values
                    .into_iter()
                    .map(Self::into_semantic)
                    .collect::<Result<_, _>>()?,
            ),
            Self::Object(members) => {
                let members = members
                    .into_iter()
                    .map(|member| {
                        Ok(JsonMember {
                            name: member.name,
                            value: member.value.into_semantic()?,
                        })
                    })
                    .collect::<Result<Vec<_>, JsonInterpretationError>>()?;
                JsonValue::Object(
                    JsonObject::new(members).map_err(JsonInterpretationError::DuplicateName)?,
                )
            }
        })
    }
}

/// A diagnostic from the strict RFC 8259 byte parser.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct JsonParseError {
    pub offset: usize,
    pub kind: JsonParseErrorKind,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum JsonParseErrorKind {
    ExpectedValue,
    ExpectedByte(u8),
    InvalidLiteral,
    InvalidNumber,
    InvalidUtf8,
    InvalidEscape,
    InvalidUnicodeEscape,
    UnescapedControl,
    DuplicateName,
    TrailingInput,
    /// A container would exceed the parser's configured nesting limit.
    NestingLimitExceeded {
        limit: usize,
    },
}

/// A checked upper bound on nested JSON arrays and objects.
///
/// The hard ceiling keeps the recursive syntax and semantic conversions in
/// this reference implementation stack-safe even when configuration comes
/// from untrusted input.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct JsonNestingLimit(usize);

// TODO(cov:json.parser-stackless-depth, major): Replace the recursive hard ceiling with a stack-safe parser whose resource policy can accept arbitrary RFC 8259 nesting.

impl JsonNestingLimit {
    /// Default limit used by [`JsonSyntaxParser`] and [`JsonParser`].
    pub const DEFAULT: Self = Self(128);
    /// Largest limit accepted by this recursive reference implementation.
    pub const MAX_SUPPORTED: usize = 256;

    /// Construct a checked nesting limit. Zero permits scalar roots only.
    pub const fn new(limit: usize) -> Option<Self> {
        if limit <= Self::MAX_SUPPORTED {
            Some(Self(limit))
        } else {
            None
        }
    }

    /// Return the maximum number of nested containers.
    pub const fn get(self) -> usize {
        self.0
    }
}

impl Default for JsonNestingLimit {
    fn default() -> Self {
        Self::DEFAULT
    }
}

/// Positive, checkable parsing evidence retained by the reference parser.
///
/// This is not a theorem. It records the exact number of source bytes consumed
/// so a later logic backend can replay the parse against the returned value.
/// The decoded tree is deliberately not duplicated inside this witness.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct JsonParseWitness {
    pub consumed: usize,
}

/// Evidence that the reference backend observed two semantic values as equal.
///
/// This is deliberately an observation token rather than a theorem. A logic
/// backend must check or reflect the values before granting proof authority.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ObservedSemanticEquality;

/// Strict RFC 8259 syntax parser.
#[derive(Clone, Copy, Debug, Default)]
pub struct JsonSyntaxParser;

/// Strict semantic parser: syntax parsing followed by recursive rejection of
/// duplicate object names.
#[derive(Clone, Copy, Debug, Default)]
pub struct JsonParser;

impl JsonSyntaxParser {
    /// Parse one RFC 8259 JSON text prefix beginning at `start`.
    ///
    /// Offsets are byte offsets in the original source. The accepted prefix
    /// includes the grammar's leading and trailing JSON whitespace; bytes
    /// after that prefix are returned as the remainder rather than rejected.
    pub fn parse_prefix_diagnostic(
        &self,
        source: &[u8],
        start: usize,
    ) -> Result<PrefixInterpretation<ParsedJsonValue, JsonParseWitness>, JsonParseError> {
        self.parse_prefix_diagnostic_with_limit(source, start, JsonNestingLimit::DEFAULT)
    }

    /// Parse one JSON text prefix with an explicit container nesting limit.
    pub fn parse_prefix_diagnostic_with_limit(
        &self,
        source: &[u8],
        start: usize,
        limit: JsonNestingLimit,
    ) -> Result<PrefixInterpretation<ParsedJsonValue, JsonParseWitness>, JsonParseError> {
        if start > source.len() {
            return Err(JsonParseError {
                offset: source.len(),
                kind: JsonParseErrorKind::ExpectedValue,
            });
        }
        let mut parser = ByteParser {
            source,
            offset: start,
            nesting_limit: limit.get(),
        };
        parser.whitespace();
        let value = parser.value(0)?;
        parser.whitespace();
        let witness = JsonParseWitness {
            consumed: parser.offset - start,
        };
        Ok(PrefixInterpretation::new(
            value,
            witness,
            Span {
                start,
                end: parser.offset,
            },
            parser.offset,
        )
        .expect("parser offset is the prefix remainder"))
    }

    /// Parse one complete JSON text and retain ordered object syntax.
    pub fn parse_diagnostic(
        &self,
        source: &[u8],
    ) -> Result<(ParsedJsonValue, JsonParseWitness), JsonParseError> {
        self.parse_diagnostic_with_limit(source, JsonNestingLimit::DEFAULT)
    }

    /// Parse with an explicit, checked container nesting limit.
    pub fn parse_diagnostic_with_limit(
        &self,
        source: &[u8],
        limit: JsonNestingLimit,
    ) -> Result<(ParsedJsonValue, JsonParseWitness), JsonParseError> {
        let parsed = self.parse_prefix_diagnostic_with_limit(source, 0, limit)?;
        if parsed.remainder != source.len() {
            return Err(JsonParseError {
                offset: parsed.remainder,
                kind: JsonParseErrorKind::TrailingInput,
            });
        }
        Ok((parsed.value, parsed.witness))
    }
}

impl JsonParser {
    /// Parse one semantic JSON value prefix, rejecting duplicate object names.
    pub fn parse_prefix_diagnostic(
        &self,
        source: &[u8],
        start: usize,
    ) -> Result<PrefixInterpretation<JsonValue, JsonParseWitness>, JsonParseError> {
        self.parse_prefix_diagnostic_with_limit(source, start, JsonNestingLimit::DEFAULT)
    }

    /// Parse one semantic JSON value prefix with an explicit nesting limit.
    pub fn parse_prefix_diagnostic_with_limit(
        &self,
        source: &[u8],
        start: usize,
        limit: JsonNestingLimit,
    ) -> Result<PrefixInterpretation<JsonValue, JsonParseWitness>, JsonParseError> {
        let parsed = JsonSyntaxParser.parse_prefix_diagnostic_with_limit(source, start, limit)?;
        let value = parsed.value.into_semantic().map_err(|_| JsonParseError {
            offset: parsed.consumed.end,
            kind: JsonParseErrorKind::DuplicateName,
        })?;
        Ok(PrefixInterpretation {
            value,
            witness: parsed.witness,
            consumed: parsed.consumed,
            remainder: parsed.remainder,
        })
    }

    /// Parse one complete JSON text and apply canonical object semantics.
    pub fn parse_diagnostic(
        &self,
        source: &[u8],
    ) -> Result<(JsonValue, JsonParseWitness), JsonParseError> {
        self.parse_diagnostic_with_limit(source, JsonNestingLimit::DEFAULT)
    }

    /// Parse with an explicit, checked container nesting limit.
    pub fn parse_diagnostic_with_limit(
        &self,
        source: &[u8],
        limit: JsonNestingLimit,
    ) -> Result<(JsonValue, JsonParseWitness), JsonParseError> {
        let (syntax, witness) = JsonSyntaxParser.parse_diagnostic_with_limit(source, limit)?;
        let value = syntax.clone().into_semantic().map_err(|_| JsonParseError {
            offset: source.len(),
            kind: JsonParseErrorKind::DuplicateName,
        })?;
        Ok((value, witness))
    }
}

impl PartialPrefixParser for JsonSyntaxParser {
    type Source = [u8];
    type Value = ParsedJsonValue;
    type Witness = JsonParseWitness;
    type Diagnostic = JsonParseError;
    type Error = Infallible;

    fn parse_prefix(
        &self,
        source: &[u8],
        start: usize,
    ) -> Result<
        ParseAttempt<PrefixInterpretation<Self::Value, Self::Witness>, Self::Diagnostic>,
        Self::Error,
    > {
        Ok(match self.parse_prefix_diagnostic(source, start) {
            Ok(parsed) => ParseAttempt::Match(parsed),
            Err(diagnostic) => ParseAttempt::NoMatch(diagnostic),
        })
    }
}

impl PartialExactParser for JsonSyntaxParser {
    type Source = [u8];
    type Value = ParsedJsonValue;
    type Witness = JsonParseWitness;
    type Diagnostic = JsonParseError;
    type Error = Infallible;

    fn parse_exact(
        &self,
        source: &[u8],
    ) -> Result<ParseAttempt<(Self::Value, Self::Witness), Self::Diagnostic>, Self::Error> {
        json_exact_from_prefix(self, source)
    }
}

impl PartialPrefixParser for JsonParser {
    type Source = [u8];
    type Value = JsonValue;
    type Witness = JsonParseWitness;
    type Diagnostic = JsonParseError;
    type Error = Infallible;

    fn parse_prefix(
        &self,
        source: &[u8],
        start: usize,
    ) -> Result<
        ParseAttempt<PrefixInterpretation<Self::Value, Self::Witness>, Self::Diagnostic>,
        Self::Error,
    > {
        Ok(match self.parse_prefix_diagnostic(source, start) {
            Ok(parsed) => ParseAttempt::Match(parsed),
            Err(diagnostic) => ParseAttempt::NoMatch(diagnostic),
        })
    }
}

impl PartialExactParser for JsonParser {
    type Source = [u8];
    type Value = JsonValue;
    type Witness = JsonParseWitness;
    type Diagnostic = JsonParseError;
    type Error = Infallible;

    fn parse_exact(
        &self,
        source: &[u8],
    ) -> Result<ParseAttempt<(Self::Value, Self::Witness), Self::Diagnostic>, Self::Error> {
        json_exact_from_prefix(self, source)
    }
}

fn json_exact_from_prefix<P>(
    parser: &P,
    source: &[u8],
) -> Result<ParseAttempt<(P::Value, P::Witness), JsonParseError>, Infallible>
where
    P: PartialPrefixParser<Source = [u8], Diagnostic = JsonParseError, Error = Infallible>,
{
    match exact_from_prefix(parser, source, source.len(), |trailing| JsonParseError {
        offset: trailing.start,
        kind: JsonParseErrorKind::TrailingInput,
    }) {
        Ok(attempt) => Ok(attempt),
        Err(PrefixAdapterError::Parse(error)) => match error {},
        Err(PrefixAdapterError::InvalidExtent { .. }) => {
            unreachable!("JSON prefix parser constructs internally validated extents")
        }
    }
}

impl PartialParser for JsonSyntaxParser {
    type Source = [u8];
    type Value = ParsedJsonValue;
    type Witness = JsonParseWitness;
    type Error = Infallible;

    fn parse(&self, source: &[u8]) -> Result<Option<(Self::Value, Self::Witness)>, Self::Error> {
        Ok(self.parse_diagnostic(source).ok())
    }
}

impl PartialParser for JsonParser {
    type Source = [u8];
    type Value = JsonValue;
    type Witness = JsonParseWitness;
    type Error = Infallible;

    fn parse(&self, source: &[u8]) -> Result<Option<(Self::Value, Self::Witness)>, Self::Error> {
        Ok(self.parse_diagnostic(source).ok())
    }
}

impl InterpretationPer for JsonParser {
    type EquivalenceWitness = ObservedSemanticEquality;

    fn same_interpretation(
        &self,
        left: &[u8],
        right: &[u8],
    ) -> Result<
        Option<SameInterpretation<Self::Value, Self::Witness, Self::EquivalenceWitness>>,
        Self::Error,
    > {
        same_interpretation_by(self, left, right, |left_value, right_value| {
            (left_value == right_value).then_some(ObservedSemanticEquality)
        })
    }
}

struct ByteParser<'a> {
    source: &'a [u8],
    offset: usize,
    nesting_limit: usize,
}

impl ByteParser<'_> {
    fn error(&self, kind: JsonParseErrorKind) -> JsonParseError {
        JsonParseError {
            offset: self.offset,
            kind,
        }
    }

    fn whitespace(&mut self) {
        while matches!(self.peek(), Some(b' ' | b'\t' | b'\n' | b'\r')) {
            self.offset += 1;
        }
    }

    fn peek(&self) -> Option<u8> {
        self.source.get(self.offset).copied()
    }

    fn take(&mut self, byte: u8) -> Result<(), JsonParseError> {
        if self.peek() == Some(byte) {
            self.offset += 1;
            Ok(())
        } else {
            Err(self.error(JsonParseErrorKind::ExpectedByte(byte)))
        }
    }

    fn literal(&mut self, literal: &[u8]) -> Result<(), JsonParseError> {
        if self.source[self.offset..].starts_with(literal) {
            self.offset += literal.len();
            Ok(())
        } else {
            Err(self.error(JsonParseErrorKind::InvalidLiteral))
        }
    }

    fn value(&mut self, depth: usize) -> Result<ParsedJsonValue, JsonParseError> {
        match self.peek() {
            Some(b'n') => {
                self.literal(b"null")?;
                Ok(ParsedJsonValue::Null)
            }
            Some(b't') => {
                self.literal(b"true")?;
                Ok(ParsedJsonValue::Bool(true))
            }
            Some(b'f') => {
                self.literal(b"false")?;
                Ok(ParsedJsonValue::Bool(false))
            }
            Some(b'"') => self.string().map(ParsedJsonValue::String),
            Some(b'[') => {
                self.check_container_depth(depth)?;
                self.array(depth + 1)
            }
            Some(b'{') => {
                self.check_container_depth(depth)?;
                self.object(depth + 1)
            }
            Some(b'-' | b'0'..=b'9') => self.number().map(ParsedJsonValue::Number),
            _ => Err(self.error(JsonParseErrorKind::ExpectedValue)),
        }
    }

    fn check_container_depth(&self, depth: usize) -> Result<(), JsonParseError> {
        if depth < self.nesting_limit {
            Ok(())
        } else {
            Err(self.error(JsonParseErrorKind::NestingLimitExceeded {
                limit: self.nesting_limit,
            }))
        }
    }

    fn array(&mut self, depth: usize) -> Result<ParsedJsonValue, JsonParseError> {
        self.take(b'[')?;
        self.whitespace();
        let mut values = Vec::new();
        if self.peek() == Some(b']') {
            self.offset += 1;
            return Ok(ParsedJsonValue::Array(values));
        }
        loop {
            values.push(self.value(depth)?);
            self.whitespace();
            match self.peek() {
                Some(b',') => {
                    self.offset += 1;
                    self.whitespace();
                }
                Some(b']') => {
                    self.offset += 1;
                    return Ok(ParsedJsonValue::Array(values));
                }
                _ => return Err(self.error(JsonParseErrorKind::ExpectedByte(b']'))),
            }
        }
    }

    fn object(&mut self, depth: usize) -> Result<ParsedJsonValue, JsonParseError> {
        self.take(b'{')?;
        self.whitespace();
        let mut members = Vec::new();
        if self.peek() == Some(b'}') {
            self.offset += 1;
            return Ok(ParsedJsonValue::Object(members));
        }
        loop {
            let name = self.string()?;
            self.whitespace();
            self.take(b':')?;
            self.whitespace();
            let value = self.value(depth)?;
            members.push(ParsedJsonMember { name, value });
            self.whitespace();
            match self.peek() {
                Some(b',') => {
                    self.offset += 1;
                    self.whitespace();
                }
                Some(b'}') => {
                    self.offset += 1;
                    return Ok(ParsedJsonValue::Object(members));
                }
                _ => return Err(self.error(JsonParseErrorKind::ExpectedByte(b'}'))),
            }
        }
    }

    fn string(&mut self) -> Result<JsonString, JsonParseError> {
        self.take(b'"')?;
        let mut result = Vec::new();
        loop {
            match self.peek() {
                None => return Err(self.error(JsonParseErrorKind::ExpectedByte(b'"'))),
                Some(b'"') => {
                    self.offset += 1;
                    return Ok(JsonString(result));
                }
                Some(0x00..=0x1f) => {
                    return Err(self.error(JsonParseErrorKind::UnescapedControl));
                }
                Some(b'\\') => {
                    self.offset += 1;
                    self.escape(&mut result)?;
                }
                Some(byte) if byte.is_ascii() => {
                    self.offset += 1;
                    result.push(JsonCodePoint::Scalar(char::from(byte)));
                }
                Some(_) => {
                    // Decode exactly one scalar. Valid text before a later
                    // malformed byte must advance normally so the diagnostic
                    // identifies the malformed byte rather than the start of
                    // the whole remaining string.
                    let width = match self.source[self.offset] {
                        0xc2..=0xdf => 2,
                        0xe0..=0xef => 3,
                        0xf0..=0xf4 => 4,
                        _ => return Err(self.error(JsonParseErrorKind::InvalidUtf8)),
                    };
                    let encoded = self
                        .source
                        .get(self.offset..self.offset + width)
                        .ok_or_else(|| self.error(JsonParseErrorKind::InvalidUtf8))?;
                    let character = std::str::from_utf8(encoded)
                        .map_err(|_| self.error(JsonParseErrorKind::InvalidUtf8))?
                        .chars()
                        .next()
                        .expect("a nonempty UTF-8 scalar");
                    self.offset += character.len_utf8();
                    result.push(JsonCodePoint::Scalar(character));
                }
            }
        }
    }

    fn escape(&mut self, result: &mut Vec<JsonCodePoint>) -> Result<(), JsonParseError> {
        let escaped = self
            .peek()
            .ok_or_else(|| self.error(JsonParseErrorKind::InvalidEscape))?;
        self.offset += 1;
        let scalar = match escaped {
            b'"' => Some('"'),
            b'\\' => Some('\\'),
            b'/' => Some('/'),
            b'b' => Some('\u{0008}'),
            b'f' => Some('\u{000c}'),
            b'n' => Some('\n'),
            b'r' => Some('\r'),
            b't' => Some('\t'),
            b'u' => {
                let first = self.hex_quad()?;
                if (0xd800..=0xdbff).contains(&first)
                    && self.source[self.offset..].starts_with(b"\\u")
                {
                    let saved = self.offset;
                    self.offset += 2;
                    let second = self.hex_quad()?;
                    if (0xdc00..=0xdfff).contains(&second) {
                        let code = 0x10000
                            + ((u32::from(first) - 0xd800) << 10)
                            + (u32::from(second) - 0xdc00);
                        Some(char::from_u32(code).expect("valid surrogate pair"))
                    } else {
                        self.offset = saved;
                        result.push(JsonCodePoint::UnpairedSurrogate(
                            JsonSurrogate::new(first).expect("high surrogate"),
                        ));
                        None
                    }
                } else if let Some(surrogate) = JsonSurrogate::new(first) {
                    result.push(JsonCodePoint::UnpairedSurrogate(surrogate));
                    None
                } else {
                    Some(
                        char::from_u32(u32::from(first))
                            .expect("non-surrogate UTF-16 code unit is scalar"),
                    )
                }
            }
            _ => return Err(self.error(JsonParseErrorKind::InvalidEscape)),
        };
        if let Some(character) = scalar {
            result.push(JsonCodePoint::Scalar(character));
        }
        Ok(())
    }

    fn hex_quad(&mut self) -> Result<u16, JsonParseError> {
        let end = self.offset.saturating_add(4);
        let bytes = self
            .source
            .get(self.offset..end)
            .ok_or_else(|| self.error(JsonParseErrorKind::InvalidUnicodeEscape))?;
        let mut value = 0_u16;
        for byte in bytes {
            let digit = match byte {
                b'0'..=b'9' => u16::from(byte - b'0'),
                b'a'..=b'f' => u16::from(byte - b'a' + 10),
                b'A'..=b'F' => u16::from(byte - b'A' + 10),
                _ => return Err(self.error(JsonParseErrorKind::InvalidUnicodeEscape)),
            };
            value = value * 16 + digit;
        }
        self.offset = end;
        Ok(value)
    }

    fn number(&mut self) -> Result<CanonicalDecimal, JsonParseError> {
        let negative = if self.peek() == Some(b'-') {
            self.offset += 1;
            true
        } else {
            false
        };
        let mut digits = Vec::new();
        match self.peek() {
            Some(b'0') => {
                digits.push(0);
                self.offset += 1;
                if matches!(self.peek(), Some(b'0'..=b'9')) {
                    return Err(self.error(JsonParseErrorKind::InvalidNumber));
                }
            }
            Some(b'1'..=b'9') => {
                while let Some(byte @ b'0'..=b'9') = self.peek() {
                    digits.push(byte - b'0');
                    self.offset += 1;
                }
            }
            _ => return Err(self.error(JsonParseErrorKind::InvalidNumber)),
        }

        let mut fractional_digits = 0_usize;
        if self.peek() == Some(b'.') {
            self.offset += 1;
            let start = self.offset;
            while let Some(byte @ b'0'..=b'9') = self.peek() {
                digits.push(byte - b'0');
                fractional_digits += 1;
                self.offset += 1;
            }
            if self.offset == start {
                return Err(self.error(JsonParseErrorKind::InvalidNumber));
            }
        }

        let mut exponent = Int::zero();
        if matches!(self.peek(), Some(b'e' | b'E')) {
            self.offset += 1;
            let sign = match self.peek() {
                Some(b'+') => {
                    self.offset += 1;
                    ""
                }
                Some(b'-') => {
                    self.offset += 1;
                    "-"
                }
                _ => "",
            };
            let start = self.offset;
            while matches!(self.peek(), Some(b'0'..=b'9')) {
                self.offset += 1;
            }
            if self.offset == start {
                return Err(self.error(JsonParseErrorKind::InvalidNumber));
            }
            let magnitude =
                std::str::from_utf8(&self.source[start..self.offset]).expect("ASCII digits");
            exponent = format!("{sign}{magnitude}")
                .parse()
                .map_err(|_| self.error(JsonParseErrorKind::InvalidNumber))?;
        }
        exponent -= Int::from(fractional_digits);
        CanonicalDecimal::new(negative, digits, exponent)
            .map_err(|_| self.error(JsonParseErrorKind::InvalidNumber))
    }
}

/// Policy for interpreting a parsed member sequence as a semantic object.
pub trait ObjectInterpretation<D> {
    type Error;

    fn interpret(&self, members: JsonMemberSequence<D>) -> Result<JsonObject<D>, Self::Error>;
}

/// Reject duplicate names, retaining the source order of unique members.
pub struct RejectDuplicates;

impl<D> ObjectInterpretation<D> for RejectDuplicates {
    type Error = DuplicateName;

    fn interpret(&self, members: JsonMemberSequence<D>) -> Result<JsonObject<D>, Self::Error> {
        JsonObject::new(members.0)
    }
}

/// External parameters of the JSON datatype family.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum JsonParameter {
    Bool,
    Decimal,
    String,
}

/// Stable declaration-order indices of the six JSON value constructors.
///
/// Backends use these indices when exposing constructor, view, and
/// no-confusion laws for [`json_value_family`]. Arrays and objects are single
/// constructors here: their payloads are respectively a recursive list and an
/// ordered recursive member list.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(usize)]
pub enum JsonConstructor {
    Null = 0,
    Bool = 1,
    Number = 2,
    String = 3,
    Array = 4,
    Object = 5,
}

impl JsonConstructor {
    /// All constructors in the declaration order used by
    /// [`json_value_family`].
    pub const ALL: [Self; 6] = [
        Self::Null,
        Self::Bool,
        Self::Number,
        Self::String,
        Self::Array,
        Self::Object,
    ];

    /// The declaration-order index consumed by proof-bearing backends.
    pub const fn index(self) -> usize {
        self as usize
    }
}

fn list_family<P>(element: DatatypeFamilyExpr<P>) -> DatatypeFamilyExpr<P> {
    DatatypeFamilyExpr::least(DatatypeFamilyExpr::Sum(vec![
        DatatypeFamilyExpr::One,
        DatatypeFamilyExpr::Product(vec![element, DatatypeFamilyExpr::Bound(0)]),
    ]))
}

/// The regular datatype family underlying JSON values.
///
/// Structurally:
///
/// ```text
/// JsonF(X) =
///   1 + Bool + Decimal + String
///     + μY. (1 + X × Y)
///     + μY. (1 + (String × X) × Y)
/// ```
///
/// The two nested least fixpoints are respectively arrays and ordered object
/// member sequences. Duplicate-name rejection remains a semantic policy above
/// this syntax. This expression supplies no fixpoint realization or proof
/// facts; those remain backend capabilities.
pub fn json_value_family() -> DatatypeFamilyExpr<JsonParameter> {
    let value = DatatypeFamilyExpr::FamilyVar;
    let member = DatatypeFamilyExpr::Product(vec![
        DatatypeFamilyExpr::Param(JsonParameter::String),
        value.clone(),
    ]);
    DatatypeFamilyExpr::Sum(vec![
        DatatypeFamilyExpr::One,
        DatatypeFamilyExpr::Param(JsonParameter::Bool),
        DatatypeFamilyExpr::Param(JsonParameter::Decimal),
        DatatypeFamilyExpr::Param(JsonParameter::String),
        list_family(value),
        list_family(member),
    ])
}

/// Compatibility name for [`json_value_family`].
///
/// The return type is now the more expressive scoped datatype-family syntax,
/// rather than a first-order [`PolynomialSpec`](covalence_inductive::PolynomialSpec)
/// with dishonest `Array` and `Object` constants.
pub fn json_value_polynomial() -> DatatypeFamilyExpr<JsonParameter> {
    json_value_family()
}

// TODO(cov:json.polynomial-composition, major): Close the native JSON family fixpoint once DatatypeFamilyExpr has a proof-bearing nested-fixpoint backend; the NativeHol constructor-layer adapter already realizes the exact six-way F(X), including recursive array/member-list payload shapes.

#[cfg(test)]
mod tests {
    use super::*;

    fn member(name: &str, value: JsonValue) -> JsonMember {
        JsonMember {
            name: name.into(),
            value,
        }
    }

    #[test]
    fn semantic_object_equality_ignores_order() {
        let left = JsonObject::new(vec![
            member("a", JsonValue::Null),
            member("b", JsonValue::Bool(true)),
        ])
        .unwrap();
        let right = JsonObject::new(vec![
            member("b", JsonValue::Bool(true)),
            member("a", JsonValue::Null),
        ])
        .unwrap();
        assert_eq!(left, right);
    }

    #[test]
    fn parsed_members_retain_duplicates_but_semantic_object_rejects_them() {
        let parsed = JsonMemberSequence(vec![
            member("x", JsonValue::Null),
            member("x", JsonValue::Bool(false)),
        ]);
        assert_eq!(parsed.0.len(), 2);
        assert!(RejectDuplicates.interpret(parsed).is_err());
    }

    #[test]
    fn datatype_family_exposes_composed_array_and_object_lists() {
        use DatatypeFamilyExpr as D;

        let family = json_value_family();
        assert_eq!(family.validate(), Ok(()));
        assert!(family.is_recursive());
        assert_eq!(
            family,
            D::Sum(vec![
                D::One,
                D::Param(JsonParameter::Bool),
                D::Param(JsonParameter::Decimal),
                D::Param(JsonParameter::String),
                D::least(D::Sum(vec![
                    D::One,
                    D::Product(vec![D::FamilyVar, D::Bound(0)])
                ])),
                D::least(D::Sum(vec![
                    D::One,
                    D::Product(vec![
                        D::Product(vec![D::Param(JsonParameter::String), D::FamilyVar]),
                        D::Bound(0)
                    ])
                ]))
            ])
        );
        assert_eq!(json_value_polynomial(), family);
    }

    #[test]
    fn datatype_family_derives_nested_list_interpretation_and_map() {
        use covalence_inductive::{
            SymbolicFamilyArrow as A, SymbolicFamilyBackend, SymbolicFamilyObject as O,
            ValidatedDatatypeFamily, interpret_family, map_family, symbolic_arrow,
        };

        let family = ValidatedDatatypeFamily::try_from(json_value_family()).unwrap();
        let source = O::Parameter(JsonParameter::Bool);
        let target = O::Parameter(JsonParameter::Decimal);
        let arrow = symbolic_arrow(source.clone(), target.clone(), "value-map");

        let O::Sum(layer) = interpret_family(&SymbolicFamilyBackend, &family, &source).unwrap()
        else {
            panic!("JSON is a six-way sum");
        };
        assert_eq!(layer.len(), JsonConstructor::ALL.len());
        assert!(matches!(layer[4], O::Fixpoint { .. }));
        assert!(matches!(layer[5], O::Fixpoint { .. }));

        let A::Sum(mapped) =
            map_family(&SymbolicFamilyBackend, &family, &source, &target, &arrow).unwrap()
        else {
            panic!("JSON map follows the six-way sum");
        };
        assert_eq!(mapped.len(), JsonConstructor::ALL.len());
        assert!(matches!(mapped[4], A::Fixpoint { .. }));
        assert!(matches!(mapped[5], A::Fixpoint { .. }));
    }

    #[test]
    fn syntax_parser_retains_nested_duplicate_members_in_order() {
        let (value, witness) = JsonSyntaxParser
            .parse_diagnostic(br#"{"x":1,"x":{"y":2,"y":3}}"#)
            .unwrap();
        let ParsedJsonValue::Object(members) = value else {
            panic!("expected object");
        };
        assert_eq!(members.len(), 2);
        assert_eq!(members[0].name, JsonString::from("x"));
        assert_eq!(members[1].name, JsonString::from("x"));
        let ParsedJsonValue::Object(nested) = &members[1].value else {
            panic!("expected nested object");
        };
        assert_eq!(nested.len(), 2);
        assert_eq!(witness.consumed, br#"{"x":1,"x":{"y":2,"y":3}}"#.len());
        assert!(JsonParser.parse(br#"{"x":1,"x":2}"#).unwrap().is_none());
    }

    #[test]
    fn numbers_are_exact_canonical_decimals() {
        let Some((JsonValue::Array(values), _)) =
            JsonParser.parse(br#"[1.2300e2,-0,4e-1000]"#).unwrap()
        else {
            panic!("expected semantic array");
        };
        let JsonValue::Number(first) = &values[0] else {
            panic!("expected number");
        };
        assert_eq!(first.digits(), &[1, 2, 3]);
        assert_eq!(first.exponent(), &Int::zero());
        let JsonValue::Number(zero) = &values[1] else {
            panic!("expected number");
        };
        assert!(!zero.is_negative());
        assert_eq!(zero.digits(), &[0]);
        let JsonValue::Number(tiny) = &values[2] else {
            panic!("expected number");
        };
        assert_eq!(tiny.exponent(), &Int::from(-1000_i64));
    }

    #[test]
    fn string_decoding_preserves_unpaired_surrogates() {
        let Some((JsonValue::Array(values), _)) = JsonParser
            .parse(b"[\"\\uD834\\uDD1E\",\"\\uD800\",\"\xc3\xa9\"]")
            .unwrap()
        else {
            panic!("expected array");
        };
        assert_eq!(
            values[0],
            JsonValue::String(JsonString(vec![JsonCodePoint::Scalar('\u{1d11e}')]))
        );
        assert_eq!(
            values[1],
            JsonValue::String(JsonString(vec![JsonCodePoint::UnpairedSurrogate(
                JsonSurrogate::new(0xd800).unwrap()
            )]))
        );
        assert_eq!(values[2], JsonValue::String(JsonString::from("é")));
    }

    #[test]
    fn semantic_per_relates_distinct_encodings_and_object_orders() {
        let same = JsonParser
            .same_interpretation(br#"{"a":"a","b":1.0}"#, br#"{ "b": 10e-1, "a": "\u0061" }"#)
            .unwrap();
        assert!(same.is_some());
        assert!(
            JsonParser
                .same_interpretation(br#"{"a":1}"#, br#"{"a":2}"#)
                .unwrap()
                .is_none()
        );
        assert!(
            JsonParser
                .same_interpretation(br#"{"a":1,"a":1}"#, br#"{"a":1}"#)
                .unwrap()
                .is_none()
        );
    }

    #[test]
    fn parser_rejects_non_rfc_number_and_string_forms() {
        for invalid in [
            &b"01"[..],
            &b"1."[..],
            &b"+1"[..],
            &b"NaN"[..],
            &b"\"line\nbreak\""[..],
            &b"true false"[..],
            &[b'"', 0xff, b'"'][..],
        ] {
            assert!(
                JsonSyntaxParser.parse(invalid).unwrap().is_none(),
                "accepted {invalid:?}"
            );
        }
    }

    #[test]
    fn prefix_and_exact_parsing_have_distinct_consumption_contracts() {
        let source = b"skip [1.0] \n next";
        let ParseAttempt::Match(prefix) =
            PartialPrefixParser::parse_prefix(&JsonParser, source, 5).unwrap()
        else {
            panic!("expected prefix match");
        };
        assert_eq!(prefix.consumed, Span { start: 5, end: 13 });
        assert_eq!(prefix.remainder, 13);
        assert_eq!(prefix.witness.consumed, 8);
        assert!(!prefix.is_complete(source.len()));

        let ParseAttempt::NoMatch(diagnostic) =
            PartialExactParser::parse_exact(&JsonParser, b"[1.0] next").unwrap()
        else {
            panic!("exact parsing must reject a remainder");
        };
        assert_eq!(diagnostic.offset, 6);
        assert_eq!(diagnostic.kind, JsonParseErrorKind::TrailingInput);
    }

    #[test]
    fn malformed_utf8_diagnostic_points_at_the_invalid_lead_byte() {
        let source = [b'"', 0xc3, 0xa9, 0xff, b'"'];
        let ParseAttempt::NoMatch(diagnostic) =
            PartialExactParser::parse_exact(&JsonSyntaxParser, &source).unwrap()
        else {
            panic!("malformed UTF-8 must not parse");
        };
        assert_eq!(diagnostic.offset, 3);
        assert_eq!(diagnostic.kind, JsonParseErrorKind::InvalidUtf8);
    }

    #[test]
    fn prefix_syntax_retains_duplicates_while_semantics_and_per_reject_them() {
        let source = br#"{"x":1,"x":2} suffix"#;
        let ParseAttempt::Match(parsed) =
            PartialPrefixParser::parse_prefix(&JsonSyntaxParser, source, 0).unwrap()
        else {
            panic!("syntax parser must retain duplicate members");
        };
        let ParsedJsonValue::Object(members) = parsed.value else {
            panic!("expected object");
        };
        assert_eq!(members.len(), 2);
        assert_eq!(&source[parsed.remainder..], b"suffix");

        let ParseAttempt::NoMatch(diagnostic) =
            PartialPrefixParser::parse_prefix(&JsonParser, source, 0).unwrap()
        else {
            panic!("semantic parser must reject duplicate names");
        };
        assert_eq!(diagnostic.kind, JsonParseErrorKind::DuplicateName);
        assert!(
            JsonParser
                .same_interpretation(br#"{"x":1,"x":2}"#, br#"{"x":2}"#)
                .unwrap()
                .is_none()
        );
    }

    #[test]
    fn checked_nesting_limit_accepts_boundary_and_rejects_next_container() {
        let four = JsonNestingLimit::new(4).unwrap();
        assert!(
            JsonSyntaxParser
                .parse_diagnostic_with_limit(b"[[[[0]]]]", four)
                .is_ok()
        );

        let error = JsonSyntaxParser
            .parse_diagnostic_with_limit(b"[[[[[0]]]]]", four)
            .unwrap_err();
        assert_eq!(error.offset, 4);
        assert_eq!(
            error.kind,
            JsonParseErrorKind::NestingLimitExceeded { limit: 4 }
        );

        let scalar_only = JsonNestingLimit::new(0).unwrap();
        assert!(
            JsonParser
                .parse_diagnostic_with_limit(b"1.2300e2", scalar_only)
                .is_ok()
        );
        assert_eq!(
            JsonParser
                .parse_diagnostic_with_limit(b"[]", scalar_only)
                .unwrap_err()
                .kind,
            JsonParseErrorKind::NestingLimitExceeded { limit: 0 }
        );
    }

    #[test]
    fn adversarial_nesting_is_rejected_before_recursive_stack_growth() {
        let source = vec![b'['; 100_000];
        let error = JsonSyntaxParser.parse_diagnostic(&source).unwrap_err();
        assert_eq!(error.offset, JsonNestingLimit::DEFAULT.get());
        assert_eq!(
            error.kind,
            JsonParseErrorKind::NestingLimitExceeded {
                limit: JsonNestingLimit::DEFAULT.get()
            }
        );
        assert!(JsonNestingLimit::new(JsonNestingLimit::MAX_SUPPORTED + 1).is_none());
    }
}
