//! Proper (capture-free) regular expressions.
//!
//! [`Regex<A>`] is an algebraic AST for regular languages over an alphabet
//! `A: Ord + Clone`. It is **proper** in the sense that there are no
//! capturing groups, named submatches, or back-references — the surface
//! syntax `(...)` is treated as a non-capturing group.
//!
//! Smart constructors ([`Regex::concat`], [`Regex::alt`], etc.) perform
//! light algebraic normalisation:
//!
//! - `Concat` flattens nested concats, drops `Eps`, and short-circuits to
//!   [`Regex::Empty`] if any operand is `Empty`.
//! - `Alt` flattens nested alts and drops `Empty`.
//! - Single-element `Concat`/`Alt` collapse to that element.
//!
//! No further normalisation (sorting, de-duplication, Brzozowski-style
//! simplification) is performed: the AST mirrors the surface as closely
//! as possible so a round-trip back to source / SpecTec is information-
//! preserving on the supported subset.
//!
//! # Parsing
//!
//! [`parse_regex`] reads a standard regex string into [`Regex<char>`].
//! Supported surface features:
//!
//! - alternation `e₁|e₂`
//! - concatenation by juxtaposition
//! - quantifiers `e*`, `e+`, `e?`, `e{n}`, `e{n,}`, `e{n,m}`
//! - non-capturing groups `(...)`
//! - character classes `[abc]`, `[^abc]`, `[a-z0-9_]`
//! - `.` — matches any single character (any Unicode scalar value)
//! - escapes: `\\`, `\.`, `\*`, `\+`, `\?`, `\(`, `\)`, `\[`, `\]`,
//!   `\{`, `\}`, `\|`, `\^`, `\$`, `\-`, `\/`, `\n`, `\t`, `\r`, `\0`,
//!   `\xHH`, `\u{H...}`
//!
//! Intentionally **unsupported**: capture groups, back-references, the
//! anchors `^`/`$`, look-around, named character classes `\d`/`\w`/`\s`.
//! Adding them later does not change the type [`Regex<A>`].

use std::fmt;
use std::sync::Arc;

/// A proper regular expression over an alphabet `A`.
///
/// Variants split into:
///
/// - Constants — [`Empty`](Regex::Empty) (`∅`, matches nothing) and
///   [`Eps`](Regex::Eps) (`ε`, matches only the empty string).
/// - Atoms — [`Lit`](Regex::Lit) (single letter) and [`Class`](Regex::Class)
///   (set-of-letters class).
/// - Combinators — [`Concat`](Regex::Concat) and [`Alt`](Regex::Alt).
/// - Repetition — [`Star`](Regex::Star), [`Plus`](Regex::Plus),
///   [`Opt`](Regex::Opt), [`Rep`](Regex::Rep).
///
/// `Plus`, `Opt`, and `Rep` are kept distinct from `Star` rather than
/// desugared. They are semantically reducible (`e+ = e e*`, `e? = ε | e`,
/// `e{0,n} = ε | e | ... | eⁿ`) but preserving them lets us round-trip
/// back to surface syntax (or SpecTec `Iter`) without losing structure.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Regex<A> {
    /// `∅` — the empty language (matches no string at all).
    Empty,
    /// `ε` — matches only the empty string.
    Eps,
    /// Single-letter literal.
    Lit(A),
    /// Character class — match any letter in the (possibly negated) union of ranges.
    Class(Class<A>),
    /// Sequential composition `r₁ r₂ ... rₙ`. By convention an empty
    /// vector equals [`Eps`](Regex::Eps); smart constructor
    /// [`Regex::concat`] always collapses that case.
    Concat(Vec<Regex<A>>),
    /// Alternation `r₁ | r₂ | ... | rₙ`. By convention an empty vector
    /// equals [`Empty`](Regex::Empty); [`Regex::alt`] always collapses that case.
    Alt(Vec<Regex<A>>),
    /// Kleene star: `r*`.
    Star(Arc<Regex<A>>),
    /// One-or-more: `r+`.
    Plus(Arc<Regex<A>>),
    /// Optional: `r?`.
    Opt(Arc<Regex<A>>),
    /// Bounded repetition `r{min, max}`. `max = None` means unbounded.
    Rep {
        inner: Arc<Regex<A>>,
        min: u32,
        max: Option<u32>,
    },
}

/// A character-class atom: a (possibly negated) set of ranges over `A`.
///
/// Ranges are inclusive on both ends. The class is *not* required to be
/// sorted or merged — the smart constructors do not canonicalise, so two
/// `Class` values that denote the same set may compare unequal.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Class<A> {
    pub negated: bool,
    pub ranges: Vec<ClassRange<A>>,
}

/// Inclusive `[lo, hi]` range in a character class.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct ClassRange<A> {
    pub lo: A,
    pub hi: A,
}

impl<A> Class<A> {
    /// Positive class containing exactly the given inclusive ranges.
    pub fn new(ranges: Vec<ClassRange<A>>) -> Self {
        Self {
            negated: false,
            ranges,
        }
    }

    /// Negated class: matches any letter *not* in any of the ranges.
    pub fn negated(ranges: Vec<ClassRange<A>>) -> Self {
        Self {
            negated: true,
            ranges,
        }
    }

    /// Positive class from a list of single letters.
    pub fn from_letters(letters: impl IntoIterator<Item = A>) -> Self
    where
        A: Clone,
    {
        let ranges = letters
            .into_iter()
            .map(|c| ClassRange {
                lo: c.clone(),
                hi: c,
            })
            .collect();
        Self::new(ranges)
    }
}

impl<A> ClassRange<A> {
    pub fn new(lo: A, hi: A) -> Self {
        Self { lo, hi }
    }

    /// Single-letter range.
    pub fn single(letter: A) -> Self
    where
        A: Clone,
    {
        Self {
            lo: letter.clone(),
            hi: letter,
        }
    }
}

impl<A> Regex<A> {
    pub fn empty() -> Self {
        Regex::Empty
    }

    pub fn eps() -> Self {
        Regex::Eps
    }

    pub fn lit(a: A) -> Self {
        Regex::Lit(a)
    }

    pub fn class(c: Class<A>) -> Self {
        Regex::Class(c)
    }

    /// Concatenate a sequence of regexes, applying the obvious algebraic
    /// simplifications:
    ///
    /// - flatten nested `Concat` into the surrounding sequence;
    /// - drop `Eps` operands;
    /// - if any operand is `Empty`, the whole concatenation is `Empty`;
    /// - an empty sequence becomes `Eps`;
    /// - a single-element sequence becomes that element.
    pub fn concat(items: impl IntoIterator<Item = Regex<A>>) -> Self {
        let mut out: Vec<Regex<A>> = Vec::new();
        for item in items {
            match item {
                Regex::Empty => return Regex::Empty,
                Regex::Eps => {}
                Regex::Concat(inner) => {
                    for x in inner {
                        match x {
                            Regex::Empty => return Regex::Empty,
                            Regex::Eps => {}
                            other => out.push(other),
                        }
                    }
                }
                other => out.push(other),
            }
        }
        match out.len() {
            0 => Regex::Eps,
            1 => out.into_iter().next().expect("len == 1"),
            _ => Regex::Concat(out),
        }
    }

    /// Alternate a list of regexes, with the dual simplifications to
    /// [`Regex::concat`]:
    ///
    /// - flatten nested `Alt`;
    /// - drop `Empty` operands;
    /// - an empty sequence becomes `Empty`;
    /// - a single-element sequence becomes that element.
    ///
    /// Duplicate alternatives are **not** removed: alphabet equality
    /// would force `A: PartialEq` here, and structural normalisation of
    /// alts is a separate pass we may add later.
    pub fn alt(items: impl IntoIterator<Item = Regex<A>>) -> Self {
        let mut out: Vec<Regex<A>> = Vec::new();
        for item in items {
            match item {
                Regex::Empty => {}
                Regex::Alt(inner) => {
                    for x in inner {
                        if !matches!(x, Regex::Empty) {
                            out.push(x);
                        }
                    }
                }
                other => out.push(other),
            }
        }
        match out.len() {
            0 => Regex::Empty,
            1 => out.into_iter().next().expect("len == 1"),
            _ => Regex::Alt(out),
        }
    }

    pub fn star(self) -> Self {
        match self {
            Regex::Empty | Regex::Eps => Regex::Eps,
            Regex::Star(_) | Regex::Plus(_) => self,
            other => Regex::Star(Arc::new(other)),
        }
    }

    pub fn plus(self) -> Self {
        match self {
            Regex::Empty => Regex::Empty,
            Regex::Eps => Regex::Eps,
            Regex::Star(_) => self,
            other => Regex::Plus(Arc::new(other)),
        }
    }

    pub fn opt(self) -> Self {
        match self {
            Regex::Empty | Regex::Eps => Regex::Eps,
            Regex::Star(_) | Regex::Opt(_) => self,
            other => Regex::Opt(Arc::new(other)),
        }
    }

    /// Bounded repetition with the algebraic shortcuts:
    /// `r{0,0}` is `ε`, `r{1,1}` is `r`, repetition of `Empty` is `Empty`
    /// (unless `min == 0`, in which case it is `Eps`), repetition of
    /// `Eps` is `Eps`.
    pub fn rep(self, min: u32, max: Option<u32>) -> Self {
        if let Some(m) = max {
            if m < min {
                return Regex::Empty;
            }
            if m == 0 {
                return Regex::Eps;
            }
        }
        match (&self, min, max) {
            (_, 1, Some(1)) => self,
            (Regex::Eps, _, _) => Regex::Eps,
            (Regex::Empty, 0, _) => Regex::Eps,
            (Regex::Empty, _, _) => Regex::Empty,
            _ => Regex::Rep {
                inner: Arc::new(self),
                min,
                max,
            },
        }
    }
}

impl<A: Clone + PartialOrd> Regex<A> {
    /// Whether the language of this regex contains the empty string.
    /// Total and structural: no derivative computation, no fixed point.
    pub fn nullable(&self) -> bool {
        match self {
            Regex::Empty => false,
            Regex::Eps => true,
            Regex::Lit(_) => false,
            Regex::Class(_) => false,
            Regex::Concat(items) => items.iter().all(Regex::nullable),
            Regex::Alt(items) => items.iter().any(Regex::nullable),
            Regex::Star(_) | Regex::Opt(_) => true,
            Regex::Plus(inner) => inner.nullable(),
            Regex::Rep { inner, min, .. } => *min == 0 || inner.nullable(),
        }
    }
}

// ============================================================================
// Display — pretty-print Regex<A> for any `A: RegexLetter`.
// ============================================================================

/// Alphabet letters that know how to print and parse themselves in the
/// two regex contexts: as a top-level literal (where regex
/// metacharacters must be escaped) and inside a character class (where
/// the class-only specials `] - ^` must be escaped).
///
/// The trait is the single hook for both [`fmt::Display`] and
/// [`parse_regex`] on [`Regex<A>`]. To add a new alphabet
/// (`Regex<UnicodeScalar>`, `Regex<wasm::Op>`, …), implement this trait
/// — no other changes are needed.
///
/// **For `Regex<char>`:** displays in the syntax [`parse_regex`]
/// consumes (`\n`/`\t`/`\r`/`\0`, control chars as `\u{HH}`, others
/// verbatim). Source `char`s pass through as-is. `\xHH` covers
/// `0x00..=0xFF`. `\u{...}` covers all Unicode scalars.
///
/// **For `Regex<u8>`:** displays in byte-regex syntax (printable ASCII
/// verbatim, others as `\xHH`). The parser ([`parse_regex_u8`]) requires
/// non-ASCII bytes to be written via `\xHH` and rejects `\u{...}` because
/// the UTF-8 / byte mapping is ambiguous and would silently expand to a
/// multi-byte sequence.
pub trait RegexLetter: Copy + Eq {
    /// Format this letter as a top-level literal in a regex.
    fn fmt_lit(self, f: &mut fmt::Formatter<'_>) -> fmt::Result;

    /// Format this letter as one position of a character class.
    fn fmt_class(self, f: &mut fmt::Formatter<'_>) -> fmt::Result;

    /// Render [`Regex::Empty`]. The empty language has no native surface
    /// syntax in most regex dialects; the convention here is a negated
    /// class spanning the whole alphabet.
    fn write_empty(f: &mut fmt::Formatter<'_>) -> fmt::Result;

    /// Inclusive lower bound of the alphabet — `'\0'` for `char`, `0` for `u8`.
    /// Used to desugar `.` into a class.
    fn min_letter() -> Self;

    /// Inclusive upper bound of the alphabet — `'\u{10FFFF}'` for `char`,
    /// `0xFF` for `u8`. Used to desugar `.` into a class.
    fn max_letter() -> Self;

    /// Promote a source character read directly from the input.
    /// For `char`, this is the identity. For `u8`, only ASCII chars
    /// succeed — non-ASCII source bytes must be written as `\xHH`.
    fn from_source_char(c: char) -> Option<Self>;

    /// Build a letter from a `\xHH` escape (an arbitrary byte value).
    /// For `char`, every byte is a valid scalar (`0x00..=0xFF`).
    /// For `u8`, the identity.
    fn from_byte_escape(b: u8) -> Option<Self>;

    /// Build a letter from a `\u{...}` escape (a Unicode scalar). For
    /// `char`, the identity. For `u8`, always `None` — see the trait
    /// note for the rationale.
    fn from_unicode_escape(c: char) -> Option<Self>;
}

impl RegexLetter for char {
    fn fmt_lit(self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            '\\' | '.' | '*' | '+' | '?' | '(' | ')' | '[' | ']' | '{' | '}' | '|' | '^' | '$' => {
                write!(f, "\\{}", self)
            }
            '\n' => f.write_str("\\n"),
            '\t' => f.write_str("\\t"),
            '\r' => f.write_str("\\r"),
            '\0' => f.write_str("\\0"),
            c if (c as u32) < 0x20 || (c as u32) == 0x7F => write!(f, "\\u{{{:X}}}", c as u32),
            c => write!(f, "{}", c),
        }
    }

    fn fmt_class(self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            '\\' | ']' | '-' | '^' => write!(f, "\\{}", self),
            '\n' => f.write_str("\\n"),
            '\t' => f.write_str("\\t"),
            '\r' => f.write_str("\\r"),
            '\0' => f.write_str("\\0"),
            c if (c as u32) < 0x20 || (c as u32) == 0x7F => write!(f, "\\u{{{:X}}}", c as u32),
            c => write!(f, "{}", c),
        }
    }

    fn write_empty(f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("(?:[^\\u{0}-\\u{10FFFF}])")
    }

    fn min_letter() -> Self {
        '\0'
    }
    fn max_letter() -> Self {
        '\u{10FFFF}'
    }
    fn from_source_char(c: char) -> Option<Self> {
        Some(c)
    }
    fn from_byte_escape(b: u8) -> Option<Self> {
        char::from_u32(u32::from(b))
    }
    fn from_unicode_escape(c: char) -> Option<Self> {
        Some(c)
    }
}

impl RegexLetter for u8 {
    fn fmt_lit(self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            b'\\' | b'.' | b'*' | b'+' | b'?' | b'(' | b')' | b'[' | b']' | b'{' | b'}' | b'|'
            | b'^' | b'$' => write!(f, "\\{}", self as char),
            b'\n' => f.write_str("\\n"),
            b'\t' => f.write_str("\\t"),
            b'\r' => f.write_str("\\r"),
            0 => f.write_str("\\0"),
            0x20..=0x7E => write!(f, "{}", self as char),
            b => write!(f, "\\x{:02X}", b),
        }
    }

    fn fmt_class(self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            b'\\' | b']' | b'-' | b'^' => write!(f, "\\{}", self as char),
            b'\n' => f.write_str("\\n"),
            b'\t' => f.write_str("\\t"),
            b'\r' => f.write_str("\\r"),
            0 => f.write_str("\\0"),
            0x20..=0x7E => write!(f, "{}", self as char),
            b => write!(f, "\\x{:02X}", b),
        }
    }

    fn write_empty(f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("(?:[^\\x00-\\xFF])")
    }

    fn min_letter() -> Self {
        0
    }
    fn max_letter() -> Self {
        0xFF
    }
    fn from_source_char(c: char) -> Option<Self> {
        if c.is_ascii() { Some(c as u8) } else { None }
    }
    fn from_byte_escape(b: u8) -> Option<Self> {
        Some(b)
    }
    fn from_unicode_escape(_c: char) -> Option<Self> {
        None
    }
}

/// Precedence levels used to insert parentheses on display.
/// Higher value binds tighter.
#[derive(Copy, Clone, Eq, PartialEq, PartialOrd, Ord)]
enum Prec {
    Alt = 0,
    Concat = 1,
    Suffix = 2,
}

impl<A: RegexLetter> fmt::Display for Regex<A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write_regex(f, self, Prec::Alt)
    }
}

fn write_regex<A: RegexLetter>(
    f: &mut fmt::Formatter<'_>,
    r: &Regex<A>,
    outer: Prec,
) -> fmt::Result {
    match r {
        Regex::Empty => A::write_empty(f),
        Regex::Eps => f.write_str("(?:)"),
        Regex::Lit(c) => c.fmt_lit(f),
        Regex::Class(c) => write_class(f, c),
        Regex::Concat(items) => {
            let needs_parens = outer > Prec::Concat;
            if needs_parens {
                f.write_str("(?:")?;
            }
            for item in items {
                write_regex(f, item, Prec::Concat)?;
            }
            if needs_parens {
                f.write_str(")")?;
            }
            Ok(())
        }
        Regex::Alt(items) => {
            let needs_parens = outer > Prec::Alt;
            if needs_parens {
                f.write_str("(?:")?;
            }
            let mut first = true;
            for item in items {
                if !first {
                    f.write_str("|")?;
                }
                first = false;
                write_regex(f, item, Prec::Alt)?;
            }
            if needs_parens {
                f.write_str(")")?;
            }
            Ok(())
        }
        Regex::Star(inner) => write_suffix(f, inner, "*"),
        Regex::Plus(inner) => write_suffix(f, inner, "+"),
        Regex::Opt(inner) => write_suffix(f, inner, "?"),
        Regex::Rep { inner, min, max } => {
            let suffix = match max {
                None => format!("{{{},}}", min),
                Some(m) if *m == *min => format!("{{{}}}", min),
                Some(m) => format!("{{{},{}}}", min, m),
            };
            write_suffix(f, inner, &suffix)
        }
    }
}

fn write_suffix<A: RegexLetter>(
    f: &mut fmt::Formatter<'_>,
    inner: &Regex<A>,
    suffix: &str,
) -> fmt::Result {
    let needs_parens = matches!(
        inner,
        Regex::Alt(_)
            | Regex::Concat(_)
            | Regex::Star(_)
            | Regex::Plus(_)
            | Regex::Opt(_)
            | Regex::Rep { .. }
    );
    if needs_parens {
        // Once we've added our own `(?:...)`, recurse at the lowest
        // precedence so `write_regex` doesn't add a second pair.
        f.write_str("(?:")?;
        write_regex(f, inner, Prec::Alt)?;
        f.write_str(")")?;
    } else {
        write_regex(f, inner, Prec::Suffix)?;
    }
    f.write_str(suffix)
}

fn write_class<A: RegexLetter>(f: &mut fmt::Formatter<'_>, c: &Class<A>) -> fmt::Result {
    f.write_str("[")?;
    if c.negated {
        f.write_str("^")?;
    }
    for r in &c.ranges {
        if r.lo == r.hi {
            r.lo.fmt_class(f)?;
        } else {
            r.lo.fmt_class(f)?;
            f.write_str("-")?;
            r.hi.fmt_class(f)?;
        }
    }
    f.write_str("]")
}

// ============================================================================
// Parser — &str -> Regex<A> for any A: RegexLetter
// ============================================================================

/// Errors from [`parse_regex`] / [`parse_regex_u8`]. Positions are byte
/// offsets into the input.
#[derive(Debug, Clone, Eq, PartialEq, thiserror::Error)]
pub enum ParseError {
    #[error("unexpected end of input at byte {at}")]
    UnexpectedEof { at: usize },
    #[error("unexpected character {ch:?} at byte {at}")]
    Unexpected { ch: char, at: usize },
    #[error("unmatched '(' at byte {at}")]
    UnclosedGroup { at: usize },
    #[error("unmatched ')' at byte {at}")]
    StrayCloseParen { at: usize },
    #[error("unclosed character class at byte {at}")]
    UnclosedClass { at: usize },
    #[error("empty character class at byte {at}")]
    EmptyClass { at: usize },
    #[error("invalid character range at byte {at}: {lo:?}-{hi:?} (lo > hi)")]
    BadRange { lo: u32, hi: u32, at: usize },
    #[error("invalid quantifier at byte {at}")]
    BadQuantifier { at: usize },
    #[error("quantifier applied to nothing at byte {at}")]
    NothingToRepeat { at: usize },
    #[error("invalid escape sequence at byte {at}: {detail}")]
    BadEscape { at: usize, detail: String },
    #[error("invalid codepoint {value:#x} at byte {at}")]
    BadCodepoint { value: u32, at: usize },
    /// A source character (or escape) does not name a valid letter in the
    /// target alphabet. For `Regex<u8>` this fires when the input contains
    /// non-ASCII bytes or uses `\u{...}` for non-ASCII scalars.
    #[error("character {c:?} is not in the target alphabet at byte {at}")]
    OutOfAlphabet { c: char, at: usize },
}

/// Parse a standard regex string into a proper [`Regex<char>`].
///
/// See the [module docs](self) for the supported surface syntax.
pub fn parse_regex(input: &str) -> Result<Regex<char>, ParseError> {
    parse_regex_generic(input)
}

/// Parse a standard regex string into a proper [`Regex<u8>`].
///
/// The surface syntax matches [`parse_regex`], with two differences
/// driven by the byte alphabet:
///
/// - Non-ASCII bytes (>= `0x80`) cannot appear in the source verbatim;
///   write them as `\xHH`. (The input itself is `&str` and therefore
///   UTF-8 — a literal `é` would have to expand to two bytes, which is
///   not what you mean when writing a byte regex.)
/// - `\u{...}` is rejected. Use `\xHH`.
///
/// Everything else — `.`, `|`, `*`, `+`, `?`, `{m,n}`, `[...]`, ranges,
/// `\n`/`\t`/`\r`/`\0`, escapes of regex metacharacters — is identical.
/// `.` matches any byte (`0x00..=0xFF`).
pub fn parse_regex_u8(input: &str) -> Result<Regex<u8>, ParseError> {
    parse_regex_generic(input)
}

fn parse_regex_generic<A: RegexLetter>(input: &str) -> Result<Regex<A>, ParseError> {
    let mut p = Parser::<A>::new(input);
    let r = p.parse_alt()?;
    if p.pos < p.bytes.len() {
        // The only way we exit parse_alt without consuming everything is a
        // stray ')'.
        return Err(ParseError::StrayCloseParen { at: p.pos });
    }
    Ok(r)
}

struct Parser<'a, A> {
    bytes: &'a [u8],
    src: &'a str,
    pos: usize,
    _marker: core::marker::PhantomData<A>,
}

impl<'a, A: RegexLetter> Parser<'a, A> {
    fn new(src: &'a str) -> Self {
        Self {
            bytes: src.as_bytes(),
            src,
            pos: 0,
            _marker: core::marker::PhantomData,
        }
    }

    fn peek_char(&self) -> Option<(char, usize)> {
        if self.pos >= self.bytes.len() {
            return None;
        }
        let rest = &self.src[self.pos..];
        let c = rest.chars().next()?;
        Some((c, c.len_utf8()))
    }

    fn bump_char(&mut self) -> Option<char> {
        let (c, w) = self.peek_char()?;
        self.pos = self.pos.checked_add(w).expect("pos in range");
        Some(c)
    }

    fn eat_byte(&mut self, b: u8) -> bool {
        if self.bytes.get(self.pos) == Some(&b) {
            self.pos = self.pos.checked_add(1).expect("pos in range");
            true
        } else {
            false
        }
    }

    fn parse_alt(&mut self) -> Result<Regex<A>, ParseError> {
        let mut branches = vec![self.parse_concat()?];
        while self.eat_byte(b'|') {
            branches.push(self.parse_concat()?);
        }
        Ok(Regex::alt(branches))
    }

    fn parse_concat(&mut self) -> Result<Regex<A>, ParseError> {
        let mut items: Vec<Regex<A>> = Vec::new();
        loop {
            match self.peek_char() {
                None => break,
                Some((c, _)) if c == '|' || c == ')' => break,
                _ => {}
            }
            items.push(self.parse_quantified()?);
        }
        Ok(Regex::concat(items))
    }

    fn parse_quantified(&mut self) -> Result<Regex<A>, ParseError> {
        let start = self.pos;
        let atom = self.parse_atom()?;
        match self.peek_char() {
            Some(('*', _)) => {
                self.bump_char();
                Ok(atom.star())
            }
            Some(('+', _)) => {
                self.bump_char();
                Ok(atom.plus())
            }
            Some(('?', _)) => {
                self.bump_char();
                Ok(atom.opt())
            }
            Some(('{', _)) => {
                // Try to parse `{n}`, `{n,}`, `{n,m}`. If parsing fails,
                // back off and treat `{` as a literal (lenient mode).
                let save = self.pos;
                match self.parse_brace_quant() {
                    Ok((min, max)) => Ok(atom.rep(min, max)),
                    Err(BraceQuantErr::NotAQuant) => {
                        self.pos = save;
                        // `{` was already consumed below in parse_brace_quant? no — we restore.
                        Ok(atom)
                    }
                    Err(BraceQuantErr::Bad(e)) => Err(e),
                }
            }
            _ => {
                // No quantifier — nothing more to do, but make sure the atom
                // wasn't itself empty-position (handled by parse_atom).
                let _ = start;
                Ok(atom)
            }
        }
    }

    fn parse_brace_quant(&mut self) -> Result<(u32, Option<u32>), BraceQuantErr> {
        let start = self.pos;
        if !self.eat_byte(b'{') {
            return Err(BraceQuantErr::NotAQuant);
        }
        let min = self.read_u32().ok_or(BraceQuantErr::NotAQuant)?;
        let max = if self.eat_byte(b',') {
            // `{n,}` or `{n,m}`
            if self.eat_byte(b'}') {
                None
            } else {
                let m = self
                    .read_u32()
                    .ok_or(BraceQuantErr::Bad(ParseError::BadQuantifier { at: start }))?;
                if !self.eat_byte(b'}') {
                    return Err(BraceQuantErr::Bad(ParseError::BadQuantifier { at: start }));
                }
                Some(m)
            }
        } else if self.eat_byte(b'}') {
            Some(min)
        } else {
            return Err(BraceQuantErr::Bad(ParseError::BadQuantifier { at: start }));
        };
        if let Some(m) = max {
            if m < min {
                return Err(BraceQuantErr::Bad(ParseError::BadQuantifier { at: start }));
            }
        }
        Ok((min, max))
    }

    fn read_u32(&mut self) -> Option<u32> {
        let start = self.pos;
        while let Some(&b) = self.bytes.get(self.pos) {
            if b.is_ascii_digit() {
                self.pos = self.pos.checked_add(1).expect("pos in range");
            } else {
                break;
            }
        }
        if self.pos == start {
            return None;
        }
        let s = &self.src[start..self.pos];
        s.parse::<u32>().ok()
    }

    fn parse_atom(&mut self) -> Result<Regex<A>, ParseError> {
        let at = self.pos;
        let (c, _) = self.peek_char().ok_or(ParseError::UnexpectedEof { at })?;
        match c {
            '(' => {
                self.bump_char();
                // Non-capturing group prefix `(?:` is accepted but optional.
                if self.eat_byte(b'?') {
                    if !self.eat_byte(b':') {
                        return Err(ParseError::BadEscape {
                            at: self.pos,
                            detail: "only `(?:` non-capturing groups are supported".into(),
                        });
                    }
                }
                let inner = self.parse_alt()?;
                if !self.eat_byte(b')') {
                    return Err(ParseError::UnclosedGroup { at });
                }
                Ok(inner)
            }
            ')' => Err(ParseError::StrayCloseParen { at }),
            '[' => {
                self.bump_char();
                self.parse_class(at)
            }
            '.' => {
                self.bump_char();
                Ok(Regex::Class(Class::new(vec![ClassRange {
                    lo: A::min_letter(),
                    hi: A::max_letter(),
                }])))
            }
            '*' | '+' | '?' | '{' => Err(ParseError::NothingToRepeat { at }),
            '|' | ']' | '}' => Err(ParseError::Unexpected { ch: c, at }),
            '\\' => {
                self.bump_char();
                let letter = self.parse_escape(at)?;
                Ok(Regex::Lit(letter))
            }
            _ => {
                let letter = self.read_source_letter(at)?;
                Ok(Regex::Lit(letter))
            }
        }
    }

    /// Consume one source character and convert it to a letter in the
    /// target alphabet, or fail with [`ParseError::OutOfAlphabet`].
    fn read_source_letter(&mut self, at: usize) -> Result<A, ParseError> {
        let c = self.bump_char().expect("peeked by caller");
        A::from_source_char(c).ok_or(ParseError::OutOfAlphabet { c, at })
    }

    /// Convert an ASCII metacharacter (already validated by the caller)
    /// into a letter. Used for `\\`, `\.`, `\*`, etc. — these are guaranteed
    /// to be representable in any [`RegexLetter`] alphabet we ship.
    fn meta_letter(c: char) -> A {
        debug_assert!(c.is_ascii(), "meta escapes are ASCII");
        A::from_source_char(c).expect("ASCII meta is in every alphabet")
    }

    fn parse_class(&mut self, open_at: usize) -> Result<Regex<A>, ParseError> {
        let negated = self.eat_byte(b'^');
        let mut ranges: Vec<ClassRange<A>> = Vec::new();
        // `]` as the very first char of a class is treated as a literal
        // (PCRE convention).
        let mut first = true;
        loop {
            let at = self.pos;
            let (c, _) = self
                .peek_char()
                .ok_or(ParseError::UnclosedClass { at: open_at })?;
            if c == ']' && !first {
                self.bump_char();
                break;
            }
            // Carry the raw codepoint of each endpoint so a BadRange error
            // can report a comparable value regardless of A.
            let (lo, lo_cp) = if c == '\\' {
                self.bump_char();
                let (letter, cp) = self.parse_escape_with_codepoint(at)?;
                (letter, cp)
            } else {
                let cp = u32::from(c);
                (self.read_source_letter(at)?, cp)
            };
            // Range continues if next is `-` AND the one after is not `]`.
            let (hi, hi_cp) = if self.bytes.get(self.pos) == Some(&b'-')
                && self.bytes.get(self.pos.saturating_add(1)) != Some(&b']')
            {
                self.bump_char(); // consume '-'
                let at2 = self.pos;
                let (c2, _) = self
                    .peek_char()
                    .ok_or(ParseError::UnclosedClass { at: open_at })?;
                if c2 == '\\' {
                    self.bump_char();
                    self.parse_escape_with_codepoint(at2)?
                } else {
                    let cp = u32::from(c2);
                    (self.read_source_letter(at2)?, cp)
                }
            } else {
                (lo, lo_cp)
            };
            if lo_cp > hi_cp {
                return Err(ParseError::BadRange {
                    lo: lo_cp,
                    hi: hi_cp,
                    at,
                });
            }
            ranges.push(ClassRange { lo, hi });
            first = false;
        }
        if ranges.is_empty() {
            return Err(ParseError::EmptyClass { at: open_at });
        }
        Ok(Regex::Class(Class { negated, ranges }))
    }

    fn parse_escape(&mut self, start: usize) -> Result<A, ParseError> {
        self.parse_escape_with_codepoint(start)
            .map(|(letter, _)| letter)
    }

    /// Parse an escape sequence and return the resulting letter *plus*
    /// the underlying codepoint. The codepoint is what the user wrote
    /// (`\xHH` -> `HH`, `\u{H...}` -> the scalar value, `\n` -> `0x0A`),
    /// independent of whether `A` could fit it; the parser uses this for
    /// range-ordering checks inside character classes.
    fn parse_escape_with_codepoint(&mut self, start: usize) -> Result<(A, u32), ParseError> {
        let c = self
            .bump_char()
            .ok_or(ParseError::UnexpectedEof { at: start })?;
        match c {
            '\\' | '.' | '*' | '+' | '?' | '(' | ')' | '[' | ']' | '{' | '}' | '|' | '^' | '$'
            | '-' | '/' => Ok((Self::meta_letter(c), u32::from(c))),
            'n' => Ok((Self::meta_letter('\n'), 0x0A)),
            't' => Ok((Self::meta_letter('\t'), 0x09)),
            'r' => Ok((Self::meta_letter('\r'), 0x0D)),
            '0' => Ok((Self::meta_letter('\0'), 0x00)),
            'x' => {
                let a = self.read_hex_digit().ok_or(ParseError::BadEscape {
                    at: start,
                    detail: "`\\x` needs two hex digits".into(),
                })?;
                let b = self.read_hex_digit().ok_or(ParseError::BadEscape {
                    at: start,
                    detail: "`\\x` needs two hex digits".into(),
                })?;
                let value = (a << 4) | b;
                let byte = u8::try_from(value).expect("two hex digits fit in u8");
                let letter = A::from_byte_escape(byte).ok_or(ParseError::OutOfAlphabet {
                    c: char::from(byte),
                    at: start,
                })?;
                Ok((letter, value))
            }
            'u' => {
                if !self.eat_byte(b'{') {
                    return Err(ParseError::BadEscape {
                        at: start,
                        detail: "expected `{` after `\\u`".into(),
                    });
                }
                let mut value: u32 = 0;
                let mut count: u32 = 0;
                loop {
                    match self.peek_char() {
                        Some(('}', _)) => {
                            self.bump_char();
                            break;
                        }
                        None => {
                            return Err(ParseError::BadEscape {
                                at: start,
                                detail: "unclosed `\\u{...}`".into(),
                            });
                        }
                        _ => {
                            let d = self.read_hex_digit().ok_or(ParseError::BadEscape {
                                at: start,
                                detail: "non-hex digit in `\\u{...}`".into(),
                            })?;
                            count = count.checked_add(1).ok_or(ParseError::BadEscape {
                                at: start,
                                detail: "too many digits in `\\u{...}`".into(),
                            })?;
                            if count > 6 {
                                return Err(ParseError::BadEscape {
                                    at: start,
                                    detail: "too many digits in `\\u{...}`".into(),
                                });
                            }
                            value = value.checked_shl(4).map(|v| v | d).ok_or(
                                ParseError::BadEscape {
                                    at: start,
                                    detail: "overflow in `\\u{...}`".into(),
                                },
                            )?;
                        }
                    }
                }
                if count == 0 {
                    return Err(ParseError::BadEscape {
                        at: start,
                        detail: "empty `\\u{}`".into(),
                    });
                }
                let scalar =
                    char::from_u32(value).ok_or(ParseError::BadCodepoint { value, at: start })?;
                let letter = A::from_unicode_escape(scalar).ok_or(ParseError::OutOfAlphabet {
                    c: scalar,
                    at: start,
                })?;
                Ok((letter, value))
            }
            other => Err(ParseError::BadEscape {
                at: start,
                detail: format!("unknown escape `\\{}`", other),
            }),
        }
    }

    fn read_hex_digit(&mut self) -> Option<u32> {
        let &b = self.bytes.get(self.pos)?;
        let d = match b {
            b'0'..=b'9' => u32::from(b - b'0'),
            b'a'..=b'f' => u32::from(b - b'a').checked_add(10)?,
            b'A'..=b'F' => u32::from(b - b'A').checked_add(10)?,
            _ => return None,
        };
        self.pos = self.pos.checked_add(1).expect("pos in range");
        Some(d)
    }
}

enum BraceQuantErr {
    /// `{` was followed by something that doesn't look like a quantifier.
    /// Treat it as a literal.
    NotAQuant,
    Bad(ParseError),
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn lit(c: char) -> Regex<char> {
        Regex::Lit(c)
    }

    fn cls(ranges: &[(char, char)]) -> Regex<char> {
        Regex::Class(Class::new(
            ranges
                .iter()
                .map(|&(a, b)| ClassRange { lo: a, hi: b })
                .collect(),
        ))
    }

    #[test]
    fn concat_flattens_and_drops_eps() {
        let r = Regex::concat([Regex::concat([lit('a'), Regex::Eps]), lit('b'), Regex::Eps]);
        assert_eq!(r, Regex::Concat(vec![lit('a'), lit('b')]));
    }

    #[test]
    fn concat_short_circuits_on_empty() {
        let r = Regex::concat([lit('a'), Regex::Empty, lit('b')]);
        assert_eq!(r, Regex::Empty);
    }

    #[test]
    fn alt_drops_empty_and_collapses_singleton() {
        let r = Regex::alt([Regex::Empty, lit('a'), Regex::Empty]);
        assert_eq!(r, lit('a'));
    }

    #[test]
    fn star_idempotent_on_star() {
        let r = lit('a').star().star();
        assert_eq!(r, Regex::Star(Arc::new(lit('a'))));
    }

    #[test]
    fn nullable_basics() {
        assert!(!lit('a').nullable());
        assert!(Regex::<char>::Eps.nullable());
        assert!(lit('a').star().nullable());
        assert!(!lit('a').plus().nullable());
        assert!(lit('a').opt().nullable());
        let r = Regex::concat([lit('a').opt(), lit('b').star()]);
        assert!(r.nullable());
    }

    #[test]
    fn parse_simple_literal() {
        assert_eq!(parse_regex("a").unwrap(), lit('a'));
    }

    #[test]
    fn parse_concat() {
        let r = parse_regex("abc").unwrap();
        assert_eq!(r, Regex::Concat(vec![lit('a'), lit('b'), lit('c')]),);
    }

    #[test]
    fn parse_alt() {
        let r = parse_regex("a|b|c").unwrap();
        assert_eq!(r, Regex::Alt(vec![lit('a'), lit('b'), lit('c')]));
    }

    #[test]
    fn parse_quantifiers() {
        assert_eq!(parse_regex("a*").unwrap(), Regex::Star(Arc::new(lit('a'))));
        assert_eq!(parse_regex("a+").unwrap(), Regex::Plus(Arc::new(lit('a'))));
        assert_eq!(parse_regex("a?").unwrap(), Regex::Opt(Arc::new(lit('a'))));
        assert_eq!(
            parse_regex("a{3}").unwrap(),
            Regex::Rep {
                inner: Arc::new(lit('a')),
                min: 3,
                max: Some(3)
            },
        );
        assert_eq!(
            parse_regex("a{2,}").unwrap(),
            Regex::Rep {
                inner: Arc::new(lit('a')),
                min: 2,
                max: None
            },
        );
        assert_eq!(
            parse_regex("a{2,5}").unwrap(),
            Regex::Rep {
                inner: Arc::new(lit('a')),
                min: 2,
                max: Some(5)
            },
        );
    }

    #[test]
    fn parse_groups() {
        let r = parse_regex("(ab)*").unwrap();
        assert_eq!(
            r,
            Regex::Star(Arc::new(Regex::Concat(vec![lit('a'), lit('b')]))),
        );
        let r = parse_regex("(?:ab)*").unwrap();
        assert_eq!(
            r,
            Regex::Star(Arc::new(Regex::Concat(vec![lit('a'), lit('b')]))),
        );
    }

    #[test]
    fn parse_class() {
        let r = parse_regex("[a-z0-9_]").unwrap();
        assert_eq!(r, cls(&[('a', 'z'), ('0', '9'), ('_', '_')]));
    }

    #[test]
    fn parse_negated_class() {
        let r = parse_regex("[^ab]").unwrap();
        let Regex::Class(c) = r else { panic!() };
        assert!(c.negated);
        assert_eq!(c.ranges.len(), 2);
    }

    #[test]
    fn parse_dot() {
        let r = parse_regex(".").unwrap();
        let Regex::Class(c) = r else { panic!() };
        assert!(!c.negated);
        assert_eq!(
            c.ranges,
            vec![ClassRange {
                lo: '\0',
                hi: '\u{10FFFF}'
            }]
        );
    }

    #[test]
    fn parse_escapes() {
        assert_eq!(parse_regex("\\.").unwrap(), lit('.'));
        assert_eq!(parse_regex("\\n").unwrap(), lit('\n'));
        assert_eq!(parse_regex("\\xFF").unwrap(), lit('\u{FF}'));
        assert_eq!(parse_regex("\\u{1F600}").unwrap(), lit('\u{1F600}'));
    }

    #[test]
    fn parse_errors() {
        assert!(matches!(
            parse_regex("("),
            Err(ParseError::UnclosedGroup { .. })
        ));
        assert!(matches!(
            parse_regex(")"),
            Err(ParseError::StrayCloseParen { .. })
        ));
        assert!(matches!(
            parse_regex("[abc"),
            Err(ParseError::UnclosedClass { .. })
        ));
        assert!(matches!(
            parse_regex("*"),
            Err(ParseError::NothingToRepeat { .. })
        ));
        assert!(matches!(
            parse_regex("[z-a]"),
            Err(ParseError::BadRange { .. })
        ));
    }

    #[test]
    fn display_round_trip_on_simple_cases() {
        for s in ["a", "ab", "a|b", "a*", "a+", "a?", "(?:ab)*", "[a-z]"] {
            let r = parse_regex(s).unwrap();
            let printed = format!("{}", r);
            let r2 = parse_regex(&printed).unwrap();
            assert_eq!(r, r2, "round-trip failed for {:?} -> {:?}", s, printed);
        }
    }

    // ---- u8 display ----

    fn lit_u8(b: u8) -> Regex<u8> {
        Regex::Lit(b)
    }

    #[test]
    fn display_u8_literals() {
        assert_eq!(format!("{}", lit_u8(b'a')), "a");
        assert_eq!(format!("{}", lit_u8(b'0')), "0");
        // Regex metacharacters escape with `\`.
        assert_eq!(format!("{}", lit_u8(b'.')), "\\.");
        assert_eq!(format!("{}", lit_u8(b'(')), "\\(");
        // Common control chars get short forms.
        assert_eq!(format!("{}", lit_u8(b'\n')), "\\n");
        assert_eq!(format!("{}", lit_u8(b'\t')), "\\t");
        assert_eq!(format!("{}", lit_u8(0)), "\\0");
        // Everything else is `\xHH`, including high bytes.
        assert_eq!(format!("{}", lit_u8(0x1B)), "\\x1B");
        assert_eq!(format!("{}", lit_u8(0xFF)), "\\xFF");
        assert_eq!(format!("{}", lit_u8(0x80)), "\\x80");
    }

    #[test]
    fn display_u8_concat_alt_iter() {
        let r: Regex<u8> = Regex::concat([lit_u8(b'a'), lit_u8(b'b'), lit_u8(b'c')]);
        assert_eq!(format!("{}", r), "abc");

        let r: Regex<u8> = Regex::alt([lit_u8(b'a'), lit_u8(b'b')]);
        assert_eq!(format!("{}", r), "a|b");

        let inner: Regex<u8> = Regex::concat([lit_u8(b'a'), lit_u8(b'b')]);
        assert_eq!(format!("{}", inner.clone().star()), "(?:ab)*");
        assert_eq!(format!("{}", inner.clone().plus()), "(?:ab)+");
        assert_eq!(format!("{}", inner.opt()), "(?:ab)?");

        let r: Regex<u8> = lit_u8(b'a').rep(2, Some(5));
        assert_eq!(format!("{}", r), "a{2,5}");
        let r: Regex<u8> = lit_u8(b'a').rep(3, None);
        assert_eq!(format!("{}", r), "a{3,}");
        let r: Regex<u8> = lit_u8(b'a').rep(4, Some(4));
        assert_eq!(format!("{}", r), "a{4}");
    }

    #[test]
    fn display_u8_class() {
        let c: Regex<u8> = Regex::Class(Class::new(vec![
            ClassRange { lo: b'a', hi: b'z' },
            ClassRange { lo: 0x80, hi: 0xFF },
        ]));
        assert_eq!(format!("{}", c), "[a-z\\x80-\\xFF]");

        let c: Regex<u8> = Regex::Class(Class::negated(vec![ClassRange {
            lo: b'\n',
            hi: b'\n',
        }]));
        assert_eq!(format!("{}", c), "[^\\n]");

        // Inside a class, only `\ ] - ^` are special — `.` `*` `(` etc. are not.
        let c: Regex<u8> = Regex::Class(Class::new(vec![
            ClassRange { lo: b'.', hi: b'.' },
            ClassRange { lo: b']', hi: b']' },
        ]));
        assert_eq!(format!("{}", c), "[.\\]]");
    }

    #[test]
    fn display_u8_empty_and_eps() {
        let r: Regex<u8> = Regex::Empty;
        assert_eq!(format!("{}", r), "(?:[^\\x00-\\xFF])");
        let r: Regex<u8> = Regex::Eps;
        assert_eq!(format!("{}", r), "(?:)");
    }

    // ---- u8 parser ----

    #[test]
    fn parse_u8_simple_literal_and_concat() {
        assert_eq!(parse_regex_u8("a").unwrap(), lit_u8(b'a'));
        assert_eq!(
            parse_regex_u8("abc").unwrap(),
            Regex::Concat(vec![lit_u8(b'a'), lit_u8(b'b'), lit_u8(b'c')]),
        );
    }

    #[test]
    fn parse_u8_alt_and_quantifiers() {
        assert_eq!(
            parse_regex_u8("a|b").unwrap(),
            Regex::Alt(vec![lit_u8(b'a'), lit_u8(b'b')]),
        );
        assert_eq!(parse_regex_u8("a*").unwrap(), lit_u8(b'a').star());
        assert_eq!(parse_regex_u8("a+").unwrap(), lit_u8(b'a').plus());
        assert_eq!(parse_regex_u8("a?").unwrap(), lit_u8(b'a').opt());
        assert_eq!(
            parse_regex_u8("a{3}").unwrap(),
            lit_u8(b'a').rep(3, Some(3))
        );
        assert_eq!(
            parse_regex_u8("a{2,5}").unwrap(),
            lit_u8(b'a').rep(2, Some(5))
        );
        assert_eq!(parse_regex_u8("a{2,}").unwrap(), lit_u8(b'a').rep(2, None));
    }

    #[test]
    fn parse_u8_dot_is_byte_universe() {
        let r = parse_regex_u8(".").unwrap();
        assert_eq!(
            r,
            Regex::Class(Class::new(vec![ClassRange { lo: 0, hi: 0xFF }])),
        );
    }

    #[test]
    fn parse_u8_class_and_ranges() {
        let r = parse_regex_u8("[a-z0-9_]").unwrap();
        assert_eq!(
            r,
            Regex::Class(Class::new(vec![
                ClassRange { lo: b'a', hi: b'z' },
                ClassRange { lo: b'0', hi: b'9' },
                ClassRange { lo: b'_', hi: b'_' },
            ])),
        );

        // Byte-level range over the high half via `\xHH`.
        let r = parse_regex_u8("[\\x80-\\xFF]").unwrap();
        assert_eq!(
            r,
            Regex::Class(Class::new(vec![ClassRange { lo: 0x80, hi: 0xFF }])),
        );

        let r = parse_regex_u8("[^\\n]").unwrap();
        let Regex::Class(c) = r else {
            panic!("expected class")
        };
        assert!(c.negated);
        assert_eq!(
            c.ranges,
            vec![ClassRange {
                lo: b'\n',
                hi: b'\n'
            }]
        );
    }

    #[test]
    fn parse_u8_byte_escapes() {
        assert_eq!(parse_regex_u8("\\x00").unwrap(), lit_u8(0));
        assert_eq!(parse_regex_u8("\\xFF").unwrap(), lit_u8(0xFF));
        assert_eq!(parse_regex_u8("\\n").unwrap(), lit_u8(b'\n'));
        assert_eq!(parse_regex_u8("\\.").unwrap(), lit_u8(b'.'));
    }

    #[test]
    fn parse_u8_rejects_non_ascii_source() {
        let err = parse_regex_u8("é").unwrap_err();
        assert!(matches!(err, ParseError::OutOfAlphabet { c: 'é', .. }));
    }

    #[test]
    fn parse_u8_rejects_unicode_escape() {
        // `\u{...}` is unambiguous for bytes only when ascii, so we reject
        // the whole syntax rather than silently allowing a partial subset.
        let err = parse_regex_u8("\\u{41}").unwrap_err();
        assert!(matches!(err, ParseError::OutOfAlphabet { .. }));
    }

    #[test]
    fn parse_u8_wasm_magic_round_trip() {
        // `\0asm\x01\0\0\0` — the WASM preamble.
        let src = "\\0asm\\x01\\0\\0\\0";
        let r = parse_regex_u8(src).unwrap();
        assert_eq!(
            r,
            Regex::Concat(vec![
                lit_u8(0x00),
                lit_u8(b'a'),
                lit_u8(b's'),
                lit_u8(b'm'),
                lit_u8(0x01),
                lit_u8(0x00),
                lit_u8(0x00),
                lit_u8(0x00),
            ]),
        );
        // And round-trips via Display.
        let printed = format!("{}", r);
        assert_eq!(printed, src);
        let r2 = parse_regex_u8(&printed).unwrap();
        assert_eq!(r, r2);
    }

    #[test]
    fn parse_u8_round_trip_corpus() {
        // Use bytes as the source-of-truth for what we round-trip; the
        // string forms are *what `Display` produces*.
        let cases: &[Regex<u8>] = &[
            Regex::Concat(vec![lit_u8(b'a'), lit_u8(b'b'), lit_u8(b'c')]),
            Regex::Alt(vec![lit_u8(b'a'), lit_u8(b'b')]),
            lit_u8(b'a').star(),
            lit_u8(b'a').plus(),
            lit_u8(b'a').opt(),
            lit_u8(b'a').rep(2, Some(5)),
            Regex::Class(Class::new(vec![
                ClassRange { lo: b'a', hi: b'z' },
                ClassRange { lo: 0x80, hi: 0xFF },
            ])),
            Regex::Class(Class::negated(vec![ClassRange { lo: 0, hi: 0x1F }])),
        ];
        for r in cases {
            let printed = format!("{}", r);
            let parsed = parse_regex_u8(&printed)
                .unwrap_or_else(|e| panic!("re-parse failed for {printed:?}: {e}"));
            assert_eq!(r, &parsed, "round-trip mismatch for {printed:?}");
        }
    }

    #[test]
    fn display_u8_wasm_magic() {
        // Concrete binary-format example: the WASM magic + version prefix
        // `\x00asm\x01\x00\x00\x00` as a u8 regex.
        let r: Regex<u8> = Regex::concat([
            lit_u8(0x00),
            lit_u8(b'a'),
            lit_u8(b's'),
            lit_u8(b'm'),
            lit_u8(0x01),
            lit_u8(0x00),
            lit_u8(0x00),
            lit_u8(0x00),
        ]);
        assert_eq!(format!("{}", r), "\\0asm\\x01\\0\\0\\0");
    }
}
