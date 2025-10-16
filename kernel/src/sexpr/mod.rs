/*!
Utilities for parsing and working with S-expressions

We slightly generalize the SMT-LIBv2 format; for example, we allow Unicode strings
*/

use std::{
    fmt::{self, Debug, Display},
    ops::Range,
};
use winnow::{
    ascii::{digit1, multispace1},
    combinator::{alt, delimited, opt, preceded, repeat, separated},
    token::{take_till, take_while},
};

use smol_str::SmolStr;

pub use winnow::{self, LocatingSlice, ModalResult, Parser};

/// A list of S-expressions, with line-comments ignored
pub struct Commands(pub Vec<Spanned<SExpr>>);

impl Commands {
    pub fn parser(input: &mut LocatingSlice<&str>) -> ModalResult<Commands> {
        delimited(
            opt(SExpr::ws),
            separated(
                0..,
                SExpr::parser.with_span().map(|(s, r)| Spanned::new(s, r)),
                SExpr::ws,
            ),
            opt(SExpr::ws),
        )
        .map(Commands)
        .parse_next(input)
    }
}

/// An S-expression
#[derive(Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub enum SExpr {
    Constant(Constant),
    Keyword(SmolStr),
    Symbol(SmolStr),
    List(Vec<Spanned<SExpr>>),
}

impl SExpr {
    pub fn parser(input: &mut LocatingSlice<&str>) -> ModalResult<SExpr> {
        alt((
            preceded(
                ":",
                take_while(1.., |c: char| {
                    c.is_alphanumeric() || "+-/*=%?!.$_~&^<>@".contains(c)
                })
                .map(|s: &str| SExpr::Keyword(s.into())),
            ),
            take_while(1.., |c: char| {
                c.is_alphanumeric() || "+-/*=%?!.%_~&<>@".contains(c)
            })
            .verify(|c: &str| !c.chars().next().unwrap().is_ascii_digit())
            .map(|s: &str| SExpr::Symbol(s.into())),
            // //TODO: |symbol|
            Constant::parser.map(SExpr::Constant),
            delimited(
                ("(", opt(Self::ws)),
                separated(
                    0..,
                    SExpr::parser.with_span().map(|(s, r)| Spanned::new(s, r)),
                    Self::ws,
                )
                .map(SExpr::List),
                (opt(Self::ws), ")"),
            ),
        ))
        .parse_next(input)
    }

    pub fn line_comment(input: &mut LocatingSlice<&str>) -> ModalResult<()> {
        (';', take_till(1.., ['\n', '\r']))
            .void() // Output is thrown away.
            .parse_next(input)
    }

    pub fn ws(input: &mut LocatingSlice<&str>) -> ModalResult<()> {
        repeat(1.., alt((multispace1.void(), Self::line_comment.void()))).parse_next(input)
    }

    pub fn as_app(&self) -> Option<(Spanned<&SmolStr>, &[Spanned<SExpr>])> {
        let SExpr::List(v) = self else {
            return None;
        };
        let symbol = v.first()?;
        let SExpr::Symbol(f) = &symbol.node else {
            return None;
        };
        Some((Spanned::new(f, symbol.start..symbol.end), &v[1..]))
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub enum Constant {
    Numeral(SmolStr),
    Decimal(SmolStr),
    Hex(SmolStr),
    Bin(SmolStr),
    String(SmolStr),
}

impl Display for Constant {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Constant::Numeral(s) => write!(f, "{s}"),
            Constant::Decimal(s) => write!(f, "{s}"),
            Constant::Hex(s) => write!(f, "#x{s}"),
            Constant::Bin(s) => write!(f, "#b{s}"),
            Constant::String(s) => write!(f, "{s:?}"),
        }
    }
}

impl Debug for Constant {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl Constant {
    pub fn numeral<'a>(input: &mut LocatingSlice<&'a str>) -> ModalResult<&'a str> {
        digit1
            .verify(|s: &str| !s.starts_with('0') || s == "0")
            .parse_next(input)
    }

    pub fn parser(input: &mut LocatingSlice<&str>) -> ModalResult<Constant> {
        alt((
            preceded(
                "#x",
                take_while(1.., |c: char| c.is_ascii_hexdigit())
                    .map(|s: &str| Constant::Hex(s.into())),
            ),
            preceded(
                "#b",
                take_while(1.., |c: char| c == '0' || c == '1')
                    .map(|s: &str| Constant::Bin(s.into())),
            ),
            (Self::numeral, ".", digit1)
                .take()
                .map(|s: &str| Constant::Decimal(s.into())),
            Self::numeral.map(|s: &str| Constant::Numeral(s.into())),
            //TODO: escaped strings
            delimited(
                "\"",
                take_while(0.., |c: char| c != '"').map(|s: &str| Constant::String(s.into())),
                "\"",
            ),
        ))
        .parse_next(input)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct Spanned<T> {
    pub node: T,
    pub start: usize,
    pub end: usize,
}

impl<T> Display for Spanned<T>
where
    T: Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Display::fmt(&self.node, f)
    }
}

impl<T> Spanned<T> {
    pub fn new(node: T, range: Range<usize>) -> Self {
        Self {
            node,
            start: range.start,
            end: range.end,
        }
    }

    pub fn as_deref(&self) -> Spanned<&T::Target>
    where
        T: std::ops::Deref,
    {
        Spanned {
            node: &*self.node,
            start: self.start,
            end: self.end,
        }
    }

    pub fn as_ref(&self) -> Spanned<&T> {
        Spanned {
            node: &self.node,
            start: self.start,
            end: self.end,
        }
    }

    pub fn as_mut(&mut self) -> Spanned<&mut T> {
        Spanned {
            node: &mut self.node,
            start: self.start,
            end: self.end,
        }
    }

    pub fn filter_map<U>(self, f: impl FnOnce(T) -> Option<U>) -> Option<Spanned<U>> {
        f(self.node).map(|node| Spanned {
            node,
            start: self.start,
            end: self.end,
        })
    }
}

impl Debug for SExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl Display for SExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SExpr::Keyword(s) => write!(f, ":{s}"),
            SExpr::Constant(c) => write!(f, "{c}"),
            SExpr::Symbol(s) => write!(f, "{s}"),
            SExpr::List(v) => {
                write!(f, "(")?;
                for (i, e) in v.iter().enumerate() {
                    if i > 0 {
                        write!(f, " ")?;
                    }
                    write!(f, "{e}")?;
                }
                write!(f, ")")
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn sexpr_roundtrip() {
        let sexprs = [
            "()",
            "(a)",
            "(a b c)",
            "(a (b c) d)",
            "(define (f x) (g x))",
            ":keyword",
            "(:key val val 3 2 3.14159)",
            "1.1",
            "\"hello world\"",
            "(3.1512 \"你好 world\")",
        ];
        for sexpr in sexprs {
            let parsed = SExpr::parser.parse(LocatingSlice::new(sexpr)).unwrap();
            assert_eq!(parsed.to_string(), sexpr);
        }
        let denormal_sexprs = [
            "(  a   b   c  )",
            "(  a (  b   c ) d 3 3 3.14159)",
            "( define ( f x ) ( g x ) )",
            "(f x ; comment
                )",
        ];
        for sexpr in denormal_sexprs {
            let parsed = SExpr::parser.parse(LocatingSlice::new(sexpr)).unwrap();
            let normalized = parsed.to_string();
            assert_ne!(normalized, sexpr);
            let reparsed = SExpr::parser
                .parse(LocatingSlice::new(&normalized))
                .unwrap();
            assert_eq!(normalized, reparsed.to_string());
        }
    }

    #[test]
    fn invalid_sexpr() {
        let invalid_sexprs = [
            "",
            "(",
            ")",
            "(a",
            "a)",
            "(a (b c) d",
            "(a b))",
            "00",
            "#b32",
        ];
        for sexpr in invalid_sexprs {
            let parsed = SExpr::parser.parse(LocatingSlice::new(sexpr));
            assert!(parsed.is_err(), "{:?} ==> {:?}", sexpr, parsed);
        }
    }
}
