/*!
Utilities for parsing and working with S-expressions

We slightly generalize the SMT-LIBv2 format; for example, we allow Unicode strings
*/

use std::fmt::{self, Debug, Display};
use winnow::{
    ascii::{digit1, multispace0, multispace1},
    combinator::{alt, delimited, preceded, separated},
    prelude::*,
    token::take_while,
};

use smol_str::SmolStr;

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
    pub fn numeral<'a>(input: &mut &'a str) -> ModalResult<&'a str> {
        digit1
            .verify(|s: &str| !s.starts_with('0') || s == "0")
            .parse_next(input)
    }

    pub fn parser(input: &mut &str) -> ModalResult<Constant> {
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

#[derive(Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub enum SExpr {
    Constant(Constant),
    Keyword(SmolStr),
    Symbol(SmolStr),
    List(Vec<SExpr>),
}

impl SExpr {
    pub fn parser(input: &mut &str) -> ModalResult<SExpr> {
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
            .verify(|c: &str| !c.chars().next().unwrap().is_digit(10))
            .map(|s: &str| SExpr::Symbol(s.into())),
            Constant::parser.map(SExpr::Constant),
            //TODO: |symbol|
            delimited(
                ("(", multispace0),
                separated(0.., SExpr::parser, multispace1).map(SExpr::List),
                (multispace0, ")"),
            ),
        ))
        .parse_next(input)
    }

    pub fn as_app(&self) -> Option<(&SmolStr, &[SExpr])> {
        let SExpr::List(v) = self else {
            return None;
        };
        let SExpr::Symbol(f) = v.get(0)? else {
            return None;
        };
        Some((f, &v[1..]))
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
            let parsed = SExpr::parser.parse(sexpr).unwrap();
            assert_eq!(parsed.to_string(), sexpr);
        }
        let denormal_sexprs = [
            "(  a   b   c  )",
            "(  a (  b   c ) d 3 3 3.14159)",
            "( define ( f x ) ( g x ) )",
        ];
        for sexpr in denormal_sexprs {
            let parsed = SExpr::parser.parse(sexpr).unwrap();
            let normalized = parsed.to_string();
            assert_ne!(normalized, sexpr);
            let reparsed = SExpr::parser.parse(&normalized).unwrap();
            assert_eq!(parsed, reparsed);
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
            let parsed = SExpr::parser.parse(sexpr);
            assert!(parsed.is_err(), "{:?} ==> {:?}", sexpr, parsed);
        }
    }
}
