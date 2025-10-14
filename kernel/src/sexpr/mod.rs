/*!
Utilities for parsing and working with S-expressions
*/

use std::fmt::{self, Debug, Display};
use winnow::{
    ascii::{multispace0, multispace1},
    combinator::{alt, delimited, preceded, separated},
    prelude::*,
    token::take_while,
};

use smol_str::SmolStr;

#[derive(Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub enum SExpr {
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
            "(:key val val)",
        ];
        for sexpr in sexprs {
            let parsed = SExpr::parser.parse(sexpr).unwrap();
            assert_eq!(parsed.to_string(), sexpr);
        }
        let denormal_sexprs = [
            "(  a   b   c  )",
            "(  a (  b   c ) d  )",
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
        let invalid_sexprs = ["", "(", ")", "(a", "a)", "(a (b c) d", "(a b))"];
        for sexpr in invalid_sexprs {
            let parsed = SExpr::parser.parse(sexpr);
            assert!(parsed.is_err(), "{:?} ==> {:?}", sexpr, parsed);
        }
    }
}
