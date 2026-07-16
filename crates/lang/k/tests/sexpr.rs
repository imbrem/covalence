//! Canonical S-expression IR snapshots: `to_sexp` output rendered through
//! `covalence_sexp::prettyprint` must be byte-for-byte stable.

use covalence_k::parse::parse_pattern;
use covalence_k::sexpr::{pattern_to_sexp, to_text};

fn snap(kore: &str) -> String {
    to_text(&pattern_to_sexp(&parse_pattern(kore).unwrap()))
}

#[test]
fn multiary_and_snapshot() {
    assert_eq!(
        snap("\\and{SortK{}}(VarX:SortK{}, \\top{SortK{}}())"),
        "(\\and (sort-app SortK) (evar VarX (sort-app SortK)) (\\top (sort-app SortK)))"
    );
}

#[test]
fn application_snapshot() {
    assert_eq!(
        snap("Lblcount{}(\\dv{SortInt{}}(\"0\"))"),
        "(app Lblcount (sorts) (dv (sort-app SortInt) \"0\"))"
    );
}

#[test]
fn sort_variable_renders_as_plain_symbol() {
    assert_eq!(snap("VarX:R"), "(evar VarX R)");
}

#[test]
fn mu_snapshot() {
    assert_eq!(
        snap("\\mu{}(@X:SortK{}, @X:SortK{})"),
        "(\\mu (svar @X (sort-app SortK)) (svar @X (sort-app SortK)))"
    );
}

#[test]
fn equals_snapshot() {
    assert_eq!(
        snap("\\equals{S, R}(VarB:S, \\dv{S}(\"true\"))"),
        "(\\equals S R (evar VarB S) (dv S \"true\"))"
    );
}
