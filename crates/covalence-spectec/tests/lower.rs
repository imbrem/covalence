//! End-to-end test for the SpecTec -> HOL lowering driver (smallest slice).
//!
//! Parses a self-contained `syntax` alias snippet, lowers the one node,
//! and asserts the resulting `covalence-core` kernel `Type` / `TypeSpec`
//! is well-formed: its carrier is the expected kernel base type, and it
//! is usable as the type of a kernel `Term` (so `Term::type_of` succeeds
//! and returns exactly the lowered type).

use covalence_core::ty::{Type, TypeKind};
use covalence_core::{Term, ty::TypeSpec};
use covalence_spectec::cst::Top;
use covalence_spectec::lex::lex;
use covalence_spectec::lower::{Lowered, lower_top};
use covalence_spectec::parse::parse;
use covalence_spectec::source::SourceMap;

/// Parse a snippet into top-level forms.
fn parse_snippet(src: &str) -> Vec<Top> {
    let mut map = SourceMap::new();
    let id = map.add("test.spectec", src);
    let tokens = lex(id, src).expect("lex");
    parse(id, tokens).expect("parse")
}

#[test]
fn lower_syntax_alias_to_typespec() {
    // A self-contained SpecTec snippet: alias `byte` to the kernel `nat`.
    let tops = parse_snippet("syntax byte = nat\n");
    assert_eq!(tops.len(), 1, "exactly one top-level form");
    assert!(matches!(tops[0], Top::Syntax(_)), "it is a `syntax` form");

    let lowered = lower_top(&tops[0])
        .expect("lowering succeeds")
        .expect("the syntax form is in scope for this slice");

    let Lowered::TypeAlias { name, spec, ty } = lowered;

    // The lowered spec carries the source name and the `nat` carrier.
    assert_eq!(name, "byte");
    assert_eq!(spec.symbol().label(), "byte");
    assert_eq!(spec.ty(), Some(&Type::nat()), "carrier is kernel nat");

    // The lowered `Type` is a well-formed `TypeKind::Spec` leaf over that
    // exact spec, with no type arguments (a nullary alias).
    match ty.kind() {
        TypeKind::Spec(got_spec, args) => {
            assert!(got_spec.ptr_eq(&spec), "leaf references the lowered spec");
            assert!(args.is_empty(), "nullary alias has no type args");
        }
        other => panic!("expected TypeKind::Spec, got {other:?}"),
    }

    // The lowered type is usable by the kernel: a free variable of that
    // type type-checks, and `type_of` returns exactly the lowered type.
    let x = Term::free("x", ty.clone());
    let inferred = x.type_of().expect("free var of lowered type type-checks");
    assert_eq!(inferred, ty, "type_of round-trips the lowered type");
}

#[test]
fn lower_syntax_alias_to_bool() {
    let tops = parse_snippet("syntax flag = bool\n");
    let lowered = lower_top(&tops[0]).expect("ok").expect("in scope");
    let Lowered::TypeAlias { spec, ty, .. } = lowered;
    assert_eq!(spec.ty(), Some(&Type::bool()));
    // Build `flag -> bool` and confirm a function leaf is well-typed.
    let f = Term::free("p", Type::fun(ty.clone(), Type::bool()));
    assert!(f.type_of().is_ok());
    let _: TypeSpec = spec; // spec handle is the public kernel type
}

#[test]
fn lower_rejects_unsupported_base() {
    // `addrtype` is not one of the kernel base types this slice maps.
    let tops = parse_snippet("syntax foo = addrtype\n");
    let err = lower_top(&tops[0]).expect_err("unsupported base type is rejected");
    assert!(err.message.contains("unsupported base type"), "{}", err.message);
}

#[test]
fn lower_skips_out_of_scope_forms() {
    // A `var` form is out of scope: lowering returns Ok(None), not an error.
    let tops = parse_snippet("var n : nat\n");
    let result = lower_top(&tops[0]).expect("no error for out-of-scope form");
    assert!(result.is_none(), "out-of-scope form lowers to None");
}
