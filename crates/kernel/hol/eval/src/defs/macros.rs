//! Macros for declaring catalogue spec entries.
//!
//! Every spec in `defs/` follows one of a handful of shapes:
//!
//! - **`let_term!`** — a monomorphic term defined by a direct body
//!   (`let name := body`). The spec's `tm` field holds the body
//!   verbatim; `ty` is computed from `body.type_of()`. The accessor
//!   returns the cached `Term`.
//!
//! - **`spec_term!`** — a monomorphic term defined by a selector
//!   predicate (`def name := ε pred`). The spec's `tm` holds the
//!   predicate, `ty` holds the typed result. The accessor returns
//!   the cached `Term`.
//!
//! - **`poly_spec_term!`** — same as `spec_term!` but the term is
//!   polymorphic in one type variable. The accessor takes the
//!   instance type and substitutes positionally.
//!
//! Each macro caches both the `TermSpec` and (when the accessor is
//! parameter-free) the resulting `Term` in a `LazyLock`. When we
//! later want to share caches more globally (a process-wide arena,
//! say), that knob lives in one place.

/// `let_term!(/// doc...\nspec_fn, accessor, Canonical::Sym, body_expr);`
///
/// Defines a `pub fn spec_fn() -> TermSpec` and a doc-attached
/// `pub fn accessor() -> Term`, both caching with `LazyLock`.
/// The body's type is computed via `body.type_of()` once and frozen.
macro_rules! let_term {
    (
        $(#[$accessor_meta:meta])*
        $spec_fn:ident, $accessor:ident, $sym:expr, $body:expr $(,)?
    ) => {
        pub fn $spec_fn() -> $crate::defs::TermSpec {
            static LAZY: std::sync::LazyLock<$crate::defs::TermSpec> =
                std::sync::LazyLock::new(|| {
                    let body: covalence_core::term::Term = $body;
                    let ty = body.type_of().unwrap_or_else(|e| {
                        panic!(
                            concat!(
                                "let_term! ",
                                stringify!($spec_fn),
                                ": body must type-check: {:?}"
                            ),
                            e
                        )
                    });
                    $crate::defs::TermSpec::new($sym, Some(ty), Some(body))
                });
            LAZY.clone()
        }

        $(#[$accessor_meta])*
        pub fn $accessor() -> covalence_core::term::Term {
            static LAZY: std::sync::LazyLock<covalence_core::term::Term> =
                std::sync::LazyLock::new(|| {
                    covalence_core::term::Term::term_spec($spec_fn(), vec![])
                });
            LAZY.clone()
        }
    };
}

/// `term_decl!(/// doc...\nspec_fn, accessor, Canonical::Sym, ty_expr);`
///
/// Declare a term-spec with only a type (no body, no predicate) — an
/// **opaque atom**. `reduce_spec` can still evaluate it on closed
/// literals, but it has no definition, so it is **sound but
/// incomplete**: nothing about it is provable in open form.
///
/// **This is a placeholder, not a finished op.** Every op should
/// eventually be `let_term!` (a body) or `spec_term!` (a first-order
/// ε-selector spec) instead — see the "sound vs complete" note in the
/// `defs` module docs and the op tracker in `notes/vibes/roadmap.md`. The
/// definition does *not* affect reduction efficiency.
macro_rules! term_decl {
    (
        $(#[$accessor_meta:meta])*
        $spec_fn:ident, $accessor:ident, $sym:expr, $ty:expr $(,)?
    ) => {
        pub fn $spec_fn() -> $crate::defs::TermSpec {
            static LAZY: std::sync::LazyLock<$crate::defs::TermSpec> =
                std::sync::LazyLock::new(|| {
                    $crate::defs::TermSpec::new($sym, Some($ty), None)
                });
            LAZY.clone()
        }

        $(#[$accessor_meta])*
        pub fn $accessor() -> covalence_core::term::Term {
            static LAZY: std::sync::LazyLock<covalence_core::term::Term> =
                std::sync::LazyLock::new(|| {
                    covalence_core::term::Term::term_spec($spec_fn(), vec![])
                });
            LAZY.clone()
        }
    };
}

/// `poly_let_term!(/// doc...\nspec_fn, accessor(alpha[, beta, ...]), Canonical::Sym, body_expr);`
///
/// Polymorphic let-style term in one *or more* type parameters. The
/// body is expressed with `Type::tfree("a")` (and `"b"`, … for further
/// parameters); `ty` is computed from the body once and frozen in the
/// spec. The accessor takes one `Type` per type parameter, in the same
/// order they are substituted positionally into the spec — so by
/// convention list them as `(alpha, beta, …)` matching `tfree("a")`,
/// `tfree("b")`, ….
macro_rules! poly_let_term {
    (
        $(#[$accessor_meta:meta])*
        $spec_fn:ident, $accessor:ident($($targ:ident),+ $(,)?), $sym:expr, $body:expr $(,)?
    ) => {
        pub fn $spec_fn() -> $crate::defs::TermSpec {
            static LAZY: std::sync::LazyLock<$crate::defs::TermSpec> =
                std::sync::LazyLock::new(|| {
                    let body: covalence_core::term::Term = $body;
                    let ty = body.type_of().unwrap_or_else(|e| {
                        panic!(
                            concat!(
                                "poly_let_term! ",
                                stringify!($spec_fn),
                                ": body must type-check: {:?}"
                            ),
                            e
                        )
                    });
                    $crate::defs::TermSpec::new($sym, Some(ty), Some(body))
                });
            LAZY.clone()
        }

        $(#[$accessor_meta])*
        pub fn $accessor($($targ: covalence_core::term::Type),+) -> covalence_core::term::Term {
            covalence_core::term::Term::term_spec($spec_fn(), vec![$($targ),+])
        }
    };
}
