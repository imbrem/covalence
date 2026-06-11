//! Macros for declaring catalogue spec entries.
//!
//! Every spec in `defs/` follows one of a handful of shapes:
//!
//! - **`let_term!`** — a monomorphic term defined by a direct body
//!   (`let name := body`). The spec's `tm` field holds the body
//!   verbatim; `ty` is computed from `body.type_of()`. The accessor
//!   returns the cached `Term`.
//!
//! - **`def_term!`** — a monomorphic term defined by a selector
//!   predicate (`def name := ε pred`). The spec's `tm` holds the
//!   predicate, `ty` holds the typed result. The accessor returns
//!   the cached `Term`.
//!
//! - **`poly_def_term!`** — same as `def_term!` but the term is
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
                    let body: $crate::term::Term = $body;
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
        pub fn $accessor() -> $crate::term::Term {
            static LAZY: std::sync::LazyLock<$crate::term::Term> =
                std::sync::LazyLock::new(|| {
                    $crate::term::Term::term_spec($spec_fn(), vec![])
                });
            LAZY.clone()
        }
    };
}

/// `term_decl!(/// doc...\nspec_fn, accessor, Canonical::Sym, ty_expr);`
///
/// Declare a term-spec with only a type (no body, no predicate).
/// Use for ops whose body / characterisation is still TODO; the
/// kernel can dispatch reductions on the spec handle without it.
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
        pub fn $accessor() -> $crate::term::Term {
            static LAZY: std::sync::LazyLock<$crate::term::Term> =
                std::sync::LazyLock::new(|| {
                    $crate::term::Term::term_spec($spec_fn(), vec![])
                });
            LAZY.clone()
        }
    };
}

/// `def_term!(/// doc...\nspec_fn, accessor, Canonical::Sym, ty_expr, pred_expr);`
///
/// Defines a `pub fn spec_fn() -> TermSpec` whose `tm` holds the
/// Hilbert-ε selector predicate, and a doc-attached
/// `pub fn accessor() -> Term`.
macro_rules! def_term {
    (
        $(#[$accessor_meta:meta])*
        $spec_fn:ident, $accessor:ident, $sym:expr, $ty:expr, $pred:expr $(,)?
    ) => {
        pub fn $spec_fn() -> $crate::defs::TermSpec {
            static LAZY: std::sync::LazyLock<$crate::defs::TermSpec> =
                std::sync::LazyLock::new(|| {
                    $crate::defs::TermSpec::new($sym, Some($ty), Some($pred))
                });
            LAZY.clone()
        }

        $(#[$accessor_meta])*
        pub fn $accessor() -> $crate::term::Term {
            static LAZY: std::sync::LazyLock<$crate::term::Term> =
                std::sync::LazyLock::new(|| {
                    $crate::term::Term::term_spec($spec_fn(), vec![])
                });
            LAZY.clone()
        }
    };
}

/// `poly_let_term!(/// doc...\nspec_fn, accessor(alpha), Canonical::Sym, body_expr);`
///
/// One-type-parameter polymorphic let-style term. The body is
/// expressed with `Type::tfree("a")` for the bound `α`; `ty` is
/// computed from the body once and frozen in the spec.
macro_rules! poly_let_term {
    (
        $(#[$accessor_meta:meta])*
        $spec_fn:ident, $accessor:ident($alpha:ident), $sym:expr, $body:expr $(,)?
    ) => {
        pub fn $spec_fn() -> $crate::defs::TermSpec {
            static LAZY: std::sync::LazyLock<$crate::defs::TermSpec> =
                std::sync::LazyLock::new(|| {
                    let body: $crate::term::Term = $body;
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
        pub fn $accessor($alpha: $crate::term::Type) -> $crate::term::Term {
            $crate::term::Term::term_spec($spec_fn(), vec![$alpha])
        }
    };
}

/// `poly_def_term!(/// doc...\nspec_fn, accessor(alpha), Canonical::Sym, ty_expr, pred_expr);`
///
/// One-type-parameter polymorphic def-style term. The spec is
/// cached; the accessor builds a fresh `Term::term_spec` per call
/// with the supplied type argument.
macro_rules! poly_def_term {
    (
        $(#[$accessor_meta:meta])*
        $spec_fn:ident, $accessor:ident($alpha:ident), $sym:expr, $ty:expr, $pred:expr $(,)?
    ) => {
        pub fn $spec_fn() -> $crate::defs::TermSpec {
            static LAZY: std::sync::LazyLock<$crate::defs::TermSpec> =
                std::sync::LazyLock::new(|| {
                    $crate::defs::TermSpec::new($sym, Some($ty), Some($pred))
                });
            LAZY.clone()
        }

        $(#[$accessor_meta])*
        pub fn $accessor($alpha: $crate::term::Type) -> $crate::term::Term {
            $crate::term::Term::term_spec($spec_fn(), vec![$alpha])
        }
    };
}

