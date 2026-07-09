//! **Flagship demo — "`init/` in the dialect", the on-ramp.**
//!
//! A small init-flavored module written in the Haskell dialect (composition
//! combinators plus a Church-encoded option helper), lowered through the full
//! pipeline:
//!
//! 1. Haskell dialect ⇒ SExpr IR ⇒ **exact asserted canonical text** — the
//!    interchange artifact a third-party consumer would receive;
//! 2. (under `--features hol`) SExpr IR ⇒ **carved `sexpr` kernel `Term`s**
//!    via the HOL backend — genuine kernel data.
//!
//! The `(define …)` output is still *inert* IR/kernel data: lowering to
//! actual `covalence-init` definitions (typed `Term`s, `Def`/`Thm`) is the
//! recorded follow-on (see `SKELETONS.md`).

use covalence_haskell::lower::{module_to_sexprs, module_to_text};
use covalence_haskell::parse::parse_module;
use covalence_haskell::sexpr::parse_sexprs;

/// The demo module: composition combinators + a Church-encoded option.
/// (`none`/`some` are eliminator-style encodings — `m d f` inspects `m` —
/// so `mapOption` needs no pattern matching, which the dialect lacks.)
const MODULE: &str = "\
compose f g x = f (g x)
const x y = x
none d f = d
some x d f = f x
mapOption g m = m none (compose some g)
";

/// The exact canonical interchange text the module lowers to.
const EXPECTED: &str = "\
(define compose (lambda f (lambda g (lambda x (f (g x))))))
(define const (lambda x (lambda y x)))
(define none (lambda d (lambda f d)))
(define some (lambda x (lambda d (lambda f (f x)))))
(define mapOption (lambda g (lambda m ((m none) ((compose some) g)))))
";

#[test]
fn init_dialect_module_lowers_to_exact_text() {
    let m = parse_module(MODULE).expect("module parses");
    assert_eq!(module_to_text(&m), EXPECTED);
}

#[test]
fn init_dialect_text_round_trips() {
    let m = parse_module(MODULE).expect("module parses");
    assert_eq!(parse_sexprs(EXPECTED).unwrap(), module_to_sexprs(&m));
}

/// The same module, through the HOL backend: every declaration lands as a
/// carved `sexpr` kernel `Term`, with `compose` checked against the
/// hand-built value.
#[cfg(feature = "hol")]
mod hol {
    use super::MODULE;
    use covalence_haskell::hol::HolBackend;
    use covalence_haskell::lower::lower_decl;
    use covalence_haskell::parse::parse_module;
    use covalence_hol_eval::mk_blob;
    use covalence_init::Term;
    use covalence_init::init::inductive::carved::carved;

    fn atom(bytes: &[u8]) -> Term {
        let c = carved().expect("carved sexpr theory builds");
        Term::app(c.atom.clone(), mk_blob(bytes.to_vec()))
    }

    fn list(items: Vec<Term>) -> Term {
        let c = carved().expect("carved sexpr theory builds");
        let mut acc = c.snil.clone();
        for it in items.into_iter().rev() {
            acc = Term::app(Term::app(c.scons.clone(), it), acc);
        }
        acc
    }

    fn lam(p: &[u8], body: Term) -> Term {
        list(vec![atom(b"lambda"), atom(p), body])
    }

    #[test]
    fn init_dialect_module_lands_as_kernel_terms() {
        let m = parse_module(MODULE).expect("module parses");
        let lowered: Vec<(String, Term)> = m
            .iter()
            .map(|d| lower_decl(d, &mut HolBackend).expect("realizes"))
            .collect();
        assert_eq!(lowered.len(), 5);

        // compose = (lambda f (lambda g (lambda x (f (g x)))))
        let body = list(vec![atom(b"f"), list(vec![atom(b"g"), atom(b"x")])]);
        let want = lam(b"f", lam(b"g", lam(b"x", body)));
        assert_eq!(lowered[0], ("compose".to_string(), want));

        // none = (lambda d (lambda f d))
        let want = lam(b"d", lam(b"f", atom(b"d")));
        assert_eq!(lowered[2], ("none".to_string(), want));
    }
}
