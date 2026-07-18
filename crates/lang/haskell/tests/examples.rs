//! **The example-library on-ramp: writing `init/`-style modules in the
//! dialect.**
//!
//! A small library of dialect sample sources (`examples/*.hs`) — core
//! combinators, an eliminator-encoded `Option` + list helpers, and a
//! monad-ish (reader) example — is compiled through the full pipeline:
//!
//! 1. Haskell dialect ⇒ SExpr IR ⇒ **exact-asserted canonical interchange
//!    text** (what a third-party consumer would receive);
//! 2. (under `--features hol`) ⇒ **carved `sexpr` kernel `Term`s** — genuine
//!    kernel data, one per top-level definition.
//!
//! The output is still *inert* IR/kernel data; realizing it into typed
//! `covalence-init` `Def`/`Thm` is the recorded follow-on (the generated open-work index).

use covalence_haskell::lower::{module_to_sexprs, module_to_text};
use covalence_haskell::parse::parse_module;
use covalence_haskell::sexpr::parse_sexprs;

const COMBINATORS: &str = include_str!("../examples/combinators.hs");
const OPTION: &str = include_str!("../examples/option.hs");
const MONAD: &str = include_str!("../examples/monad.hs");

/// The exact canonical interchange text `combinators.hs` lowers to (the type
/// signatures are dropped).
const COMBINATORS_TEXT: &str = "\
(define id (lambda x x))
(define const (lambda x (lambda y x)))
(define compose (lambda f (lambda g (lambda x (f (g x))))))
(define flip (lambda f (lambda x (lambda y ((f y) x)))))
(define apply (lambda f (lambda x (f x))))
";

const OPTION_TEXT: &str = "\
(define none (lambda d (lambda f d)))
(define some (lambda x (lambda d (lambda f (f x)))))
(define mapOption (lambda g (lambda m ((m none) ((compose some) g)))))
(define getOrElse (lambda d (lambda m ((m d) (lambda x x)))))
(define isSome (lambda m ((m false) (lambda x true))))
(define nil (lambda n (lambda c n)))
(define cons (lambda h (lambda t (lambda n (lambda c ((c h) t))))))
(define singleton (lambda x ((cons x) nil)))
";

const MONAD_TEXT: &str = "\
(define ret (lambda x (lambda e x)))
(define bind (lambda m (lambda k (lambda e ((k (m e)) e)))))
(define ask (lambda e e))
(define classify (lambda p ((bind ask) (lambda e (ret (if (p e) (tuple tagHi e) (tuple tagLo e)))))))
(define pair2 ((bind ask) (lambda x ((bind ask) (lambda y (ret (list x y)))))))
";

fn check(src: &str, expected: &str, defs: usize) {
    let m = parse_module(src).unwrap_or_else(|e| panic!("parse: {e}"));
    assert_eq!(m.len(), defs, "definition count");
    // Exact canonical interchange text.
    assert_eq!(module_to_text(&m), expected);
    // The text a third party would receive re-parses to the same forms.
    assert_eq!(parse_sexprs(expected).unwrap(), module_to_sexprs(&m));
}

#[test]
fn combinators_lower_to_exact_text() {
    check(COMBINATORS, COMBINATORS_TEXT, 5);
}

#[test]
fn option_lowers_to_exact_text() {
    check(OPTION, OPTION_TEXT, 8);
}

#[test]
fn monad_lowers_to_exact_text() {
    check(MONAD, MONAD_TEXT, 5);
}

/// Every example module, lowered through the HOL backend, lands each top-level
/// definition as a carved `sexpr` kernel `Term` — genuine kernel data.
#[cfg(feature = "hol")]
mod hol {
    use super::{COMBINATORS, MONAD, OPTION};
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

    fn lower_all(src: &str) -> Vec<(String, Term)> {
        parse_module(src)
            .expect("parses")
            .iter()
            .map(|d| lower_decl(d, &mut HolBackend).expect("realizes"))
            .collect()
    }

    #[test]
    fn all_examples_land_as_kernel_terms() {
        assert_eq!(lower_all(COMBINATORS).len(), 5);
        assert_eq!(lower_all(OPTION).len(), 8);
        assert_eq!(lower_all(MONAD).len(), 5);
    }

    /// Spot-check a couple of definitions against hand-built carved terms.
    #[test]
    fn selected_definitions_match_hand_built_terms() {
        let comb = lower_all(COMBINATORS);
        // id = (lambda x x)
        assert_eq!(comb[0], ("id".to_string(), lam(b"x", atom(b"x"))));
        // const = (lambda x (lambda y x))
        assert_eq!(
            comb[1],
            ("const".to_string(), lam(b"x", lam(b"y", atom(b"x"))))
        );

        let opt = lower_all(OPTION);
        // none = (lambda d (lambda f d))
        assert_eq!(
            opt[0],
            ("none".to_string(), lam(b"d", lam(b"f", atom(b"d"))))
        );

        // The monad example's `if`/tuple/list heads land as ordinary atoms.
        let mon = lower_all(MONAD);
        // ask = (lambda e e)
        assert_eq!(mon[2], ("ask".to_string(), lam(b"e", atom(b"e"))));
    }
}
