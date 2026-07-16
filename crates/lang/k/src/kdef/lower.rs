//! Bridge the `.k`-source rule AST ([`crate::kdef::ast::KRule`] /
//! [`crate::kdef::ast::RuleTerm`]) to the KORE-facing [`crate::ast::Pattern`] /
//! [`crate::fragment::RewriteRule`] types — so `.k`-parsed rules flow into the
//! same lowering (`covalence-init::k::rewrite`) the KORE path uses. One reducer,
//! two frontends.
//!
//! The mapping is direct: a prefix constructor application `sym(args…)` becomes a
//! [`Pattern::App`] (no sort parameters); a variable `X[:Sort]` becomes a
//! [`Pattern::EVar`] (the annotated sort, or a placeholder `K` sort — sorts don't
//! affect the free-algebra encoding, only symbol identity does).

use crate::ast::{Pattern, Sort as KoreSort};
use crate::fragment::RewriteRule;
use crate::kdef::ast::{KRule, RuleTerm};

/// The placeholder sort for a variable with no annotation (the free-algebra
/// encoding ignores sorts — only the variable *name* matters).
fn placeholder_sort() -> KoreSort {
    KoreSort::App("K".into(), vec![])
}

/// Convert a `.k` grammar [`crate::kdef::ast::Sort`] to a KORE [`KoreSort`].
fn lower_sort(s: &crate::kdef::ast::Sort) -> KoreSort {
    KoreSort::App(s.name.clone(), s.params.iter().map(lower_sort).collect())
}

impl RuleTerm {
    /// Lower this prefix term to a KORE [`Pattern`].
    pub fn to_pattern(&self) -> Pattern {
        match self {
            RuleTerm::App { sym, args } => Pattern::App {
                symbol: sym.clone(),
                sorts: Vec::new(),
                args: args.iter().map(RuleTerm::to_pattern).collect(),
            },
            RuleTerm::Var { name, sort } => Pattern::EVar(
                name.clone(),
                sort.as_ref().map_or_else(placeholder_sort, lower_sort),
            ),
        }
    }
}

impl KRule {
    /// Lower this `.k` rule to a KORE [`RewriteRule`] (the reducer's input type).
    /// `requires` is carried as a raw pattern (so the reducer skips it as an F1
    /// conditional rule, exactly as for KORE).
    pub fn to_rewrite_rule(&self) -> RewriteRule {
        RewriteRule {
            sort: placeholder_sort(),
            lhs: self.lhs.to_pattern(),
            rhs: self.rhs.to_pattern(),
            requires: self.requires.as_ref().map(RuleTerm::to_pattern),
            ensures: None,
            priority: 50,
            label: None,
            unique_id: None,
        }
    }
}

/// Lower all of a module's `.k` rules to [`RewriteRule`]s.
pub fn module_rules(m: &crate::kdef::ast::KModule) -> Vec<RewriteRule> {
    m.rules.iter().map(KRule::to_rewrite_rule).collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kdef::parse::parse_definition;

    #[test]
    fn parses_and_lowers_peano_rules() {
        // PEANO in the prefix fragment (nullary ctor written `z()`).
        let src = r#"
module PEANO
  syntax Nat ::= "z" | "s" | "plus"
  rule plus(z(), N) => N
  rule plus(s(M), N) => s(plus(M, N))
endmodule
"#;
        let def = parse_definition(src).unwrap();
        let m = &def.modules[0];
        assert_eq!(m.rules.len(), 2, "both rules parsed");

        let rules = module_rules(m);
        assert_eq!(rules.len(), 2);
        // rule 0: plus(z(), N) => N
        let r0 = &rules[0];
        assert!(matches!(&r0.lhs, Pattern::App { symbol, .. } if symbol == "plus"));
        assert!(matches!(&r0.rhs, Pattern::EVar(n, _) if n == "N"));
        assert!(r0.requires.is_none());
        // rule 1's RHS is s(plus(M, N)).
        assert!(matches!(&rules[1].rhs, Pattern::App { symbol, .. } if symbol == "s"));
    }

    #[test]
    fn colorof_lesson_1_2_rules() {
        // Constructors written with parens (Lesson 1.2 style); variable F is bare.
        let src = r#"
module COLORS
  syntax Color ::= "Yellow"
  rule colorOf(Banana()) => Yellow()
  rule contentsOfJar(Jar(F)) => F
endmodule
"#;
        let def = parse_definition(src).unwrap();
        let rules = module_rules(&def.modules[0]);
        assert_eq!(rules.len(), 2);
        // colorOf(Banana()) => Yellow(): nullary ctors are Apps with no args.
        let Pattern::App { symbol, args, .. } = &rules[0].lhs else {
            panic!("expected app");
        };
        assert_eq!(symbol, "colorOf");
        assert!(
            matches!(&args[0], Pattern::App { symbol, args, .. } if symbol == "Banana" && args.is_empty())
        );
        // contentsOfJar(Jar(F)) => F: F is a variable.
        assert!(matches!(&rules[1].rhs, Pattern::EVar(n, _) if n == "F"));
    }

    #[test]
    fn requires_rule_carried() {
        let src = "module M rule f(X) => g(X) requires isOk(X) endmodule";
        let def = parse_definition(src).unwrap();
        let rules = module_rules(&def.modules[0]);
        assert_eq!(rules.len(), 1);
        assert!(rules[0].requires.is_some());
    }
}
