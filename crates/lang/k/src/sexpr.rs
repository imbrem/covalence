//! THE canonical S-expression rendering of the KORE AST — the "simple
//! S-expression IR" the K-frontend design promises (`notes/design/k-frontend.md`).
//!
//! The rendering is **deterministic**: one AST value has exactly one SExpr
//! (and, through [`covalence_sexp::prettyprint`], one text form via
//! [`to_text`]). Consumers downstream of this crate read this IR, never KORE
//! syntax. `to_sexp` direction only — `from_sexp` / round-trip is a recorded
//! skeleton (the generated open-work index).
//!
//! # Canonical shapes
//!
//! ```text
//! definition:  (kore (attrs A…) MODULE…)
//! module:      (module NAME SENTENCE… (attrs A…))
//! sentences:   (import NAME (attrs …))
//!              (sort NAME (sort-vars V…) (attrs …))          ; hooked-sort likewise
//!              (symbol NAME (sort-vars V…) (args S…) RET (attrs …))
//!              (alias NAME (sort-vars V…) (args S…) RET LHS RHS (attrs …))
//!              (axiom (sort-vars V…) PATTERN (attrs …))      ; claim likewise
//! sorts:       NAME                       ; sort variable — plain symbol
//!              (sort-app NAME S…)         ; constructor app (nullary: (sort-app NAME))
//! patterns:    (evar NAME SORT)  (svar NAME SORT)   ; svar NAME keeps its `@`
//!              "lit"                                ; string literal atom
//!              (app SYMBOL (sorts S…) ARG…)
//!              (\top SORT)  (\bottom SORT)  (\not SORT P)  (\next SORT P)
//!              (\and SORT P…)  (\or SORT P…)         ; multiary
//!              (\implies SORT P Q)  (\iff SORT P Q)  (\rewrites SORT P Q)
//!              (\exists SORT (evar X XS) P)  (\forall SORT (evar X XS) P)
//!              (\mu (svar X XS) P)  (\nu (svar X XS) P)
//!              (\ceil ARGSORT SORT P)  (\floor ARGSORT SORT P)
//!              (\equals ARGSORT SORT P Q)  (\in ARGSORT SORT P Q)
//!              (dv SORT "lit")
//! ```

use covalence_sexp::{SExp, SExpr, prettyprint};

use crate::ast::{Definition, Module, Pattern, Sentence, Sort};

/// Render a whole definition: `(kore (attrs …) MODULE…)`.
pub fn definition_to_sexp(def: &Definition) -> SExpr {
    let mut items = vec![SExp::symbol("kore"), attrs_to_sexp(&def.attrs)];
    items.extend(def.modules.iter().map(module_to_sexp));
    SExp::List(items)
}

/// Render a module: `(module NAME SENTENCE… (attrs …))`.
pub fn module_to_sexp(m: &Module) -> SExpr {
    let mut items = vec![SExp::symbol("module"), SExp::symbol(m.name.clone())];
    items.extend(m.sentences.iter().map(sentence_to_sexp));
    items.push(attrs_to_sexp(&m.attrs));
    SExp::List(items)
}

/// Render a sentence (shapes in the module docs).
pub fn sentence_to_sexp(s: &Sentence) -> SExpr {
    match s {
        Sentence::Import { name, attrs } => SExp::List(vec![
            SExp::symbol("import"),
            SExp::symbol(name.clone()),
            attrs_to_sexp(attrs),
        ]),
        Sentence::Sort {
            hooked,
            name,
            vars,
            attrs,
        } => SExp::List(vec![
            SExp::symbol(if *hooked { "hooked-sort" } else { "sort" }),
            SExp::symbol(name.clone()),
            sort_vars_to_sexp(vars),
            attrs_to_sexp(attrs),
        ]),
        Sentence::Symbol {
            hooked,
            name,
            sort_vars,
            arg_sorts,
            ret,
            attrs,
        } => SExp::List(vec![
            SExp::symbol(if *hooked { "hooked-symbol" } else { "symbol" }),
            SExp::symbol(name.clone()),
            sort_vars_to_sexp(sort_vars),
            tagged_sorts("args", arg_sorts),
            sort_to_sexp(ret),
            attrs_to_sexp(attrs),
        ]),
        Sentence::Alias {
            name,
            sort_vars,
            arg_sorts,
            ret,
            lhs,
            rhs,
            attrs,
        } => SExp::List(vec![
            SExp::symbol("alias"),
            SExp::symbol(name.clone()),
            sort_vars_to_sexp(sort_vars),
            tagged_sorts("args", arg_sorts),
            sort_to_sexp(ret),
            pattern_to_sexp(lhs),
            pattern_to_sexp(rhs),
            attrs_to_sexp(attrs),
        ]),
        Sentence::Axiom {
            sort_vars,
            pattern,
            attrs,
        } => SExp::List(vec![
            SExp::symbol("axiom"),
            sort_vars_to_sexp(sort_vars),
            pattern_to_sexp(pattern),
            attrs_to_sexp(attrs),
        ]),
        Sentence::Claim {
            sort_vars,
            pattern,
            attrs,
        } => SExp::List(vec![
            SExp::symbol("claim"),
            sort_vars_to_sexp(sort_vars),
            pattern_to_sexp(pattern),
            attrs_to_sexp(attrs),
        ]),
    }
}

/// Render a sort: a plain symbol for a sort variable, `(sort-app NAME S…)`
/// for a constructor application (nullary included).
pub fn sort_to_sexp(s: &Sort) -> SExpr {
    match s {
        Sort::Var(name) => SExp::symbol(name.clone()),
        Sort::App(name, params) => {
            let mut items = vec![SExp::symbol("sort-app"), SExp::symbol(name.clone())];
            items.extend(params.iter().map(sort_to_sexp));
            SExp::List(items)
        }
    }
}

/// Render a pattern (shapes in the module docs).
pub fn pattern_to_sexp(p: &Pattern) -> SExpr {
    match p {
        Pattern::EVar(name, sort) => SExp::List(vec![
            SExp::symbol("evar"),
            SExp::symbol(name.clone()),
            sort_to_sexp(sort),
        ]),
        Pattern::SVar(name, sort) => SExp::List(vec![
            SExp::symbol("svar"),
            SExp::symbol(name.clone()),
            sort_to_sexp(sort),
        ]),
        Pattern::String(s) => SExp::string("", s.as_bytes().to_vec()),
        Pattern::App {
            symbol,
            sorts,
            args,
        } => {
            let mut items = vec![
                SExp::symbol("app"),
                SExp::symbol(symbol.clone()),
                tagged_sorts("sorts", sorts),
            ];
            items.extend(args.iter().map(pattern_to_sexp));
            SExp::List(items)
        }
        Pattern::Top(s) => SExp::List(vec![SExp::symbol("\\top"), sort_to_sexp(s)]),
        Pattern::Bottom(s) => SExp::List(vec![SExp::symbol("\\bottom"), sort_to_sexp(s)]),
        Pattern::Not(s, p) => unary("\\not", s, p),
        Pattern::Next(s, p) => unary("\\next", s, p),
        Pattern::And(s, args) => nary("\\and", s, args),
        Pattern::Or(s, args) => nary("\\or", s, args),
        Pattern::Implies(s, a, b) => binary("\\implies", s, a, b),
        Pattern::Iff(s, a, b) => binary("\\iff", s, a, b),
        Pattern::Rewrites(s, a, b) => binary("\\rewrites", s, a, b),
        Pattern::Exists {
            sort,
            var,
            var_sort,
            body,
        } => quantifier("\\exists", sort, var, var_sort, body),
        Pattern::Forall {
            sort,
            var,
            var_sort,
            body,
        } => quantifier("\\forall", sort, var, var_sort, body),
        Pattern::Mu {
            var,
            var_sort,
            body,
        } => fixpoint("\\mu", var, var_sort, body),
        Pattern::Nu {
            var,
            var_sort,
            body,
        } => fixpoint("\\nu", var, var_sort, body),
        Pattern::Ceil {
            arg_sort,
            sort,
            arg,
        } => SExp::List(vec![
            SExp::symbol("\\ceil"),
            sort_to_sexp(arg_sort),
            sort_to_sexp(sort),
            pattern_to_sexp(arg),
        ]),
        Pattern::Floor {
            arg_sort,
            sort,
            arg,
        } => SExp::List(vec![
            SExp::symbol("\\floor"),
            sort_to_sexp(arg_sort),
            sort_to_sexp(sort),
            pattern_to_sexp(arg),
        ]),
        Pattern::Equals {
            arg_sort,
            sort,
            lhs,
            rhs,
        } => SExp::List(vec![
            SExp::symbol("\\equals"),
            sort_to_sexp(arg_sort),
            sort_to_sexp(sort),
            pattern_to_sexp(lhs),
            pattern_to_sexp(rhs),
        ]),
        Pattern::In {
            arg_sort,
            sort,
            lhs,
            rhs,
        } => SExp::List(vec![
            SExp::symbol("\\in"),
            sort_to_sexp(arg_sort),
            sort_to_sexp(sort),
            pattern_to_sexp(lhs),
            pattern_to_sexp(rhs),
        ]),
        Pattern::DV(s, lit) => SExp::List(vec![
            SExp::symbol("dv"),
            sort_to_sexp(s),
            SExp::string("", lit.as_bytes().to_vec()),
        ]),
    }
}

/// Render any SExpr to its canonical text via `covalence_sexp::prettyprint`.
pub fn to_text(sexp: &SExpr) -> String {
    let mut buf = Vec::new();
    prettyprint(std::slice::from_ref(sexp), &mut buf).expect("write to Vec never fails");
    String::from_utf8(buf).expect("prettyprint produces valid UTF-8")
}

// -- helpers ----------------------------------------------------------------

fn attrs_to_sexp(attrs: &[Pattern]) -> SExpr {
    let mut items = vec![SExp::symbol("attrs")];
    items.extend(attrs.iter().map(pattern_to_sexp));
    SExp::List(items)
}

fn sort_vars_to_sexp(vars: &[smol_str::SmolStr]) -> SExpr {
    let mut items = vec![SExp::symbol("sort-vars")];
    items.extend(vars.iter().map(|v| SExp::symbol(v.clone())));
    SExp::List(items)
}

fn tagged_sorts(tag: &str, sorts: &[Sort]) -> SExpr {
    let mut items = vec![SExp::symbol(tag)];
    items.extend(sorts.iter().map(sort_to_sexp));
    SExp::List(items)
}

fn unary(head: &str, s: &Sort, p: &Pattern) -> SExpr {
    SExp::List(vec![
        SExp::symbol(head),
        sort_to_sexp(s),
        pattern_to_sexp(p),
    ])
}

fn nary(head: &str, s: &Sort, args: &[Pattern]) -> SExpr {
    let mut items = vec![SExp::symbol(head), sort_to_sexp(s)];
    items.extend(args.iter().map(pattern_to_sexp));
    SExp::List(items)
}

fn binary(head: &str, s: &Sort, a: &Pattern, b: &Pattern) -> SExpr {
    SExp::List(vec![
        SExp::symbol(head),
        sort_to_sexp(s),
        pattern_to_sexp(a),
        pattern_to_sexp(b),
    ])
}

fn quantifier(head: &str, sort: &Sort, var: &str, var_sort: &Sort, body: &Pattern) -> SExpr {
    SExp::List(vec![
        SExp::symbol(head),
        sort_to_sexp(sort),
        SExp::List(vec![
            SExp::symbol("evar"),
            SExp::symbol(var),
            sort_to_sexp(var_sort),
        ]),
        pattern_to_sexp(body),
    ])
}

fn fixpoint(head: &str, var: &str, var_sort: &Sort, body: &Pattern) -> SExpr {
    SExp::List(vec![
        SExp::symbol(head),
        SExp::List(vec![
            SExp::symbol("svar"),
            SExp::symbol(var),
            sort_to_sexp(var_sort),
        ]),
        pattern_to_sexp(body),
    ])
}
