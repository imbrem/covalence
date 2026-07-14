//! Canonical S-expression rendering of the parsed `.k` grammar
//! ([`crate::kdef::ast`]) — the deterministic interchange IR downstream
//! consumers read instead of `.k` syntax. `to_sexp` direction only.
//!
//! # Canonical shapes
//!
//! ```text
//! definition:  (kdef (requires "f"…) MODULE…)
//! module:      (module NAME (attrs ATTR…) (imports IMPORT…) SYNTAX… (skipped N))
//! import:      (import NAME) | (import public NAME) | (import private NAME)
//! syntax:      (syntax SORT BLOCK…)                 ; productions, tightest block first
//!              (syntax SORT (list ELEM "sep"))      ; List{…}   ((nelist …) for NeList)
//!              (syntax-sort SORT (attrs ATTR…))     ; bare sort declaration
//! block:       (block ASSOC? PROD…)                 ; ASSOC = left|right|non-assoc
//! production:  (prod (items ITEM…) (attrs ATTR…))
//! item:        "terminal"                           ; a terminal string atom
//!              (nt SORT) | (nt LABEL SORT)          ; non-terminal (opt. field label)
//! sort:        NAME | (sort NAME PARAM…)            ; nullary → plain symbol
//! attr:        KEY | (KEY "arg")
//! ```

use covalence_sexp::{SExp, SExpr, prettyprint};

use crate::kdef::ast::{
    Assoc, Attr, Import, KDefinition, KModule, ListDecl, PriorityBlock, ProdItem, Production, Sort,
    SyntaxDecl,
};

/// Render a whole `.k` grammar definition.
pub fn definition_to_sexp(def: &KDefinition) -> SExpr {
    let mut items = vec![SExp::symbol("kdef"), requires_to_sexp(&def.requires)];
    items.extend(def.modules.iter().map(module_to_sexp));
    SExp::List(items)
}

fn requires_to_sexp(reqs: &[String]) -> SExpr {
    let mut items = vec![SExp::symbol("requires")];
    items.extend(reqs.iter().map(|r| SExp::string("", r.as_bytes().to_vec())));
    SExp::List(items)
}

/// Render a module.
pub fn module_to_sexp(m: &KModule) -> SExpr {
    let mut items = vec![SExp::symbol("module"), SExp::symbol(m.name.clone())];
    items.push(attrs_to_sexp(&m.attrs));
    let mut imports = vec![SExp::symbol("imports")];
    imports.extend(m.imports.iter().map(import_to_sexp));
    items.push(SExp::List(imports));
    items.extend(m.syntax.iter().map(syntax_to_sexp));
    items.push(SExp::List(vec![
        SExp::symbol("skipped"),
        SExp::symbol(m.skipped_sentences.to_string()),
    ]));
    SExp::List(items)
}

fn import_to_sexp(i: &Import) -> SExpr {
    let mut items = vec![SExp::symbol("import")];
    match i.public {
        Some(true) => items.push(SExp::symbol("public")),
        Some(false) => items.push(SExp::symbol("private")),
        None => {}
    }
    items.push(SExp::symbol(i.name.clone()));
    SExp::List(items)
}

/// Render one `syntax` declaration.
pub fn syntax_to_sexp(d: &SyntaxDecl) -> SExpr {
    if let Some(list) = &d.list {
        return SExp::List(vec![
            SExp::symbol("syntax"),
            sort_to_sexp(&d.sort),
            list_to_sexp(list),
        ]);
    }
    if d.blocks.is_empty() {
        // Bare sort declaration.
        return SExp::List(vec![
            SExp::symbol("syntax-sort"),
            sort_to_sexp(&d.sort),
            attrs_to_sexp(&d.attrs),
        ]);
    }
    let mut items = vec![SExp::symbol("syntax"), sort_to_sexp(&d.sort)];
    items.extend(d.blocks.iter().map(block_to_sexp));
    SExp::List(items)
}

fn list_to_sexp(l: &ListDecl) -> SExpr {
    SExp::List(vec![
        SExp::symbol(if l.non_empty { "nelist" } else { "list" }),
        sort_to_sexp(&l.elem),
        SExp::string("", l.sep.as_bytes().to_vec()),
    ])
}

fn block_to_sexp(b: &PriorityBlock) -> SExpr {
    let mut items = vec![SExp::symbol("block")];
    if let Some(a) = b.assoc {
        items.push(SExp::symbol(match a {
            Assoc::Left => "left",
            Assoc::Right => "right",
            Assoc::NonAssoc => "non-assoc",
        }));
    }
    items.extend(b.prods.iter().map(prod_to_sexp));
    SExp::List(items)
}

fn prod_to_sexp(p: &Production) -> SExpr {
    let mut items = vec![SExp::symbol("items")];
    items.extend(p.items.iter().map(item_to_sexp));
    SExp::List(vec![
        SExp::symbol("prod"),
        SExp::List(items),
        attrs_to_sexp(&p.attrs),
    ])
}

fn item_to_sexp(it: &ProdItem) -> SExpr {
    match it {
        ProdItem::Terminal(s) => SExp::string("", s.as_bytes().to_vec()),
        ProdItem::NonTerminal { label, sort } => {
            let mut items = vec![SExp::symbol("nt")];
            if let Some(l) = label {
                items.push(SExp::symbol(l.clone()));
            }
            items.push(sort_to_sexp(sort));
            SExp::List(items)
        }
    }
}

/// Render a sort: nullary → a plain symbol, parametric → `(sort NAME PARAM…)`.
pub fn sort_to_sexp(s: &Sort) -> SExpr {
    if s.params.is_empty() {
        SExp::symbol(s.name.clone())
    } else {
        let mut items = vec![SExp::symbol("sort"), SExp::symbol(s.name.clone())];
        items.extend(s.params.iter().map(sort_to_sexp));
        SExp::List(items)
    }
}

fn attrs_to_sexp(attrs: &[Attr]) -> SExpr {
    let mut items = vec![SExp::symbol("attrs")];
    items.extend(attrs.iter().map(attr_to_sexp));
    SExp::List(items)
}

fn attr_to_sexp(a: &Attr) -> SExpr {
    match &a.arg {
        None => SExp::symbol(a.key.clone()),
        Some(arg) => SExp::List(vec![
            SExp::symbol(a.key.clone()),
            SExp::string("", arg.as_bytes().to_vec()),
        ]),
    }
}

/// Render any SExpr to its canonical text via `covalence_sexp::prettyprint`.
pub fn to_text(sexp: &SExpr) -> String {
    let mut buf = Vec::new();
    prettyprint(std::slice::from_ref(sexp), &mut buf).expect("write to Vec never fails");
    String::from_utf8(buf).expect("prettyprint produces valid UTF-8")
}
