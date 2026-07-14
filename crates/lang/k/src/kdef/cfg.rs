//! Lower a parsed `.k` grammar ([`crate::kdef::ast`]) to a
//! [`covalence_grammar::Cfg`]`<char>` — the neutral context-free-grammar IR the
//! kernel CFG stratum (`covalence_init::grammar::cfg`) turns into
//! `Derives` judgements. This is what connects "parse a K tutorial language's
//! grammar" to "internally certify that a token string is a valid program".
//!
//! # What is preserved and what is flattened
//!
//! A K `syntax Sort ::= …` production is, structurally, a CFG production: the
//! sort is the left-hand non-terminal, terminals (`"lambda"`, `"+"`) become
//! terminal segments (a char-exact [`Regex`]), and non-terminals become
//! references. We deliberately **flatten** the disambiguation layer:
//!
//! - **Priority (`>`) and associativity (`[left]`/`left:`)** are parse-time
//!   *filters* over the same underlying CFG — the raw context-free language is
//!   priority-free — so all priority blocks collapse into plain alternatives.
//! - **`[bracket]`** productions are kept verbatim (they are real productions of
//!   the recognised language: `Exp ::= "(" Exp ")"`).
//! - **`List{E,"s"}`** desugars to `S ::= ε | E | E "s" S`; **`NeList`** to
//!   `S ::= E | E "s" S`.
//! - **Imported token sorts** (`Id`, `Int`, `Bool` from `DOMAINS-SYNTAX`) are
//!   referenced but not defined in the module. How they get concrete syntax is a
//!   swappable **strategy** — the [`SortResolver`] trait: [`NoDomains`] leaves
//!   them empty non-terminals (structural reference only); [`KDomains`] injects
//!   the standard K builtin token regexes so the CFG recognises real programs; a
//!   future resolver could parse the imported module transitively.
//!
//! The result is structurally valid ([`Cfg::validate`]) either way.

use covalence_grammar::{Cfg, CfgError, NtId, Regex, Seg, parse_regex};

use crate::kdef::ast::{KDefinition, KModule, ListDecl, ProdItem, Sort, SyntaxDecl};

/// Strategy for resolving sorts a module *references* but does not *define* —
/// typically the builtin token sorts imported from `DOMAINS-SYNTAX` (`Id`,
/// `Int`, `Bool`, …). Swap implementations to change how those sorts are given
/// concrete syntax in the lowered CFG, without touching the lowering itself.
pub trait SortResolver {
    /// Token production(s) for an otherwise-undefined `sort`, as terminal
    /// regexes. `None` leaves the sort an empty non-terminal (a structural
    /// reference only); `Some(vec![r₁, r₂])` adds `sort ::= r₁ | r₂` (one
    /// single-terminal production per regex).
    fn token_regexes(&self, sort: &str) -> Option<Vec<Regex<char>>>;
}

/// The pure-structural resolver: leaves every imported sort an empty
/// non-terminal. The lowered CFG then captures grammar *shape* only (no imported
/// tokens can be recognised, but every reference resolves).
#[derive(Debug, Clone, Copy, Default)]
pub struct NoDomains;

impl SortResolver for NoDomains {
    fn token_regexes(&self, _sort: &str) -> Option<Vec<Regex<char>>> {
        None
    }
}

/// The standard K `DOMAINS-SYNTAX` builtin token sorts. Injects the usual
/// regexes so the lowered CFG can actually recognise programs over `Id`/`Int`/
/// `Bool`. (Layout/whitespace between tokens is a separate scanner concern — see
/// `SKELETONS.md` — so this recognises token-adjacent input only.)
#[derive(Debug, Clone, Copy, Default)]
pub struct KDomains;

impl SortResolver for KDomains {
    fn token_regexes(&self, sort: &str) -> Option<Vec<Regex<char>>> {
        let one = |pat: &str| Some(vec![parse_regex(pat).expect("builtin regex parses")]);
        match sort {
            // K's `Id` token (identifiers). Keyword exclusion is a scanner
            // concern, omitted here.
            "Id" => one("[a-zA-Z_][a-zA-Z0-9_]*"),
            // Unsigned integer literal — K spells signed ints with a unary-minus
            // production, so the token itself is unsigned.
            "Int" => one("[0-9]+"),
            "Bool" => Some(vec![
                parse_regex("true").unwrap(),
                parse_regex("false").unwrap(),
            ]),
            _ => None,
        }
    }
}

/// Lower a single module's `syntax` declarations to a validated `Cfg<char>`,
/// using [`NoDomains`] (structural only). For imported token sorts, use
/// [`module_to_cfg_with`] with [`KDomains`].
pub fn module_to_cfg(m: &KModule) -> Result<Cfg<char>, CfgError> {
    module_to_cfg_with(m, &NoDomains)
}

/// Lower a module's `syntax` declarations to a `Cfg<char>`, resolving sorts the
/// module references but does not define via `resolver`.
pub fn module_to_cfg_with(m: &KModule, resolver: &dyn SortResolver) -> Result<Cfg<char>, CfgError> {
    let mut cfg = Cfg::new();
    for decl in &m.syntax {
        lower_decl(&mut cfg, decl);
    }
    resolve_undefined(&mut cfg, resolver);
    cfg.validate()?;
    Ok(cfg)
}

/// Give a token production to every referenced non-terminal that has none yet
/// and that `resolver` recognises (the imported `DOMAINS-SYNTAX` sorts).
fn resolve_undefined(cfg: &mut Cfg<char>, resolver: &dyn SortResolver) {
    let names: Vec<String> = cfg.nts().iter().map(|d| d.name.clone()).collect();
    for name in names {
        let Some(id) = cfg.lookup(&name) else {
            continue;
        };
        if cfg.productions_of(id).next().is_some() {
            continue; // the module defines this sort
        }
        if let Some(regexes) = resolver.token_regexes(&name) {
            for r in regexes {
                cfg.add_prod(id, vec![Seg::term(r)]);
            }
        }
    }
}

/// Lower the module named `module` to a `Cfg` ([`NoDomains`] resolver). Returns
/// `None` if no module of that name exists.
pub fn definition_to_cfg(def: &KDefinition, module: &str) -> Option<Result<Cfg<char>, CfgError>> {
    definition_to_cfg_with(def, module, &NoDomains)
}

/// [`definition_to_cfg`] with an explicit [`SortResolver`].
pub fn definition_to_cfg_with(
    def: &KDefinition,
    module: &str,
    resolver: &dyn SortResolver,
) -> Option<Result<Cfg<char>, CfgError>> {
    def.modules
        .iter()
        .find(|m| m.name == module)
        .map(|m| module_to_cfg_with(m, resolver))
}

fn nt(cfg: &mut Cfg<char>, sort: &Sort) -> NtId {
    cfg.get_or_add_nt(sort.name.as_str())
}

fn lower_decl(cfg: &mut Cfg<char>, decl: &SyntaxDecl) {
    let lhs = nt(cfg, &decl.sort);
    if let Some(list) = &decl.list {
        lower_list(cfg, lhs, list);
        return;
    }
    for block in &decl.blocks {
        for prod in &block.prods {
            let segs: Vec<Seg<char>> = prod
                .items
                .iter()
                .map(|item| seg_of_item(cfg, item))
                .collect();
            cfg.add_prod(lhs, segs);
        }
    }
}

/// `List{E,"s"}` → `S ::= ε | E | E "s" S`; `NeList` → `S ::= E | E "s" S`.
fn lower_list(cfg: &mut Cfg<char>, lhs: NtId, list: &ListDecl) {
    let elem = nt(cfg, &list.elem);
    if !list.non_empty {
        cfg.add_prod(lhs, vec![]); // ε (possibly-empty)
    }
    cfg.add_prod(lhs, vec![Seg::nt(elem)]); // single element
    // element separator element … (right-recursive)
    let mut cons = vec![Seg::nt(elem)];
    if !list.sep.is_empty() {
        cons.push(Seg::term(term_regex(&list.sep)));
    }
    cons.push(Seg::nt(lhs));
    cfg.add_prod(lhs, cons);
}

fn seg_of_item(cfg: &mut Cfg<char>, item: &ProdItem) -> Seg<char> {
    match item {
        ProdItem::Terminal(t) => Seg::term(term_regex(t)),
        ProdItem::NonTerminal { sort, .. } => Seg::nt(nt(cfg, sort)),
    }
}

/// A terminal string → a char-exact regex (`"lambda"` → `l·a·m·b·d·a`); the
/// empty string → `ε`.
fn term_regex(t: &str) -> Regex<char> {
    Regex::concat(t.chars().map(Regex::lit))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kdef::parse::parse_definition;

    const LAMBDA: &str = include_str!("../../examples/k-tutorial/lambda.k");

    #[test]
    fn lambda_syntax_lowers_to_a_valid_cfg() {
        let def = parse_definition(LAMBDA).unwrap();
        let cfg = definition_to_cfg(&def, "LAMBDA-SYNTAX").unwrap().unwrap();
        // Sorts: Val, Id, Exp (Id imported from DOMAINS-SYNTAX → empty NT).
        assert!(cfg.lookup("Val").is_some());
        assert!(cfg.lookup("Exp").is_some());
        assert!(cfg.lookup("Id").is_some());
        // Exp has three productions: Val | Exp Exp | "(" Exp ")".
        let exp = cfg.lookup("Exp").unwrap();
        assert_eq!(cfg.productions_of(exp).count(), 3);
        // Val has two: Id | "lambda" Id "." Exp.
        let val = cfg.lookup("Val").unwrap();
        assert_eq!(cfg.productions_of(val).count(), 2);
    }

    #[test]
    fn bracket_production_is_kept() {
        let def = parse_definition(LAMBDA).unwrap();
        let cfg = definition_to_cfg(&def, "LAMBDA-SYNTAX").unwrap().unwrap();
        let exp = cfg.lookup("Exp").unwrap();
        // One Exp production is "(" Exp ")": 3 segments, first terminal '('.
        let has_paren = cfg.productions_of(exp).any(|(_, p)| {
            p.segs.len() == 3 && matches!(&p.segs[0], Seg::Term(r) if matches!(r, Regex::Lit('(')))
        });
        assert!(has_paren, "the [bracket] production should be present");
    }

    #[test]
    fn no_domains_leaves_id_empty_but_kdomains_fills_it() {
        let def = parse_definition(LAMBDA).unwrap();

        // Structural resolver: Id is a referenced-but-empty non-terminal.
        let structural = definition_to_cfg(&def, "LAMBDA-SYNTAX").unwrap().unwrap();
        let id = structural.lookup("Id").unwrap();
        assert_eq!(structural.productions_of(id).count(), 0);

        // KDomains resolver: Id gets its token regex, and now recognises a real
        // identifier (token-adjacent input — no layout).
        let filled = definition_to_cfg_with(&def, "LAMBDA-SYNTAX", &KDomains)
            .unwrap()
            .unwrap();
        let id = filled.lookup("Id").unwrap();
        assert_eq!(filled.productions_of(id).count(), 1);
        let word: Vec<char> = "foo".chars().collect();
        assert!(filled.naive_parse(id, &word), "Id should accept `foo`");
        assert!(
            !filled.naive_parse(id, &"9x".chars().collect::<Vec<_>>()),
            "Id must not start with a digit"
        );
    }
}
