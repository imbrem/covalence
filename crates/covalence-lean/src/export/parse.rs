use std::io::BufRead;
use std::sync::Arc;

use serde::Deserialize;
use smol_str::SmolStr;

use super::decl::{
    AxiomInfo, CtorInfo, Decl, DefnInfo, InductInfo, OpaqueInfo, QuotInfo, QuotKind, RecInfo,
    RecRule, ReducibilityHint, Safety, ThmInfo,
};
use super::env::Env;
use super::expr::{BinderInfo, Expr, Literal};
use super::level::Level;
use super::name::Name;

/// Error during NDJSON parsing.
#[derive(Debug, thiserror::Error)]
pub enum ParseError {
    #[error("JSON error at line {line}: {source}")]
    Json {
        line: usize,
        #[source]
        source: serde_json::Error,
    },
    #[error("invalid name index {0}")]
    InvalidNameIndex(usize),
    #[error("invalid level index {0}")]
    InvalidLevelIndex(usize),
    #[error("invalid expr index {0}")]
    InvalidExprIndex(usize),
    #[error("unknown binder info: {0}")]
    UnknownBinderInfo(String),
    #[error("unknown declaration kind at line {0}")]
    UnknownDeclKind(usize),
    #[error("unknown safety value: {0}")]
    UnknownSafety(String),
    #[error("unknown quot kind: {0}")]
    UnknownQuotKind(String),
    #[error("unknown reducibility hint kind: {0}")]
    UnknownHintKind(String),
    #[error("I/O error: {0}")]
    Io(#[from] std::io::Error),
}

/// Parse an NDJSON string into a Lean environment.
pub fn parse_ndjson(input: &str) -> Result<Env, ParseError> {
    parse_ndjson_reader(input.as_bytes())
}

/// Parse NDJSON from a reader into a Lean environment.
pub fn parse_ndjson_reader(reader: impl BufRead) -> Result<Env, ParseError> {
    let mut ctx = ParseCtx::new();

    for (line_num, line) in reader.lines().enumerate() {
        let line = line.map_err(ParseError::Io)?;
        let line = line.trim();
        if line.is_empty() {
            continue;
        }
        let entry: RawEntry = serde_json::from_str(line).map_err(|e| ParseError::Json {
            line: line_num + 1,
            source: e,
        })?;
        ctx.process_entry(entry, line_num + 1)?;
    }

    Ok(Env { decls: ctx.decls })
}

// ---------------------------------------------------------------------------
// Raw serde types (close to JSON schema, index-based)
// ---------------------------------------------------------------------------

#[derive(Deserialize)]
#[serde(tag = "kind")]
#[allow(dead_code)] // idx fields are consumed by serde but not read in Rust
enum RawEntry {
    // Names
    #[serde(rename = "name_anon")]
    NameAnon { idx: usize },
    #[serde(rename = "name_str")]
    NameStr {
        idx: usize,
        prefix: usize,
        name: String,
    },
    #[serde(rename = "name_num")]
    NameNum { idx: usize, prefix: usize, num: u64 },

    // Levels
    #[serde(rename = "level_zero")]
    LevelZero { idx: usize },
    #[serde(rename = "level_succ")]
    LevelSucc { idx: usize, pred: usize },
    #[serde(rename = "level_max")]
    LevelMax { idx: usize, lhs: usize, rhs: usize },
    #[serde(rename = "level_imax")]
    LevelIMax { idx: usize, lhs: usize, rhs: usize },
    #[serde(rename = "level_param")]
    LevelParam { idx: usize, name: usize },

    // Expressions
    #[serde(rename = "expr_bvar")]
    ExprBVar { idx: usize, de_bruijn: u32 },
    #[serde(rename = "expr_sort")]
    ExprSort { idx: usize, level: usize },
    #[serde(rename = "expr_const")]
    ExprConst {
        idx: usize,
        name: usize,
        levels: Vec<usize>,
    },
    #[serde(rename = "expr_app")]
    ExprApp {
        idx: usize,
        #[serde(rename = "fn")]
        func: usize,
        arg: usize,
    },
    #[serde(rename = "expr_lam")]
    ExprLam {
        idx: usize,
        name: usize,
        info: String,
        dom: usize,
        body: usize,
    },
    #[serde(rename = "expr_pi")]
    ExprPi {
        idx: usize,
        name: usize,
        info: String,
        dom: usize,
        body: usize,
    },
    #[serde(rename = "expr_let")]
    ExprLet {
        idx: usize,
        name: usize,
        #[serde(rename = "type")]
        ty: usize,
        val: usize,
        body: usize,
    },
    #[serde(rename = "expr_proj")]
    ExprProj {
        idx: usize,
        name: usize,
        proj_idx: u32,
        #[serde(rename = "struct")]
        struc: usize,
    },
    #[serde(rename = "expr_lit_nat")]
    ExprLitNat { idx: usize, val: u64 },
    #[serde(rename = "expr_lit_str")]
    ExprLitStr { idx: usize, val: String },

    // Declarations
    #[serde(rename = "axiom")]
    Axiom {
        name: usize,
        level_params: Vec<usize>,
        #[serde(rename = "type")]
        ty: usize,
        is_unsafe: bool,
    },
    #[serde(rename = "def")]
    Def {
        name: usize,
        level_params: Vec<usize>,
        #[serde(rename = "type")]
        ty: usize,
        value: usize,
        hints: RawHint,
        safety: String,
        all: Vec<usize>,
    },
    #[serde(rename = "theorem")]
    Theorem {
        name: usize,
        level_params: Vec<usize>,
        #[serde(rename = "type")]
        ty: usize,
        value: usize,
        all: Vec<usize>,
    },
    #[serde(rename = "opaque")]
    Opaque {
        name: usize,
        level_params: Vec<usize>,
        #[serde(rename = "type")]
        ty: usize,
        value: usize,
        is_unsafe: bool,
        all: Vec<usize>,
    },
    #[serde(rename = "quot")]
    Quot {
        name: usize,
        level_params: Vec<usize>,
        #[serde(rename = "type")]
        ty: usize,
        quot_kind: String,
    },
    #[serde(rename = "inductive")]
    Inductive {
        name: usize,
        level_params: Vec<usize>,
        #[serde(rename = "type")]
        ty: usize,
        num_params: u32,
        num_indices: u32,
        all: Vec<usize>,
        ctors: Vec<usize>,
        is_recursive: bool,
        is_reflexive: bool,
        is_nested: bool,
        is_unsafe: bool,
    },
    #[serde(rename = "constructor")]
    Constructor {
        name: usize,
        level_params: Vec<usize>,
        #[serde(rename = "type")]
        ty: usize,
        induct: usize,
        cidx: u32,
        num_params: u32,
        num_fields: u32,
        is_unsafe: bool,
    },
    #[serde(rename = "recursor")]
    Recursor {
        name: usize,
        level_params: Vec<usize>,
        #[serde(rename = "type")]
        ty: usize,
        all: Vec<usize>,
        num_params: u32,
        num_indices: u32,
        num_motives: u32,
        num_minors: u32,
        rules: Vec<RawRecRule>,
        k: bool,
        is_unsafe: bool,
    },
}

#[derive(Deserialize)]
#[serde(tag = "kind")]
enum RawHint {
    #[serde(rename = "opaque")]
    Opaque,
    #[serde(rename = "abbrev")]
    Abbrev,
    #[serde(rename = "regular")]
    Regular { height: u32 },
}

#[derive(Deserialize)]
struct RawRecRule {
    ctor: usize,
    nfields: u32,
    rhs: usize,
}

// ---------------------------------------------------------------------------
// Parse context: maintains indexed arrays, resolves references
// ---------------------------------------------------------------------------

struct ParseCtx {
    names: Vec<Name>,
    levels: Vec<Arc<Level>>,
    exprs: Vec<Arc<Expr>>,
    decls: Vec<Decl>,
}

impl ParseCtx {
    fn new() -> Self {
        ParseCtx {
            names: Vec::new(),
            levels: Vec::new(),
            exprs: Vec::new(),
            decls: Vec::new(),
        }
    }

    fn get_name(&self, idx: usize) -> Result<Name, ParseError> {
        self.names
            .get(idx)
            .cloned()
            .ok_or(ParseError::InvalidNameIndex(idx))
    }

    fn get_level(&self, idx: usize) -> Result<Arc<Level>, ParseError> {
        self.levels
            .get(idx)
            .cloned()
            .ok_or(ParseError::InvalidLevelIndex(idx))
    }

    fn get_expr(&self, idx: usize) -> Result<Arc<Expr>, ParseError> {
        self.exprs
            .get(idx)
            .cloned()
            .ok_or(ParseError::InvalidExprIndex(idx))
    }

    fn resolve_names(&self, indices: &[usize]) -> Result<Vec<Name>, ParseError> {
        indices.iter().map(|&i| self.get_name(i)).collect()
    }

    fn resolve_levels(&self, indices: &[usize]) -> Result<Vec<Arc<Level>>, ParseError> {
        indices.iter().map(|&i| self.get_level(i)).collect()
    }

    fn parse_binder_info(s: &str) -> Result<BinderInfo, ParseError> {
        match s {
            "default" => Ok(BinderInfo::Default),
            "implicit" => Ok(BinderInfo::Implicit),
            "strict_implicit" => Ok(BinderInfo::StrictImplicit),
            "inst_implicit" => Ok(BinderInfo::InstImplicit),
            _ => Err(ParseError::UnknownBinderInfo(s.to_string())),
        }
    }

    fn parse_safety(s: &str) -> Result<Safety, ParseError> {
        match s {
            "safe" => Ok(Safety::Safe),
            "unsafe" => Ok(Safety::Unsafe),
            "partial" => Ok(Safety::Partial),
            _ => Err(ParseError::UnknownSafety(s.to_string())),
        }
    }

    fn parse_quot_kind(s: &str) -> Result<QuotKind, ParseError> {
        match s {
            "type" => Ok(QuotKind::Type),
            "ctor" => Ok(QuotKind::Ctor),
            "lift" => Ok(QuotKind::Lift),
            "ind" => Ok(QuotKind::Ind),
            _ => Err(ParseError::UnknownQuotKind(s.to_string())),
        }
    }

    fn process_entry(&mut self, entry: RawEntry, _line: usize) -> Result<(), ParseError> {
        match entry {
            // Names
            RawEntry::NameAnon { .. } => {
                self.names.push(Name::Anon);
            }
            RawEntry::NameStr { prefix, name, .. } => {
                let prefix = self.get_name(prefix)?;
                self.names
                    .push(Name::Str(Arc::new(prefix), SmolStr::new(&name)));
            }
            RawEntry::NameNum { prefix, num, .. } => {
                let prefix = self.get_name(prefix)?;
                self.names.push(Name::Num(Arc::new(prefix), num));
            }

            // Levels
            RawEntry::LevelZero { .. } => {
                self.levels.push(Arc::new(Level::Zero));
            }
            RawEntry::LevelSucc { pred, .. } => {
                let pred = self.get_level(pred)?;
                self.levels.push(Arc::new(Level::Succ(pred)));
            }
            RawEntry::LevelMax { lhs, rhs, .. } => {
                let lhs = self.get_level(lhs)?;
                let rhs = self.get_level(rhs)?;
                self.levels.push(Arc::new(Level::Max(lhs, rhs)));
            }
            RawEntry::LevelIMax { lhs, rhs, .. } => {
                let lhs = self.get_level(lhs)?;
                let rhs = self.get_level(rhs)?;
                self.levels.push(Arc::new(Level::IMax(lhs, rhs)));
            }
            RawEntry::LevelParam { name, .. } => {
                let name = self.get_name(name)?;
                self.levels.push(Arc::new(Level::Param(name)));
            }

            // Expressions
            RawEntry::ExprBVar { de_bruijn, .. } => {
                self.exprs.push(Arc::new(Expr::BVar(de_bruijn)));
            }
            RawEntry::ExprSort { level, .. } => {
                let level = self.get_level(level)?;
                self.exprs.push(Arc::new(Expr::Sort(level)));
            }
            RawEntry::ExprConst { name, levels, .. } => {
                let name = self.get_name(name)?;
                let levels = self.resolve_levels(&levels)?;
                self.exprs.push(Arc::new(Expr::Const(name, levels)));
            }
            RawEntry::ExprApp { func, arg, .. } => {
                let func = self.get_expr(func)?;
                let arg = self.get_expr(arg)?;
                self.exprs.push(Arc::new(Expr::App(func, arg)));
            }
            RawEntry::ExprLam {
                name,
                info,
                dom,
                body,
                ..
            } => {
                let name = self.get_name(name)?;
                let info = Self::parse_binder_info(&info)?;
                let dom = self.get_expr(dom)?;
                let body = self.get_expr(body)?;
                self.exprs.push(Arc::new(Expr::Lam(name, info, dom, body)));
            }
            RawEntry::ExprPi {
                name,
                info,
                dom,
                body,
                ..
            } => {
                let name = self.get_name(name)?;
                let info = Self::parse_binder_info(&info)?;
                let dom = self.get_expr(dom)?;
                let body = self.get_expr(body)?;
                self.exprs.push(Arc::new(Expr::Pi(name, info, dom, body)));
            }
            RawEntry::ExprLet {
                name,
                ty,
                val,
                body,
                ..
            } => {
                let name = self.get_name(name)?;
                let ty = self.get_expr(ty)?;
                let val = self.get_expr(val)?;
                let body = self.get_expr(body)?;
                self.exprs.push(Arc::new(Expr::Let(name, ty, val, body)));
            }
            RawEntry::ExprProj {
                name,
                proj_idx,
                struc,
                ..
            } => {
                let name = self.get_name(name)?;
                let struc = self.get_expr(struc)?;
                self.exprs.push(Arc::new(Expr::Proj(name, proj_idx, struc)));
            }
            RawEntry::ExprLitNat { val, .. } => {
                self.exprs.push(Arc::new(Expr::Lit(Literal::Nat(val))));
            }
            RawEntry::ExprLitStr { val, .. } => {
                self.exprs.push(Arc::new(Expr::Lit(Literal::Str(val))));
            }

            // Declarations
            RawEntry::Axiom {
                name,
                level_params,
                ty,
                is_unsafe,
            } => {
                self.decls.push(Decl::Axiom(AxiomInfo {
                    name: self.get_name(name)?,
                    level_params: self.resolve_names(&level_params)?,
                    ty: self.get_expr(ty)?,
                    is_unsafe,
                }));
            }
            RawEntry::Def {
                name,
                level_params,
                ty,
                value,
                hints,
                safety,
                all,
            } => {
                let hints = match hints {
                    RawHint::Opaque => ReducibilityHint::Opaque,
                    RawHint::Abbrev => ReducibilityHint::Abbrev,
                    RawHint::Regular { height } => ReducibilityHint::Regular(height),
                };
                self.decls.push(Decl::Defn(DefnInfo {
                    name: self.get_name(name)?,
                    level_params: self.resolve_names(&level_params)?,
                    ty: self.get_expr(ty)?,
                    value: self.get_expr(value)?,
                    hints,
                    safety: Self::parse_safety(&safety)?,
                    all: self.resolve_names(&all)?,
                }));
            }
            RawEntry::Theorem {
                name,
                level_params,
                ty,
                value,
                all,
            } => {
                self.decls.push(Decl::Thm(ThmInfo {
                    name: self.get_name(name)?,
                    level_params: self.resolve_names(&level_params)?,
                    ty: self.get_expr(ty)?,
                    value: self.get_expr(value)?,
                    all: self.resolve_names(&all)?,
                }));
            }
            RawEntry::Opaque {
                name,
                level_params,
                ty,
                value,
                is_unsafe,
                all,
            } => {
                self.decls.push(Decl::Opaque(OpaqueInfo {
                    name: self.get_name(name)?,
                    level_params: self.resolve_names(&level_params)?,
                    ty: self.get_expr(ty)?,
                    value: self.get_expr(value)?,
                    is_unsafe,
                    all: self.resolve_names(&all)?,
                }));
            }
            RawEntry::Quot {
                name,
                level_params,
                ty,
                quot_kind,
            } => {
                self.decls.push(Decl::Quot(QuotInfo {
                    name: self.get_name(name)?,
                    level_params: self.resolve_names(&level_params)?,
                    ty: self.get_expr(ty)?,
                    kind: Self::parse_quot_kind(&quot_kind)?,
                }));
            }
            RawEntry::Inductive {
                name,
                level_params,
                ty,
                num_params,
                num_indices,
                all,
                ctors,
                is_recursive,
                is_reflexive,
                is_nested,
                is_unsafe,
            } => {
                self.decls.push(Decl::Induct(InductInfo {
                    name: self.get_name(name)?,
                    level_params: self.resolve_names(&level_params)?,
                    ty: self.get_expr(ty)?,
                    num_params,
                    num_indices,
                    all: self.resolve_names(&all)?,
                    ctors: self.resolve_names(&ctors)?,
                    is_recursive,
                    is_reflexive,
                    is_nested,
                    is_unsafe,
                }));
            }
            RawEntry::Constructor {
                name,
                level_params,
                ty,
                induct,
                cidx,
                num_params,
                num_fields,
                is_unsafe,
            } => {
                self.decls.push(Decl::Ctor(CtorInfo {
                    name: self.get_name(name)?,
                    level_params: self.resolve_names(&level_params)?,
                    ty: self.get_expr(ty)?,
                    induct: self.get_name(induct)?,
                    cidx,
                    num_params,
                    num_fields,
                    is_unsafe,
                }));
            }
            RawEntry::Recursor {
                name,
                level_params,
                ty,
                all,
                num_params,
                num_indices,
                num_motives,
                num_minors,
                rules,
                k,
                is_unsafe,
            } => {
                let rules = rules
                    .into_iter()
                    .map(|r| {
                        Ok(RecRule {
                            ctor: self.get_name(r.ctor)?,
                            nfields: r.nfields,
                            rhs: self.get_expr(r.rhs)?,
                        })
                    })
                    .collect::<Result<Vec<_>, ParseError>>()?;
                self.decls.push(Decl::Rec(RecInfo {
                    name: self.get_name(name)?,
                    level_params: self.resolve_names(&level_params)?,
                    ty: self.get_expr(ty)?,
                    all: self.resolve_names(&all)?,
                    num_params,
                    num_indices,
                    num_motives,
                    num_minors,
                    rules,
                    k,
                    is_unsafe,
                }));
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Minimal NDJSON export: defines `Nat.zero : Nat` as an axiom.
    ///
    /// Names:  0=Anon, 1=Anon.Nat, 2=Anon.Nat.zero
    /// Levels: 0=Zero, 1=Succ(0)
    /// Exprs:  0=Sort(1) [Type 0], 1=Const(1, []) [Nat]
    /// Decl:   axiom Nat.zero : Nat
    const MINIMAL_EXPORT: &str = r#"{"kind":"name_anon","idx":0}
{"kind":"name_str","idx":1,"prefix":0,"name":"Nat"}
{"kind":"name_str","idx":2,"prefix":1,"name":"zero"}
{"kind":"level_zero","idx":0}
{"kind":"level_succ","idx":1,"pred":0}
{"kind":"expr_sort","idx":0,"level":1}
{"kind":"expr_const","idx":1,"name":1,"levels":[]}
{"kind":"axiom","name":2,"level_params":[],"type":1,"is_unsafe":false}
"#;

    #[test]
    fn parse_minimal_export() {
        let env = parse_ndjson(MINIMAL_EXPORT).unwrap();
        assert_eq!(env.decls.len(), 1);

        let decl = &env.decls[0];
        assert_eq!(decl.name().to_string(), "Nat.zero");

        match decl {
            Decl::Axiom(info) => {
                assert!(!info.is_unsafe);
                assert!(info.level_params.is_empty());
                // Type should be Const("Nat", [])
                match info.ty.as_ref() {
                    Expr::Const(name, levels) => {
                        assert_eq!(name.to_string(), "Nat");
                        assert!(levels.is_empty());
                    }
                    _ => panic!("expected Const"),
                }
            }
            _ => panic!("expected Axiom"),
        }
    }

    /// Export with a definition: `Nat.id := fun (n : Nat) => n`.
    const DEF_EXPORT: &str = r#"{"kind":"name_anon","idx":0}
{"kind":"name_str","idx":1,"prefix":0,"name":"Nat"}
{"kind":"name_str","idx":2,"prefix":1,"name":"id"}
{"kind":"name_str","idx":3,"prefix":0,"name":"n"}
{"kind":"level_zero","idx":0}
{"kind":"level_succ","idx":1,"pred":0}
{"kind":"expr_sort","idx":0,"level":1}
{"kind":"expr_const","idx":1,"name":1,"levels":[]}
{"kind":"expr_bvar","idx":2,"de_bruijn":0}
{"kind":"expr_pi","idx":3,"name":3,"info":"default","dom":1,"body":1}
{"kind":"expr_lam","idx":4,"name":3,"info":"default","dom":1,"body":2}
{"kind":"def","name":2,"level_params":[],"type":3,"value":4,"hints":{"kind":"regular","height":1},"safety":"safe","all":[2]}
"#;

    #[test]
    fn parse_definition() {
        let env = parse_ndjson(DEF_EXPORT).unwrap();
        assert_eq!(env.decls.len(), 1);

        match &env.decls[0] {
            Decl::Defn(info) => {
                assert_eq!(info.name.to_string(), "Nat.id");
                assert_eq!(info.safety, Safety::Safe);
                assert_eq!(info.hints, ReducibilityHint::Regular(1));
                // Type: Nat -> Nat (Pi)
                match info.ty.as_ref() {
                    Expr::Pi(_, BinderInfo::Default, _, _) => {}
                    _ => panic!("expected Pi"),
                }
                // Value: fun (n : Nat) => n (Lam)
                match info.value.as_ref() {
                    Expr::Lam(name, BinderInfo::Default, _, body) => {
                        assert_eq!(name.to_string(), "n");
                        assert_eq!(**body, Expr::BVar(0));
                    }
                    _ => panic!("expected Lam"),
                }
            }
            _ => panic!("expected Defn"),
        }
    }

    /// Universe-polymorphic constant: `List.nil.{u} : List.{u} α`.
    const POLY_EXPORT: &str = r#"{"kind":"name_anon","idx":0}
{"kind":"name_str","idx":1,"prefix":0,"name":"u"}
{"kind":"name_str","idx":2,"prefix":0,"name":"List"}
{"kind":"name_str","idx":3,"prefix":2,"name":"nil"}
{"kind":"level_zero","idx":0}
{"kind":"level_param","idx":1,"name":1}
{"kind":"expr_sort","idx":0,"level":1}
{"kind":"expr_const","idx":1,"name":2,"levels":[1]}
{"kind":"axiom","name":3,"level_params":[1],"type":0,"is_unsafe":false}
"#;

    #[test]
    fn parse_universe_polymorphic() {
        let env = parse_ndjson(POLY_EXPORT).unwrap();
        assert_eq!(env.decls.len(), 1);

        match &env.decls[0] {
            Decl::Axiom(info) => {
                assert_eq!(info.name.to_string(), "List.nil");
                assert_eq!(info.level_params.len(), 1);
                assert_eq!(info.level_params[0].to_string(), "u");
            }
            _ => panic!("expected Axiom"),
        }
    }

    #[test]
    fn parse_invalid_name_index() {
        let input = r#"{"kind":"name_str","idx":0,"prefix":99,"name":"bad"}"#;
        let err = parse_ndjson(input).unwrap_err();
        assert!(matches!(err, ParseError::InvalidNameIndex(99)));
    }

    #[test]
    fn parse_invalid_json() {
        let input = "not json at all\n";
        let err = parse_ndjson(input).unwrap_err();
        assert!(matches!(err, ParseError::Json { line: 1, .. }));
    }

    #[test]
    fn parse_empty_input() {
        let env = parse_ndjson("").unwrap();
        assert!(env.decls.is_empty());
    }

    #[test]
    fn parse_blank_lines() {
        let input = "\n\n\n";
        let env = parse_ndjson(input).unwrap();
        assert!(env.decls.is_empty());
    }

    #[test]
    fn parse_inductive() {
        let input = r#"{"kind":"name_anon","idx":0}
{"kind":"name_str","idx":1,"prefix":0,"name":"Bool"}
{"kind":"name_str","idx":2,"prefix":1,"name":"true"}
{"kind":"name_str","idx":3,"prefix":1,"name":"false"}
{"kind":"level_zero","idx":0}
{"kind":"level_succ","idx":1,"pred":0}
{"kind":"expr_sort","idx":0,"level":1}
{"kind":"expr_const","idx":1,"name":1,"levels":[]}
{"kind":"inductive","name":1,"level_params":[],"type":0,"num_params":0,"num_indices":0,"all":[1],"ctors":[2,3],"is_recursive":false,"is_reflexive":false,"is_nested":false,"is_unsafe":false}
{"kind":"constructor","name":2,"level_params":[],"type":1,"induct":1,"cidx":0,"num_params":0,"num_fields":0,"is_unsafe":false}
{"kind":"constructor","name":3,"level_params":[],"type":1,"induct":1,"cidx":1,"num_params":0,"num_fields":0,"is_unsafe":false}
"#;
        let env = parse_ndjson(input).unwrap();
        assert_eq!(env.decls.len(), 3);

        match &env.decls[0] {
            Decl::Induct(info) => {
                assert_eq!(info.name.to_string(), "Bool");
                assert_eq!(info.ctors.len(), 2);
                assert_eq!(info.ctors[0].to_string(), "Bool.true");
                assert_eq!(info.ctors[1].to_string(), "Bool.false");
                assert!(!info.is_recursive);
            }
            _ => panic!("expected Induct"),
        }

        match &env.decls[1] {
            Decl::Ctor(info) => {
                assert_eq!(info.name.to_string(), "Bool.true");
                assert_eq!(info.induct.to_string(), "Bool");
                assert_eq!(info.cidx, 0);
            }
            _ => panic!("expected Ctor"),
        }
    }
}
