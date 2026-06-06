//! Egglog-source → [`ast::Command`] parser.
//!
//! Thin wrapper over [`covalence_sexp::parse_egglog`]. Each top-level
//! S-expression is dispatched by its head symbol to a per-command parser.
//! Anything unrecognised surfaces as
//! [`BridgeError::Malformed`](crate::BridgeError::Malformed) — we don't yet
//! parse the full egglog command set, so loud failure on unknown heads
//! is intentional.

use covalence_sexp::{SExp, SExpr};

use crate::ast::{Command, Expr};
use crate::error::BridgeError;

/// Parse an egglog source string into a [`Vec<Command>`].
pub fn parse_program(input: &str) -> Result<Vec<Command>, BridgeError> {
    let sexps = covalence_sexp::parse_egglog(input)
        .map_err(|e| BridgeError::Malformed(format!("egglog parse: {e}")))?;
    sexps.iter().map(parse_command).collect()
}

fn parse_command(sexp: &SExpr) -> Result<Command, BridgeError> {
    let items = sexp
        .as_list()
        .ok_or_else(|| BridgeError::Malformed("command: expected list".into()))?;
    let (head, tail) = items
        .split_first()
        .ok_or_else(|| BridgeError::Malformed("command: empty list".into()))?;
    let head_sym = head
        .as_symbol()
        .ok_or_else(|| BridgeError::Malformed("command: non-symbol head".into()))?;

    match head_sym {
        "sort" => parse_sort(tail),
        "constructor" => parse_constructor(tail),
        "datatype" => parse_datatype(tail),
        "union" => parse_union(tail),
        "prove" => parse_prove(tail),
        other => Err(BridgeError::Malformed(format!(
            "unsupported egglog command: `{other}` — covalence-egglog only \
             parses sort/constructor/datatype/union/prove so far"
        ))),
    }
}

fn parse_sort(tail: &[SExpr]) -> Result<Command, BridgeError> {
    let [name] = tail else {
        return Err(BridgeError::Malformed(
            "(sort Name): expected one name".into(),
        ));
    };
    let name = name
        .as_symbol()
        .ok_or_else(|| BridgeError::Malformed("(sort …): expected symbol".into()))?;
    Ok(Command::Sort(name.to_string()))
}

fn parse_constructor(tail: &[SExpr]) -> Result<Command, BridgeError> {
    let [name, params, result] = tail else {
        return Err(BridgeError::Malformed(
            "(constructor name (params) result): expected three forms".into(),
        ));
    };
    let name = name
        .as_symbol()
        .ok_or_else(|| BridgeError::Malformed("(constructor …): expected symbol name".into()))?;
    let params = params.as_list().ok_or_else(|| {
        BridgeError::Malformed("(constructor …): expected list of param sorts".into())
    })?;
    let result = result.as_symbol().ok_or_else(|| {
        BridgeError::Malformed("(constructor …): expected symbol result sort".into())
    })?;
    let param_names = params
        .iter()
        .map(|p| {
            p.as_symbol()
                .map(str::to_string)
                .ok_or_else(|| BridgeError::Malformed("constructor param: expected symbol".into()))
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(Command::Constructor {
        name: name.to_string(),
        params: param_names,
        result: result.to_string(),
    })
}

fn parse_datatype(tail: &[SExpr]) -> Result<Command, BridgeError> {
    let (name, ctor_forms) = tail
        .split_first()
        .ok_or_else(|| BridgeError::Malformed("(datatype Name …): missing name".into()))?;
    let name = name
        .as_symbol()
        .ok_or_else(|| BridgeError::Malformed("(datatype …): expected symbol name".into()))?;
    let mut ctors = Vec::with_capacity(ctor_forms.len());
    for form in ctor_forms {
        let items = form.as_list().ok_or_else(|| {
            BridgeError::Malformed("(datatype …): expected (Ctor A …) lists".into())
        })?;
        let (ctor_name, ctor_params) = items
            .split_first()
            .ok_or_else(|| BridgeError::Malformed("datatype variant: empty list".into()))?;
        let ctor_name = ctor_name.as_symbol().ok_or_else(|| {
            BridgeError::Malformed("datatype variant: expected symbol head".into())
        })?;
        let param_names = ctor_params
            .iter()
            .map(|p| {
                p.as_symbol().map(str::to_string).ok_or_else(|| {
                    BridgeError::Malformed("datatype variant param: expected symbol".into())
                })
            })
            .collect::<Result<Vec<_>, _>>()?;
        ctors.push((ctor_name.to_string(), param_names));
    }
    Ok(Command::Datatype {
        name: name.to_string(),
        ctors,
    })
}

fn parse_union(tail: &[SExpr]) -> Result<Command, BridgeError> {
    let [lhs, rhs] = tail else {
        return Err(BridgeError::Malformed(
            "(union lhs rhs): expected two operands".into(),
        ));
    };
    Ok(Command::Union(parse_expr(lhs)?, parse_expr(rhs)?))
}

fn parse_prove(tail: &[SExpr]) -> Result<Command, BridgeError> {
    let [eq] = tail else {
        return Err(BridgeError::Malformed(
            "(prove (= lhs rhs)): expected one argument".into(),
        ));
    };
    let items = eq.as_list().ok_or_else(|| {
        BridgeError::Malformed("(prove …): body must be an equality form".into())
    })?;
    match items {
        [head, lhs, rhs] if head.as_symbol() == Some("=") => {
            Ok(Command::Prove(parse_expr(lhs)?, parse_expr(rhs)?))
        }
        _ => Err(BridgeError::Malformed(
            "(prove …): expected (= lhs rhs)".into(),
        )),
    }
}

fn parse_expr(sexp: &SExpr) -> Result<Expr, BridgeError> {
    match sexp {
        SExp::Atom(_) => {
            let sym = sexp
                .as_symbol()
                .ok_or_else(|| BridgeError::Malformed("expr: non-symbol atom".into()))?;
            Ok(Expr::Sym(sym.to_string()))
        }
        SExp::List(items) => {
            let (head, args) = items
                .split_first()
                .ok_or_else(|| BridgeError::Malformed("expr: empty application".into()))?;
            let head_sym = head
                .as_symbol()
                .ok_or_else(|| BridgeError::Malformed("expr: non-symbol head".into()))?;
            let arg_exprs = args.iter().map(parse_expr).collect::<Result<Vec<_>, _>>()?;
            Ok(Expr::App(head_sym.to_string(), arg_exprs))
        }
    }
}
