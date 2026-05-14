use covalence_object::O256;
use covalence_sexp::SExp;
use covalence_wasm::WasmEngine;

use crate::blob_store::BlobStore;

/// A REPL session with its own blob store and WASM engine.
pub struct Session {
    store: BlobStore,
    engine: WasmEngine,
    /// Whether filesystem access is allowed (CLI only, not web).
    allow_fs: bool,
}

impl Session {
    pub fn new(allow_fs: bool) -> Result<Self, String> {
        let engine = WasmEngine::new().map_err(|e| format!("failed to create WASM engine: {e}"))?;
        Ok(Session {
            store: BlobStore::new(),
            engine,
            allow_fs,
        })
    }

    /// Evaluate a line of input (one or more S-expressions).
    /// Returns the result as a displayable string.
    pub fn eval(&mut self, input: &str) -> String {
        let sexps = match covalence_sexp::parse(input) {
            Ok(sexps) => sexps,
            Err(e) => return format!("parse error: {e}"),
        };
        if sexps.is_empty() {
            return String::new();
        }
        let mut results = Vec::new();
        for sexp in &sexps {
            match self.eval_sexp(sexp) {
                Ok(s) => results.push(s),
                Err(e) => results.push(format!("error: {e}")),
            }
        }
        results.join("\n")
    }

    /// Evaluate a single S-expression command.
    pub fn eval_sexp(&mut self, sexp: &SExp) -> Result<String, String> {
        match sexp {
            SExp::List(items) if !items.is_empty() => {
                let cmd = match &items[0] {
                    SExp::Atom(s) => s.as_str(),
                    _ => return Err("command must be an atom".into()),
                };
                let args = &items[1..];
                match cmd {
                    "load" => self.cmd_load(args),
                    "load-url" => self.cmd_load_url(args),
                    "load-file" => self.cmd_load_file(args),
                    "component" => self.cmd_wat("component", args),
                    "module" => self.cmd_wat("module", args),
                    "parse-module" => self.cmd_parse_module(args),
                    "parse-component" => self.cmd_parse_component(args),
                    "check-prop" => self.cmd_check_prop(args),
                    "store" => self.cmd_store(args),
                    "help" => Ok(Self::cmd_help()),
                    _ => Err(format!("unknown command: {cmd}")),
                }
            }
            SExp::Atom(s) if s == "help" => Ok(Self::cmd_help()),
            SExp::Atom(s) if s == "store" => self.cmd_store(&[]),
            _ => Err("expected a command like (help) or (component ...)".into()),
        }
    }

    fn cmd_load(&mut self, args: &[SExp]) -> Result<String, String> {
        if args.len() != 1 {
            return Err("usage: (load \"data\")".into());
        }
        let data = match &args[0] {
            SExp::String(s) => s.as_bytes().to_vec(),
            _ => return Err("load expects a string argument".into()),
        };
        let hash = self.store.insert(data);
        Ok(hash.to_string())
    }

    fn cmd_wat(&mut self, keyword: &str, args: &[SExp]) -> Result<String, String> {
        let mut wat = format!("({keyword}");
        for arg in args {
            wat.push(' ');
            sexp_to_wat(arg, &mut wat);
        }
        wat.push(')');
        let wasm = wat::parse_str(&wat).map_err(|e| format!("{e}"))?;
        let hash = self.store.insert(wasm);
        Ok(hash.to_string())
    }

    fn cmd_load_url(&mut self, args: &[SExp]) -> Result<String, String> {
        if args.len() != 1 {
            return Err("usage: (load-url \"https://...\")".into());
        }
        let url = match &args[0] {
            SExp::String(s) => s.as_str(),
            _ => return Err("load-url expects a string argument".into()),
        };
        let body = ureq::get(url)
            .call()
            .map_err(|e| format!("fetch error: {e}"))?
            .into_body()
            .read_to_vec()
            .map_err(|e| format!("read error: {e}"))?;
        let hash = self.store.insert(body);
        Ok(hash.to_string())
    }

    fn cmd_load_file(&mut self, args: &[SExp]) -> Result<String, String> {
        if !self.allow_fs {
            return Err("load-file is only available in CLI mode".into());
        }
        if args.len() != 1 {
            return Err("usage: (load-file \"path/to/file\")".into());
        }
        let path = match &args[0] {
            SExp::String(s) => s.as_str(),
            _ => return Err("load-file expects a string argument".into()),
        };
        let data = std::fs::read(path).map_err(|e| format!("read error: {e}"))?;
        let hash = self.store.insert(data);
        Ok(hash.to_string())
    }

    fn cmd_parse_module(&self, args: &[SExp]) -> Result<String, String> {
        let hash = self.require_hash_arg(args, "parse-module")?;
        let data = self
            .store
            .get(&hash)
            .ok_or_else(|| format!("blob not found: {hash}"))?;
        let info = self
            .engine
            .parse_module(data)
            .map_err(|e| format!("invalid module: {e}"))?;
        Ok(info.to_string())
    }

    fn cmd_parse_component(&self, args: &[SExp]) -> Result<String, String> {
        let hash = self.require_hash_arg(args, "parse-component")?;
        let data = self
            .store
            .get(&hash)
            .ok_or_else(|| format!("blob not found: {hash}"))?;
        let info = self
            .engine
            .parse_component(data)
            .map_err(|e| format!("invalid component: {e}"))?;
        Ok(info.to_string())
    }

    fn cmd_check_prop(&self, args: &[SExp]) -> Result<String, String> {
        let hash = self.require_hash_arg(args, "check-prop")?;
        let data = self
            .store
            .get(&hash)
            .ok_or_else(|| format!("blob not found: {hash}"))?;
        let result = self
            .engine
            .check_prop(data, &self.store)
            .map_err(|e| format!("{e}"))?;
        Ok(result.to_string())
    }

    fn cmd_store(&self, _args: &[SExp]) -> Result<String, String> {
        let hashes = self.store.hashes();
        if hashes.is_empty() {
            return Ok("(empty)".into());
        }
        let lines: Vec<String> = hashes.iter().map(|h| h.to_string()).collect();
        Ok(lines.join("\n"))
    }

    fn cmd_help() -> String {
        "\
(load \"data\")             load string as blob, return hash
(load-url \"url\")          fetch URL as blob, return hash
(load-file \"path\")        load file as blob, return hash (CLI only)
(component ...)            compile WAT component, store as blob
(module ...)               compile WAT module, store as blob
(parse-module <hash>)      validate blob as WASM module
(parse-component <hash>)   validate blob as WASM component
(check-prop <hash>)        check if prop calls attest() on startup
(store)                    list all blob hashes
(help)                     show this help"
            .into()
    }

    fn require_hash_arg(&self, args: &[SExp], cmd: &str) -> Result<O256, String> {
        if args.len() != 1 {
            return Err(format!("usage: ({cmd} <hash>)"));
        }
        let hex = match &args[0] {
            SExp::Atom(s) => s.as_str(),
            _ => return Err(format!("{cmd} expects a hash (64 hex chars)")),
        };
        O256::from_hex(hex).ok_or_else(|| format!("invalid hash: {hex}"))
    }
}

/// Serialize an SExp back to WAT-compatible text.
fn sexp_to_wat(sexp: &SExp, out: &mut String) {
    match sexp {
        SExp::Atom(s) => out.push_str(s),
        SExp::String(s) => {
            out.push('"');
            for ch in s.chars() {
                match ch {
                    '"' => out.push_str("\\\""),
                    '\\' => out.push_str("\\\\"),
                    _ => out.push(ch),
                }
            }
            out.push('"');
        }
        SExp::QuotedSymbol(s) => {
            out.push('|');
            out.push_str(s);
            out.push('|');
        }
        SExp::List(items) => {
            out.push('(');
            for (i, item) in items.iter().enumerate() {
                if i > 0 {
                    out.push(' ');
                }
                sexp_to_wat(item, out);
            }
            out.push(')');
        }
    }
}
