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
                    "store" => self.cmd_store(args),
                    "store-url" => self.cmd_store_url(args),
                    "store-file" => self.cmd_store_file(args),
                    "read" => self.cmd_read(args),
                    "read-wat" => self.cmd_read_wat(args),
                    "component" => self.cmd_wat("component", args),
                    "module" => self.cmd_wat("module", args),
                    "parse-module" => self.cmd_parse_module(args),
                    "parse-component" => self.cmd_parse_component(args),
                    "check-prop" => self.cmd_check_prop(args),
                    "list" => self.cmd_list(args),
                    "help" => Ok(Self::cmd_help()),
                    _ => Err(format!("unknown command: {cmd}")),
                }
            }
            SExp::Atom(s) if s == "help" => Ok(Self::cmd_help()),
            SExp::Atom(s) if s == "list" => self.cmd_list(&[]),
            _ => Err("expected a command like (help) or (component ...)".into()),
        }
    }

    fn cmd_store(&mut self, args: &[SExp]) -> Result<String, String> {
        if args.len() != 1 {
            return Err("usage: (store \"data\")".into());
        }
        let data = match &args[0] {
            SExp::String(s) => s.as_bytes().to_vec(),
            _ => return Err("store expects a string argument".into()),
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

    fn cmd_store_url(&mut self, args: &[SExp]) -> Result<String, String> {
        if args.len() != 1 {
            return Err("usage: (store-url \"https://...\")".into());
        }
        let url = match &args[0] {
            SExp::String(s) => s.as_str(),
            _ => return Err("store-url expects a string argument".into()),
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

    fn cmd_store_file(&mut self, args: &[SExp]) -> Result<String, String> {
        if !self.allow_fs {
            return Err("store-file is only available in CLI mode".into());
        }
        if args.len() != 1 {
            return Err("usage: (store-file \"path/to/file\")".into());
        }
        let path = match &args[0] {
            SExp::String(s) => s.as_str(),
            _ => return Err("store-file expects a string argument".into()),
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

    fn cmd_read(&self, args: &[SExp]) -> Result<String, String> {
        let hash = self.require_hash_arg(args, "read")?;
        let data = self
            .store
            .get(&hash)
            .ok_or_else(|| format!("blob not found: {hash}"))?;
        String::from_utf8(data.to_vec()).map_err(|e| format!("blob is not valid UTF-8: {e}"))
    }

    fn cmd_read_wat(&self, args: &[SExp]) -> Result<String, String> {
        let hash = self.require_hash_arg(args, "read-wat")?;
        let data = self
            .store
            .get(&hash)
            .ok_or_else(|| format!("blob not found: {hash}"))?;
        wasmprinter::print_bytes(data).map_err(|e| format!("not a valid WASM module/component: {e}"))
    }

    fn cmd_list(&self, _args: &[SExp]) -> Result<String, String> {
        let hashes = self.store.hashes();
        if hashes.is_empty() {
            return Ok("(empty)".into());
        }
        let lines: Vec<String> = hashes.iter().map(|h| h.to_string()).collect();
        Ok(lines.join("\n"))
    }

    fn cmd_help() -> String {
        "\
(store \"data\")            store string as blob, return hash
(store-url \"url\")         fetch URL as blob, return hash
(store-file \"path\")       store file as blob, return hash (CLI only)
(read <hash>)              read blob as text
(read-wat <hash>)          read blob as WAT (error if not valid WASM)
(component ...)            compile WAT component, store as blob
(module ...)               compile WAT module, store as blob
(parse-module <hash>)      validate blob as WASM module
(parse-component <hash>)   validate blob as WASM component
(check-prop <hash>)        check if prop calls attest() on startup
(list)                     list all blob hashes
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
