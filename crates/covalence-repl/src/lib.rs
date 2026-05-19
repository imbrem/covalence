pub use covalence_kernel::{BackendInfo, KernelError, SyncBackend};

use covalence_hash::O256;
use covalence_sexp::SExp;

/// A REPL session that evaluates S-expression commands locally,
/// delegating storage and WASM execution to a SyncBackend.
pub struct Session {
    backend: Box<dyn SyncBackend>,
    /// Whether filesystem access is allowed (CLI only, not web).
    allow_fs: bool,
    /// Whether URL fetching is allowed.
    allow_fetch: bool,
}

impl Session {
    /// Create a new session with the given backend.
    pub fn new(backend: Box<dyn SyncBackend>, allow_fs: bool, allow_fetch: bool) -> Self {
        Session {
            backend,
            allow_fs,
            allow_fetch,
        }
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
                    "decide" => self.cmd_decide(args),
                    "status" => Ok(self.cmd_status()),
                    "help" => Ok(Self::cmd_help()),
                    _ => Err(format!("unknown command: {cmd}")),
                }
            }
            SExp::Atom(s) if s == "help" => Ok(Self::cmd_help()),
            SExp::Atom(s) if s == "status" => Ok(self.cmd_status()),
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
        let hash = self.backend.store_blob(&data).map_err(|e| e.to_string())?;
        Ok(hash.to_string())
    }

    fn cmd_wat(&mut self, keyword: &str, args: &[SExp]) -> Result<String, String> {
        let mut wat = format!("({keyword}");
        for arg in args {
            wat.push(' ');
            sexp_to_wat(arg, &mut wat);
        }
        wat.push(')');
        let wasm = covalence_wasm::compile_wat(&wat).map_err(|e| e.to_string())?;
        let hash = self.backend.store_blob(&wasm).map_err(|e| e.to_string())?;
        Ok(hash.to_string())
    }

    fn cmd_store_url(&mut self, args: &[SExp]) -> Result<String, String> {
        if !self.allow_fetch {
            return Err("store-url is not available in this mode".into());
        }
        if args.len() != 1 {
            return Err("usage: (store-url \"https://...\")".into());
        }
        let _url = match &args[0] {
            SExp::String(s) => s.as_str(),
            _ => return Err("store-url expects a string argument".into()),
        };
        #[cfg(feature = "fetch")]
        {
            let body = ureq::get(_url)
                .call()
                .map_err(|e| format!("fetch error: {e}"))?
                .into_body()
                .read_to_vec()
                .map_err(|e| format!("read error: {e}"))?;
            let hash = self.backend.store_blob(&body).map_err(|e| e.to_string())?;
            Ok(hash.to_string())
        }
        #[cfg(not(feature = "fetch"))]
        {
            Err("store-url requires the 'fetch' feature".into())
        }
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
        let hash = self.backend.store_blob(&data).map_err(|e| e.to_string())?;
        Ok(hash.to_string())
    }

    fn cmd_parse_module(&self, args: &[SExp]) -> Result<String, String> {
        let hash = self.require_hash_arg(args, "parse-module")?;
        let data = self
            .backend
            .get_blob(&hash)
            .map_err(|e| e.to_string())?
            .ok_or_else(|| format!("blob not found: {hash}"))?;
        covalence_wasm::parse_module(&data)
            .map(|info| info.to_string())
            .map_err(|e| e.to_string())
    }

    fn cmd_parse_component(&self, args: &[SExp]) -> Result<String, String> {
        let hash = self.require_hash_arg(args, "parse-component")?;
        let data = self
            .backend
            .get_blob(&hash)
            .map_err(|e| e.to_string())?
            .ok_or_else(|| format!("blob not found: {hash}"))?;
        covalence_wasm::parse_component(&data)
            .map(|info| info.to_string())
            .map_err(|e| e.to_string())
    }

    fn cmd_decide(&self, args: &[SExp]) -> Result<String, String> {
        let hash = self.require_hash_arg(args, "decide")?;
        self.backend
            .decide(&hash)
            .map(|d| d.to_string())
            .map_err(|e| e.to_string())
    }

    fn cmd_read(&self, args: &[SExp]) -> Result<String, String> {
        let hash = self.require_hash_arg(args, "read")?;
        let data = self
            .backend
            .get_blob(&hash)
            .map_err(|e| e.to_string())?
            .ok_or_else(|| format!("blob not found: {hash}"))?;
        String::from_utf8(data).map_err(|e| format!("blob is not valid UTF-8: {e}"))
    }

    fn cmd_read_wat(&self, args: &[SExp]) -> Result<String, String> {
        let hash = self.require_hash_arg(args, "read-wat")?;
        let data = self
            .backend
            .get_blob(&hash)
            .map_err(|e| e.to_string())?
            .ok_or_else(|| format!("blob not found: {hash}"))?;
        covalence_wasm::wasm_to_wat(&data).map_err(|e| e.to_string())
    }

    fn cmd_status(&self) -> String {
        let info = self.backend.info();
        let count = self.backend.blob_count().ok().flatten();
        match count {
            Some(n) => format!("backend: {} ({})\nblobs:   {n}", info.kind, info.target),
            None => format!("backend: {} ({})", info.kind, info.target),
        }
    }

    fn cmd_help() -> String {
        const COMMANDS: &[(&str, &str)] = &[
            ("(store \"data\")", "store string as blob, return hash"),
            ("(store-url \"url\")", "fetch URL, store as blob"),
            ("(store-file \"path\")", "store file as blob (CLI only)"),
            ("(read <hash>)", "read blob as UTF-8 text"),
            ("(read-wat <hash>)", "decompile blob as WAT"),
            ("(module ...)", "compile WAT module, store as blob"),
            ("(component ...)", "compile WAT component, store as blob"),
            (
                "(parse-module <hash>)",
                "inspect WASM module imports/exports",
            ),
            (
                "(parse-component <hash>)",
                "inspect WASM component imports/exports",
            ),
            ("(decide <hash>)", "decide if proposition is true"),
            ("(status)", "show backend connection info"),
            ("(help)", "show this help"),
        ];
        let width = COMMANDS.iter().map(|(cmd, _)| cmd.len()).max().unwrap_or(0);
        COMMANDS
            .iter()
            .map(|(cmd, desc)| format!("{cmd:<width$}  {desc}"))
            .collect::<Vec<_>>()
            .join("\n")
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
