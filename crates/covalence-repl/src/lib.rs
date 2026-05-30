pub use covalence_kernel::{BackendInfo, KernelError, SyncBackend};

use covalence_forsp::{FCtx, FError, ForeignPrims, Forsp};
use covalence_hash::O256;

/// Foreign primitives for the REPL: storage, WASM, and I/O commands.
struct ReplPrims {
    backend: Box<dyn SyncBackend>,
    allow_fs: bool,
    allow_fetch: bool,
    output: String,
}

impl ForeignPrims for ReplPrims {
    fn call(&mut self, name: &str, ctx: &mut FCtx<'_>) -> Result<bool, FError> {
        let result = match name {
            "print" => self.cmd_print(ctx),
            "store" => self.cmd_store(ctx),
            "read" => self.cmd_read(ctx),
            "read-wat" => self.cmd_read_wat(ctx),
            "store-url" => self.cmd_store_url(ctx),
            "store-file" => self.cmd_store_file(ctx),
            "decide" => self.cmd_decide(ctx),
            "prove" => self.cmd_prove(ctx),
            "parse-module" => self.cmd_parse_module(ctx),
            "parse-component" => self.cmd_parse_component(ctx),
            "compile-wat" => self.cmd_compile_wat(ctx),
            "status" => self.cmd_status(ctx),
            "help" => self.cmd_help(ctx),
            "hash" => self.cmd_hash(ctx),
            _ => return Ok(false),
        };
        result.map(|()| true)
    }
}

impl ReplPrims {
    fn emit(&mut self, s: &str) {
        self.output.push_str(s);
        self.output.push('\n');
    }

    fn backend_err(e: KernelError) -> FError {
        FError::Parse(e.to_string())
    }

    // --- commands ---

    /// `print`: val → (appends formatted val to output)
    fn cmd_print(&mut self, ctx: &mut FCtx<'_>) -> Result<(), FError> {
        let val = ctx.try_pop()?;
        let s = ctx.show(val);
        self.emit(&s);
        Ok(())
    }

    /// `store`: blob → hash
    fn cmd_store(&mut self, ctx: &mut FCtx<'_>) -> Result<(), FError> {
        let data = ctx.try_pop_blob()?;
        let hash = self.backend.store_blob(&data).map_err(Self::backend_err)?;
        ctx.push_hash(hash);
        Ok(())
    }

    /// `read`: hash → blob
    fn cmd_read(&mut self, ctx: &mut FCtx<'_>) -> Result<(), FError> {
        let hash = ctx.try_pop_hash()?;
        let data = self
            .backend
            .get_blob(&hash)
            .map_err(Self::backend_err)?
            .ok_or_else(|| FError::Parse(format!("blob not found: {hash}")))?;
        ctx.push_blob(data);
        Ok(())
    }

    /// `read-wat`: hash → blob (decompiled WAT text)
    fn cmd_read_wat(&mut self, ctx: &mut FCtx<'_>) -> Result<(), FError> {
        let hash = ctx.try_pop_hash()?;
        let data = self
            .backend
            .get_blob(&hash)
            .map_err(Self::backend_err)?
            .ok_or_else(|| FError::Parse(format!("blob not found: {hash}")))?;
        let wat = covalence_wasm::wasm_to_wat(&data).map_err(|e| FError::Parse(e.to_string()))?;
        ctx.push_blob(wat.into_bytes());
        Ok(())
    }

    /// `store-url`: blob → hash (blob contains URL string)
    fn cmd_store_url(&mut self, ctx: &mut FCtx<'_>) -> Result<(), FError> {
        if !self.allow_fetch {
            return Err(FError::Parse(
                "store-url is not available in this mode".into(),
            ));
        }
        let url_bytes = ctx.try_pop_blob()?;
        let _url = std::str::from_utf8(&url_bytes)
            .map_err(|e| FError::Parse(format!("URL is not valid UTF-8: {e}")))?;
        #[cfg(feature = "fetch")]
        {
            let body = ureq::get(_url)
                .call()
                .map_err(|e| FError::Parse(format!("fetch error: {e}")))?
                .into_body()
                .read_to_vec()
                .map_err(|e| FError::Parse(format!("read error: {e}")))?;
            let hash = self.backend.store_blob(&body).map_err(Self::backend_err)?;
            ctx.push_hash(hash);
        }
        #[cfg(not(feature = "fetch"))]
        return Err(FError::Parse(
            "store-url requires the 'fetch' feature".into(),
        ));
        #[cfg(feature = "fetch")]
        Ok(())
    }

    /// `store-file`: blob → hash (blob contains file path)
    fn cmd_store_file(&mut self, ctx: &mut FCtx<'_>) -> Result<(), FError> {
        if !self.allow_fs {
            return Err(FError::Parse(
                "store-file is only available in CLI mode".into(),
            ));
        }
        let path_bytes = ctx.try_pop_blob()?;
        let path = std::str::from_utf8(&path_bytes)
            .map_err(|e| FError::Parse(format!("path is not valid UTF-8: {e}")))?;
        let data = std::fs::read(path).map_err(|e| FError::Parse(format!("read error: {e}")))?;
        let hash = self.backend.store_blob(&data).map_err(Self::backend_err)?;
        ctx.push_hash(hash);
        Ok(())
    }

    /// `decide`: hash → (prints decision + proved hashes)
    fn cmd_decide(&mut self, ctx: &mut FCtx<'_>) -> Result<(), FError> {
        let hash = ctx.try_pop_hash()?;
        let output = self.backend.decide(&hash).map_err(Self::backend_err)?;
        for proved_hash in &output.proved {
            self.emit(&format!("{proved_hash} true"));
        }
        self.emit(&format!("{hash} {}", output.decision));
        Ok(())
    }

    /// `prove`: hash → (decide + add self to proved set)
    fn cmd_prove(&mut self, ctx: &mut FCtx<'_>) -> Result<(), FError> {
        let hash = ctx.try_pop_hash()?;
        let mut output = self.backend.decide(&hash).map_err(Self::backend_err)?;
        if output.decision == covalence_kernel::Decision::Sat && !output.proved.contains(&hash) {
            output.proved.push(hash);
        }
        for proved_hash in &output.proved {
            self.emit(&format!("{proved_hash} true"));
        }
        self.emit(&format!("{hash} {}", output.decision));
        Ok(())
    }

    /// `parse-module`: hash → (prints module imports/exports)
    fn cmd_parse_module(&mut self, ctx: &mut FCtx<'_>) -> Result<(), FError> {
        let hash = ctx.try_pop_hash()?;
        let data = self
            .backend
            .get_blob(&hash)
            .map_err(Self::backend_err)?
            .ok_or_else(|| FError::Parse(format!("blob not found: {hash}")))?;
        let info = covalence_wasm::parse_module(&data).map_err(|e| FError::Parse(e.to_string()))?;
        self.emit(&info.to_string());
        Ok(())
    }

    /// `parse-component`: hash → (prints component imports/exports)
    fn cmd_parse_component(&mut self, ctx: &mut FCtx<'_>) -> Result<(), FError> {
        let hash = ctx.try_pop_hash()?;
        let data = self
            .backend
            .get_blob(&hash)
            .map_err(Self::backend_err)?
            .ok_or_else(|| FError::Parse(format!("blob not found: {hash}")))?;
        let info =
            covalence_wasm::parse_component(&data).map_err(|e| FError::Parse(e.to_string()))?;
        self.emit(&info.to_string());
        Ok(())
    }

    /// `compile-wat`: blob → hash (compile WAT source to WASM, store)
    fn cmd_compile_wat(&mut self, ctx: &mut FCtx<'_>) -> Result<(), FError> {
        let wat_bytes = ctx.try_pop_blob()?;
        let wat_str = std::str::from_utf8(&wat_bytes)
            .map_err(|e| FError::Parse(format!("WAT source is not valid UTF-8: {e}")))?;
        let wasm =
            covalence_wasm::compile_wat(wat_str).map_err(|e| FError::Parse(e.to_string()))?;
        let hash = self.backend.store_blob(&wasm).map_err(Self::backend_err)?;
        ctx.push_hash(hash);
        Ok(())
    }

    /// `status`: → (prints backend info)
    fn cmd_status(&mut self, _ctx: &mut FCtx<'_>) -> Result<(), FError> {
        let info = self.backend.info();
        let count = self.backend.blob_count().ok().flatten();
        match count {
            Some(n) => self.emit(&format!(
                "backend: {} ({})\nblobs:   {n}",
                info.kind, info.target
            )),
            None => self.emit(&format!("backend: {} ({})", info.kind, info.target)),
        }
        Ok(())
    }

    /// `help`: → (prints available commands)
    fn cmd_help(&mut self, _ctx: &mut FCtx<'_>) -> Result<(), FError> {
        const COMMANDS: &[(&str, &str)] = &[
            ("\"data\" store", "store blob, push hash"),
            ("\"url\" store-url", "fetch URL, store as blob"),
            ("\"path\" store-file", "store file as blob (CLI only)"),
            ("<hash> read", "read blob by hash"),
            ("<hash> read-wat", "decompile WASM to WAT"),
            ("\"(module ...)\" compile-wat", "compile WAT to WASM, store"),
            ("<hash> parse-module", "inspect module imports/exports"),
            (
                "<hash> parse-component",
                "inspect component imports/exports",
            ),
            ("<hash> decide", "decide proposition"),
            ("<hash> prove", "prove container (decide + add self)"),
            ("\"data\" hash", "hash blob (BLAKE3) without storing"),
            ("<val> print", "print a value"),
            ("status", "show backend info"),
            ("help", "show this help"),
            ("3 4 +", "arithmetic: + - *"),
            ("42 $x ^x", "variable binding and recall"),
            ("($x ^x 1 +) $inc", "define a closure"),
        ];
        let width = COMMANDS.iter().map(|(cmd, _)| cmd.len()).max().unwrap_or(0);
        let help = COMMANDS
            .iter()
            .map(|(cmd, desc)| format!("{cmd:<width$}  {desc}"))
            .collect::<Vec<_>>()
            .join("\n");
        self.emit(&help);
        Ok(())
    }

    /// `hash`: blob → hash (BLAKE3 hash without storing)
    fn cmd_hash(&mut self, ctx: &mut FCtx<'_>) -> Result<(), FError> {
        let data = ctx.try_pop_blob()?;
        let hash = O256::blob(&data);
        ctx.push_hash(hash);
        Ok(())
    }
}

/// A REPL session backed by a Forsp interpreter.
pub struct Session {
    forsp: Forsp<ReplPrims>,
}

impl Session {
    /// Create a new session with the given backend.
    pub fn new(backend: Box<dyn SyncBackend>, allow_fs: bool, allow_fetch: bool) -> Self {
        let prims = ReplPrims {
            backend,
            allow_fs,
            allow_fetch,
            output: String::new(),
        };
        Session {
            forsp: Forsp::new_with(prims),
        }
    }

    /// Evaluate a line of input.
    /// Returns the result as a displayable string.
    pub fn eval(&mut self, input: &str) -> String {
        self.forsp.foreign.output.clear();

        match self.forsp.run(input) {
            Ok(()) => {
                let output = std::mem::take(&mut self.forsp.foreign.output);
                if !output.is_empty() {
                    output.trim_end().to_string()
                } else if !self.forsp.stack.is_nil() {
                    let top = self.forsp.try_peek().unwrap();
                    self.forsp.show(top)
                } else {
                    String::new()
                }
            }
            Err(e) => format!("error: {e}"),
        }
    }
}
