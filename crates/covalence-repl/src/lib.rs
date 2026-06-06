pub use covalence_shell::{BackendInfo, KernelError, SyncBackend};

use covalence_forsp::{FCtx, FError, ForeignPrims, Forsp};
use covalence_hash::O256;

#[cfg(feature = "parquet")]
mod parquet_tree;

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
            "compile-wat" => self.cmd_compile_wat(ctx),
            "status" => self.cmd_status(ctx),
            "help" => self.cmd_help(ctx),
            "hash" => self.cmd_hash(ctx),
            #[cfg(feature = "arrow")]
            "arrow-stats" => self.cmd_arrow_stats(ctx),
            #[cfg(feature = "parquet")]
            "parquet-stats" => self.cmd_parquet_stats(ctx),
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
        #[allow(unused_mut)]
        let mut commands: Vec<(&str, &str)> = vec![
            ("\"data\" store", "store blob, push hash"),
            ("\"url\" store-url", "fetch URL, store as blob"),
            ("\"path\" store-file", "store file as blob (CLI only)"),
            ("<hash> read", "read blob by hash"),
            ("<hash> read-wat", "decompile WASM to WAT"),
            ("\"(module ...)\" compile-wat", "compile WAT to WASM, store"),
            ("\"data\" hash", "hash blob (BLAKE3) without storing"),
            ("<val> print", "print a value"),
            ("status", "show backend info"),
            ("help", "show this help"),
            ("3 4 +", "arithmetic: + - *"),
            ("42 $x ^x", "variable binding and recall"),
            ("($x ^x 1 +) $inc", "define a closure"),
        ];
        #[cfg(feature = "arrow")]
        commands.push(("<hash> arrow-stats", "parse blob as Arrow IPC, print stats"));
        #[cfg(feature = "parquet")]
        commands.push((
            "<hash> parquet-stats",
            "parse blob as Parquet (auto-detects hive-partitioned tree)",
        ));
        let width = commands.iter().map(|(cmd, _)| cmd.len()).max().unwrap_or(0);
        let help = commands
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

    /// Fetch a blob by hash or fail with a parse error.
    #[cfg(any(feature = "arrow", feature = "parquet"))]
    fn fetch_blob(&self, hash: &O256) -> Result<Vec<u8>, FError> {
        self.backend
            .get_blob(hash)
            .map_err(Self::backend_err)?
            .ok_or_else(|| FError::Parse(format!("blob not found: {hash}")))
    }

    /// `arrow-stats`: hash → (prints Arrow IPC stats)
    #[cfg(feature = "arrow")]
    fn cmd_arrow_stats(&mut self, ctx: &mut FCtx<'_>) -> Result<(), FError> {
        let hash = ctx.try_pop_hash()?;
        let data = self.fetch_blob(&hash)?;
        let info = covalence_arrow::parse_ipc(&data).map_err(|e| FError::Parse(e.to_string()))?;
        self.emit(info.to_string().trim_end());
        Ok(())
    }

    /// `parquet-stats`: hash → (prints Parquet stats; if the hash is a tree,
    /// scans it as a hive-partitioned dataset, otherwise parses as a file)
    #[cfg(feature = "parquet")]
    fn cmd_parquet_stats(&mut self, ctx: &mut FCtx<'_>) -> Result<(), FError> {
        let hash = ctx.try_pop_hash()?;
        let is_tree = self.backend.is_tree(&hash).map_err(Self::backend_err)?;
        let info = if is_tree {
            let mut source = parquet_tree::BackendHiveSource::new(self.backend.as_ref(), hash);
            covalence_parquet::scan_hive(&mut source).map_err(|e| FError::Parse(e.to_string()))?
        } else {
            let data = self.fetch_blob(&hash)?;
            covalence_parquet::parse_file(&data).map_err(|e| FError::Parse(e.to_string()))?
        };
        self.emit(info.to_string().trim_end());
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
