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
    /// Optional GitStore for the `git-*` commands. `git-open` populates it;
    /// every other `git-*` command errors with a clear "open a store first"
    /// message until it is set.
    #[cfg(feature = "cogit")]
    git_store: Option<covalence_git::store::GitStore>,
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
            #[cfg(feature = "cogit")]
            "git-open" => self.cmd_git_open(ctx),
            #[cfg(feature = "cogit")]
            "git-close" => self.cmd_git_close(ctx),
            #[cfg(feature = "cogit")]
            "git-info" => self.cmd_git_info(ctx),
            #[cfg(feature = "cogit")]
            "git-resolve" => self.cmd_git_resolve(ctx),
            #[cfg(feature = "cogit")]
            "git-reverse" => self.cmd_git_reverse(ctx),
            #[cfg(feature = "cogit")]
            "git-store-blob" => self.cmd_git_store_blob(ctx),
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
        #[cfg(feature = "cogit")]
        {
            commands.push(("\"path\" git-open", "open a GitStore (e.g. from cov cog clone)"));
            commands.push(("git-close", "drop the open GitStore handle"));
            commands.push(("git-info", "show counts for the open GitStore"));
            commands.push((
                "\"<oid-hex>\" git-resolve",
                "look up the O256 a git OID maps to",
            ));
            commands.push((
                "<O256> git-reverse",
                "find a git OID whose blob hashes to this O256",
            ));
            commands.push((
                "\"data\" git-store-blob",
                "register data as a git blob; push git OID",
            ));
        }
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

    // --- cogit (GitStore SHA1 → O256 map) commands ---

    /// Look up the current GitStore or error.
    #[cfg(feature = "cogit")]
    fn git_store(&self) -> Result<&covalence_git::store::GitStore, FError> {
        self.git_store
            .as_ref()
            .ok_or_else(|| FError::Parse("git store not open; use `\"path\" git-open` first".into()))
    }

    /// `git-open`: path-blob → (open SQLite GitStore at the given path)
    #[cfg(feature = "cogit")]
    fn cmd_git_open(&mut self, ctx: &mut FCtx<'_>) -> Result<(), FError> {
        let path_bytes = ctx.try_pop_blob()?;
        let path = std::str::from_utf8(&path_bytes)
            .map_err(|e| FError::Parse(format!("path is not valid UTF-8: {e}")))?;
        let store = covalence_git::store::GitStore::open(
            path,
            covalence_hash::gix_hash::Kind::Sha1,
        )
        .map_err(|e| FError::Parse(format!("open git store: {e}")))?;
        self.emit(&format!(
            "opened git store: {path} ({} object(s))",
            store.len()
        ));
        self.git_store = Some(store);
        Ok(())
    }

    /// `git-close`: → (drop the open GitStore handle)
    #[cfg(feature = "cogit")]
    fn cmd_git_close(&mut self, _ctx: &mut FCtx<'_>) -> Result<(), FError> {
        if self.git_store.take().is_some() {
            self.emit("closed git store");
        } else {
            self.emit("no git store was open");
        }
        Ok(())
    }

    /// `git-info`: → (prints count and covalence-tree count)
    #[cfg(feature = "cogit")]
    fn cmd_git_info(&mut self, _ctx: &mut FCtx<'_>) -> Result<(), FError> {
        let store = self.git_store()?;
        let total = store.len();
        let cov_trees = store.cov_tree_hashes().len();
        self.emit(&format!("git objects:    {total}"));
        self.emit(&format!("covalence trees: {cov_trees}"));
        Ok(())
    }

    /// `git-resolve`: oid-hex-blob → O256
    /// Look up the O256 a git OID maps to. Errors if the OID is unknown or
    /// only registered as a shallow placeholder (no data).
    #[cfg(feature = "cogit")]
    fn cmd_git_resolve(&mut self, ctx: &mut FCtx<'_>) -> Result<(), FError> {
        use covalence_git::store::GitBackend;
        let hex_bytes = ctx.try_pop_blob()?;
        let oid = parse_git_oid(&hex_bytes)?;
        let store = self.git_store()?;
        let obj = store.read_object(&oid).map_err(|e| {
            FError::Parse(format!("git OID {oid} not resolvable: {e}"))
        })?;
        // The store keys blobs by `O256::blob(data)`, which is exactly the
        // mapping cog clone established.
        ctx.push_hash(covalence_hash::O256::blob(&obj.data));
        Ok(())
    }

    /// `git-reverse`: O256 → oid-hex-blob
    /// Find a git OID whose data hashes to the given O256. If multiple git
    /// OIDs share the same blob hash (rare — typically only blob vs tree
    /// with identical payload), returns the lexicographically-smallest OID.
    #[cfg(feature = "cogit")]
    fn cmd_git_reverse(&mut self, ctx: &mut FCtx<'_>) -> Result<(), FError> {
        let target = ctx.try_pop_hash()?;
        let store = self.git_store()?;
        let oid = store.git_oid_for_blob_hash(&target).map_err(|e| {
            FError::Parse(format!("reverse lookup: {e}"))
        })?;
        match oid {
            Some(oid) => ctx.push_blob(oid.to_string().into_bytes()),
            None => return Err(FError::Parse(format!("no git OID maps to {target}"))),
        }
        Ok(())
    }

    /// `git-store-blob`: data-blob → oid-hex-blob
    /// Write `data` to the open GitStore as a git blob object. Registers both
    /// the SHA-1 OID and the implicit O256 (`O256::blob(data)`) mapping, so
    /// it becomes visible to `git-resolve` and `git-reverse`. Pushes the
    /// hex-encoded git OID.
    #[cfg(feature = "cogit")]
    fn cmd_git_store_blob(&mut self, ctx: &mut FCtx<'_>) -> Result<(), FError> {
        use covalence_git::store::{GitBackend, GitObjectKind};
        let data = ctx.try_pop_blob()?;
        let store = self.git_store()?;
        let oid = store
            .write_object(GitObjectKind::Blob, &data)
            .map_err(|e| FError::Parse(format!("write blob: {e}")))?;
        // Also push the corresponding O256 into the backend so the rest of
        // the REPL (`read`, `arrow-stats`, …) sees the same bytes.
        let _ = self.backend.store_blob(&data).map_err(Self::backend_err)?;
        ctx.push_blob(oid.to_string().into_bytes());
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

/// Parse a git OID from its UTF-8 hex representation (40 chars for SHA-1).
#[cfg(feature = "cogit")]
fn parse_git_oid(bytes: &[u8]) -> Result<covalence_hash::gix_hash::ObjectId, FError> {
    let s = std::str::from_utf8(bytes)
        .map_err(|e| FError::Parse(format!("git OID is not valid UTF-8: {e}")))?;
    let s = s.trim();
    covalence_hash::gix_hash::ObjectId::from_hex(s.as_bytes())
        .map_err(|e| FError::Parse(format!("invalid git OID {s:?}: {e}")))
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
            #[cfg(feature = "cogit")]
            git_store: None,
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
