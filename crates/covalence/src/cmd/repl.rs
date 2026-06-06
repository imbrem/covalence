use crate::VERSION_LONG;

#[derive(clap::Args)]
pub struct ReplArgs {
    /// Force standalone mode (no server discovery)
    #[arg(long)]
    standalone: bool,

    /// Connect to a specific server (Unix socket path or HTTP URL)
    #[arg(long)]
    connect: Option<String>,

    /// Syntax highlighting: auto (default), always, or never.
    /// Respects NO_COLOR env var when set to auto.
    #[arg(long, default_value = "auto")]
    color: ColorMode,

    /// Use SQLite store for persistence (optional path; defaults to XDG data dir)
    #[arg(long, num_args = 0..=1, default_missing_value = "")]
    store: Option<String>,

    /// Use in-memory store (default, conflicts with --store)
    #[arg(long, conflicts_with = "store")]
    memory: bool,
}

#[derive(Clone, Copy, PartialEq, Eq, clap::ValueEnum)]
pub enum ColorMode {
    Auto,
    Always,
    Never,
}

/// Check if parentheses are balanced (accounting for strings).
pub fn parens_balanced(input: &str) -> bool {
    let mut depth: i32 = 0;
    let mut in_string = false;
    let mut escape = false;
    for ch in input.chars() {
        if escape {
            escape = false;
            continue;
        }
        if in_string {
            match ch {
                '\\' => escape = true,
                '"' => in_string = false,
                _ => {}
            }
            continue;
        }
        match ch {
            '"' => in_string = true,
            '(' => depth += 1,
            ')' => depth -= 1,
            ';' => break, // rest is comment
            _ => {}
        }
    }
    depth <= 0
}

#[cfg(not(target_family = "wasm"))]
pub fn run(args: ReplArgs) -> eyre::Result<()> {
    use crate::highlight;
    use rustyline::Editor;

    let color = match args.color {
        ColorMode::Always => true,
        ColorMode::Never => false,
        ColorMode::Auto => {
            // Respect NO_COLOR convention; also check if stdout is a terminal
            std::env::var_os("NO_COLOR").is_none()
                && std::io::IsTerminal::is_terminal(&std::io::stdout())
        }
    };

    let backend: Box<dyn covalence_shell::SyncBackend> = if let Some(ref addr) = args.connect {
        super::connect_backend(addr)
    } else if args.standalone {
        let store = super::resolve_store(args.store)?;
        let kernel = covalence_shell::Kernel::with_store(store);
        Box::new(kernel)
    } else {
        // Auto-discovery: try to find a running server, fall back to kernel
        let cwd = std::env::current_dir().ok();
        let servers = covalence_proto::discovery::discover_servers(cwd.as_deref());
        if let Some(url) = servers.first().and_then(|(_, desc)| desc.url.as_ref()) {
            println!(
                "connected to server {} (pid {})",
                servers[0].1.id, servers[0].1.pid
            );
            Box::new(covalence_client::SyncHttpBackend::new(url.clone()))
        } else {
            let store = super::resolve_store(args.store)?;
            let kernel = covalence_shell::Kernel::with_store(store);
            Box::new(kernel)
        }
    };

    let mut session = covalence_repl::Session::new(backend, true, true);

    println!("covalence {VERSION_LONG}");
    println!("Type help for available commands.\n");

    let helper = highlight::SexpHelper { color };
    let mut rl = Editor::new()?;
    rl.set_helper(Some(helper));
    let mut buf = String::new();

    loop {
        let prompt = if buf.is_empty() { "cov> " } else { "...> " };
        match rl.readline(prompt) {
            Ok(line) => {
                let line = line.trim_end();
                if buf.is_empty() && line.is_empty() {
                    continue;
                }
                if !buf.is_empty() {
                    buf.push('\n');
                }
                buf.push_str(line);

                // Check if parens are balanced before evaluating.
                if !parens_balanced(&buf) {
                    continue;
                }

                let input = buf.trim();
                if !input.is_empty() {
                    let _ = rl.add_history_entry(input);
                    let result = session.eval(input);
                    if !result.is_empty() {
                        println!("{}", highlight::highlight_output(&result, color));
                    }
                }
                buf.clear();
            }
            Err(
                rustyline::error::ReadlineError::Interrupted | rustyline::error::ReadlineError::Eof,
            ) => {
                break;
            }
            Err(e) => {
                eprintln!("readline error: {e}");
                break;
            }
        }
    }

    Ok(())
}
