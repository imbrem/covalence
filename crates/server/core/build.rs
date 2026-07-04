fn main() {
    if std::env::var("CARGO_FEATURE_STATIC").is_ok() {
        let web_build = concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../../apps/covalence-web/build"
        );
        println!("cargo::rerun-if-changed={web_build}");

        if !std::path::Path::new(web_build).exists() {
            // Create empty directory so rust-embed compiles; the server
            // will serve the "not embedded" fallback page instead.
            std::fs::create_dir_all(web_build).ok();
            println!(
                "cargo::warning=apps/covalence-web/build/ not found — run `bun run build:web` to embed the frontend. \
                 The server will show a placeholder page."
            );
        }
    }
}
