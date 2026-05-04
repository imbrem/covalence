fn main() {
    if std::env::var("CARGO_FEATURE_STATIC").is_ok() {
        let web_build = concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../apps/covalence-web/build"
        );
        println!("cargo::rerun-if-changed={web_build}");

        if !std::path::Path::new(web_build).exists() {
            println!(
                "cargo::warning=apps/covalence-web/build/ not found — run `bun run build:web` first. \
                 The server will return 404 for all static files."
            );
        }
    }
}
