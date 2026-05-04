fn main() {
    println!(
        "cargo::rustc-env=COV_TARGET={}",
        std::env::var("TARGET").unwrap()
    );
}
