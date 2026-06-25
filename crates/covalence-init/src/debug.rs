//! Minimal debug-instrumentation primitives.
//!
//! Just enough to time proof construction when chasing a slow theorem: set the
//! `COV_PROFILE` environment variable and [`timed`] regions print their elapsed
//! time to stderr. A full instrumentation/tracing system is future work (and the
//! layers around here are expected to change a lot first) — these are the basic
//! primitives that work today.
//!
//! The [`cached_thm!`](crate::cached_thm) macro routes every cached theorem
//! build through [`timed`], so `COV_PROFILE=1 cargo test …` prints how long each
//! cached derivation took to build.

/// Whether profiling output is enabled — true iff the `COV_PROFILE` environment
/// variable is set. Checked once and cached.
#[cfg(not(target_arch = "wasm32"))]
pub fn profiling() -> bool {
    static ON: std::sync::LazyLock<bool> =
        std::sync::LazyLock::new(|| std::env::var_os("COV_PROFILE").is_some());
    *ON
}

/// Profiling is always off on `wasm32` (there is no wall clock there).
#[cfg(target_arch = "wasm32")]
pub fn profiling() -> bool {
    false
}

/// Run `f`, printing `[cov-profile] <label>: <elapsed>` to stderr when
/// [`profiling`] is on. When off it is a single bool check then a plain call, so
/// it is safe to leave in hot paths; on `wasm32` it never touches a clock.
pub fn timed<T>(label: &str, f: impl FnOnce() -> T) -> T {
    #[cfg(not(target_arch = "wasm32"))]
    if profiling() {
        let start = std::time::Instant::now();
        let out = f();
        eprintln!("[cov-profile] {label}: {:?}", start.elapsed());
        return out;
    }
    let _ = label;
    f()
}
