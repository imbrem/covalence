mod backend;
mod component;
mod default;
mod git;
mod hash;
mod server;
mod session;
mod sexp;
mod store;
mod table;
mod worker;

use pyo3::prelude::*;

#[pymodule]
fn covalence(m: &Bound<'_, PyModule>) -> PyResult<()> {
    // Types
    m.add_class::<hash::O256>()?;
    m.add_class::<hash::Hasher>()?;
    m.add_class::<git::GitObject>()?;
    m.add_class::<git::GitHasher>()?;
    m.add_class::<backend::Backend>()?;
    m.add_class::<session::Session>()?;
    m.add_class::<component::Component>()?;
    m.add_class::<store::Store>()?;
    m.add_class::<git::GitStore>()?;
    m.add_class::<server::Server>()?;
    m.add_class::<table::PyRowSchema>()?;
    m.add_class::<table::PyTableBuilder>()?;
    m.add_class::<table::PyDirectoryBuilder>()?;

    // Hasher constructors
    m.add_function(wrap_pyfunction!(hash::blake3, m)?)?;
    m.add_function(wrap_pyfunction!(hash::blake3_keyed, m)?)?;
    m.add_function(wrap_pyfunction!(hash::blake3_kdf, m)?)?;
    m.add_function(wrap_pyfunction!(hash::sha256, m)?)?;
    m.add_function(wrap_pyfunction!(hash::hasher, m)?)?;

    // Git hasher constructors
    m.add_function(wrap_pyfunction!(git::git_sha1, m)?)?;
    m.add_function(wrap_pyfunction!(git::git_sha256, m)?)?;
    m.add_function(wrap_pyfunction!(git::git_tree_to_dir_rows, m)?)?;

    // Backend constructors
    m.add_function(wrap_pyfunction!(backend::local, m)?)?;
    m.add_function(wrap_pyfunction!(backend::local_persistent, m)?)?;

    // Session constructor
    m.add_function(wrap_pyfunction!(session::session_local, m)?)?;

    // Server
    m.add_function(wrap_pyfunction!(server::serve, m)?)?;

    // S-expression types
    m.add_class::<sexp::PySExp>()?;
    m.add_class::<sexp::PyPySExp>()?;
    m.add_function(wrap_pyfunction!(sexp::parse_sexp, m)?)?;
    m.add_function(wrap_pyfunction!(sexp::parse_sexp_smt, m)?)?;
    m.add_function(wrap_pyfunction!(sexp::parse_sexp_wat, m)?)?;

    // Module-level convenience functions (lazy default backend)
    m.add_function(wrap_pyfunction!(default::store, m)?)?;
    m.add_function(wrap_pyfunction!(default::store_str, m)?)?;
    m.add_function(wrap_pyfunction!(default::get, m)?)?;
    m.add_function(wrap_pyfunction!(default::has, m)?)?;
    m.add_function(wrap_pyfunction!(default::compile_wat, m)?)?;
    m.add_function(wrap_pyfunction!(default::decide, m)?)?;

    Ok(())
}
