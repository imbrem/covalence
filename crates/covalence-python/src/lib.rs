mod backend;
mod component;
mod component_builder;
mod compression;
mod container;
mod container_builder;
mod default;
mod git;
mod graph;
mod hash;
mod kvstore;
#[cfg(feature = "llm")]
mod llm;
mod module;
mod module_builder;
mod object_store;
mod sat;
mod server;
mod session;
mod sexp;
mod signing;
mod store;
mod system_builder;
mod table;
mod tagged_store;
mod treestore;
mod val;
mod wasm_store;
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
    m.add_class::<module::Module>()?;
    m.add_class::<container::Container>()?;
    m.add_class::<store::Store>()?;
    m.add_class::<tagged_store::PyTaggedStore>()?;
    m.add_class::<object_store::PyObjectStore>()?;
    m.add_class::<git::GitStore>()?;
    m.add_class::<git::GitImport>()?;
    m.add_class::<git::GitRef>()?;
    m.add_class::<git::GitCloneResult>()?;
    m.add_class::<server::Server>()?;
    m.add_class::<table::PyRowSchema>()?;
    m.add_class::<table::PyTableBuilder>()?;
    m.add_class::<table::PyDirectoryBuilder>()?;
    m.add_class::<treestore::TreeStore>()?;
    m.add_class::<kvstore::KvStore>()?;
    m.add_class::<kvstore::MemoryKvStore>()?;
    m.add_class::<kvstore::AwsKvStore>()?;
    m.add_class::<kvstore::S3KvStore>()?;
    m.add_class::<val::PyVal>()?;
    m.add_class::<val::PyValType>()?;
    m.add_class::<signing::Principal>()?;
    m.add_class::<signing::Signature>()?;
    m.add_class::<signing::Signer>()?;

    // (The HOL kernel Python API — `pure` module exposing
    // Type/Term/Thm — is to be reinstated on `covalence-hol`.
    // See notes/type-hierarchy.md.)

    // Builder types
    m.add_class::<container_builder::ContainerBuilder>()?;
    m.add_class::<component_builder::ComponentBuilder>()?;
    m.add_class::<module_builder::ModuleBuilder>()?;
    m.add_class::<module_builder::FuncBuilder>()?;
    m.add_class::<module_builder::FuncRef>()?;
    m.add_class::<module_builder::InstanceRef>()?;

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
    m.add_function(wrap_pyfunction!(git::git_clone, m)?)?;

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

    // SAT / DRAT
    m.add_class::<sat::PyCnf>()?;
    m.add_class::<sat::PyDratProof>()?;
    m.add_function(wrap_pyfunction!(sat::parse_dimacs_str, m)?)?;
    m.add_function(wrap_pyfunction!(sat::parse_drat_text_str, m)?)?;
    m.add_function(wrap_pyfunction!(sat::parse_drat_binary_bytes, m)?)?;
    m.add_function(wrap_pyfunction!(sat::check_drat, m)?)?;
    m.add_function(wrap_pyfunction!(sat::load_dimacs, m)?)?;
    m.add_function(wrap_pyfunction!(sat::load_drat, m)?)?;

    // Compression
    m.add_function(wrap_pyfunction!(compression::read_compressed, m)?)?;

    // LLM bindings (covalence-llm, feature-gated)
    #[cfg(feature = "llm")]
    llm::register(m)?;

    // Module-level convenience functions (lazy default backend)
    m.add_function(wrap_pyfunction!(default::store, m)?)?;
    m.add_function(wrap_pyfunction!(default::store_str, m)?)?;
    m.add_function(wrap_pyfunction!(default::get, m)?)?;
    m.add_function(wrap_pyfunction!(default::has, m)?)?;
    m.add_function(wrap_pyfunction!(default::compile_wat, m)?)?;

    // wasm_store submodule
    wasm_store::register(m)?;

    // covalence-graph: Graph + GraphBuilder
    graph::register(m)?;

    Ok(())
}
