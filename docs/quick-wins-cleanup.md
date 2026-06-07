# Quick Wins: Clarity/Correctness/Testing

This note tracks low-risk cleanup opportunities found during a fast pass, with architecture and API unchanged.

## Completed in this pass

- Removed dead code scaffolding in `crates/covalence-kernel/src/hash.rs` (deleted unused `Arc` import and phantom `#[allow(dead_code)]` workaround).
- Reduced repetition in `crates/covalence-python/src/module_builder.rs` by centralizing instruction emission in `FuncBuilder::push_instr`/`push_op`.
- Reduced repetition in `crates/covalence-fuse/src/tree_fs.rs` by centralizing repeated inode-size decision logic in `TreeFs::size_for`.
- Reduced repetition in `crates/covalence-python/src/module_builder.rs` by extracting shared container-chain validation into `ModuleBuilder::require_container_id`.
- Reduced repetition in `crates/covalence-fuse/src/tree_fs.rs` by extracting `.` / `..` entry constructors for `readdir` and `readdirplus`.
- Added focused unit tests in `crates/covalence-fuse/src/tree_fs.rs` for `mode_to_fuse` mappings.
- Reduced repetition in `crates/covalence-git/src/store/sqlite_store.rs` by extracting shared blob-data query logic used by `all_blob_data` and `all_tree_data`.
- Reduced repeated module-initialization boilerplate in `crates/covalence-python/src/{system_builder,module_builder,component_builder,container_builder}.rs` via `SystemBuilder::new_module_data`.
- Reduced repeated git-object existence checks in `crates/covalence-git/src/store/sqlite_store.rs` via `GitStore::has_git_object`.

## Additional quick-win opportunities

- `crates/covalence-kernel/src/hash.rs`: currently recursive hashing of imports recomputes source arena hashes inline; a memoized helper could improve performance for large shared import graphs without changing the hash scheme.
- Test coverage opportunity: add focused unit tests around the extracted helper paths (`size_for`, instruction emission helpers) to lock in behavior while allowing future internal refactors.
