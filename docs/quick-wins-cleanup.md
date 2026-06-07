# Quick Wins: Clarity/Correctness/Testing

This note tracks low-risk cleanup opportunities found during a fast pass, with architecture and API unchanged.

## Completed in this pass

- Removed dead code scaffolding in `crates/covalence-kernel/src/hash.rs` (deleted unused `Arc` import and phantom `#[allow(dead_code)]` workaround).
- Reduced repetition in `crates/covalence-python/src/module_builder.rs` by centralizing instruction emission in `FuncBuilder::push_instr`/`push_op`.
- Reduced repetition in `crates/covalence-fuse/src/tree_fs.rs` by centralizing repeated inode-size decision logic in `TreeFs::size_for`.

## Additional quick-win opportunities

- `crates/covalence-git/src/store/sqlite_store.rs`: repeated `conn.lock().unwrap()` + SQL error mapping patterns can be centralized in small private helpers to reduce boilerplate and improve consistency.
- `crates/covalence-python/src/module_builder.rs`: repeated `"kernel methods require a container chain ..."` checks appear in multiple methods and can be extracted to one validator helper.
- `crates/covalence-fuse/src/tree_fs.rs`: repeated creation of `.` / `..` directory entries (in both `readdir` and `readdirplus`) can be extracted to helper constructors.
- `crates/covalence-kernel/src/hash.rs`: currently recursive hashing of imports recomputes source arena hashes inline; a memoized helper could improve performance for large shared import graphs without changing the hash scheme.
- Test coverage opportunity: add focused unit tests around the extracted helper paths (`size_for`, instruction emission helpers) to lock in behavior while allowing future internal refactors.
