/*!
The kernel's trusted code base

This module is further subdivided into three primary components:
- `data`, which contains generic data structures and (trusted) functions for manipulating them
- `api`, which describes the generic API our rules are implemented over, including the API of the
  rules themselves
- `kernel`, which implements an LCF-style kernel for `covalence` over an abstract datastore
- `store`, which is a specific, trusted implementation of our datastore API using `egg`

In general, you shouldn't depend on this file directly, but rather use the re-exports and utility
functions provided in the rest of this crate. This is separated out into a separate file for the
purposes of documentation, as well as to make it easier to look for soundness issues.

The idea is that any functions visible from outside this module must be sound w.r.t. our type
theory; that is, they must not allow us to (safely) derive false statements. This includes anything
marked `pub(crate)`, which denotes a safe but unstable API used to implement external stable
wrappers.

The files in this module _only_ import each other and trusted external crates. We may, however, have
other imports in tests and doctests (the former should all be gated by `#[cfg(test)]`).
Our TCB hence consists of:
- the `trusted` module of `covalence_kernel`
- the `egg` crate for E-graph implementation; eventually we might vendor a specialized one
- the `indexmap` and `smallvec` crates for data structures
- the Rust compiler, toolchain, and standard library
- the WASM or native runtime used

Note that some impls may leak from other modules into the `trusted` module, e.g. on `Term`.
In general, we want to maintain the invariant that this never happens. To ensure this, we gate the
compilation of everything _except_ the trusted module by a default feature `wrapper`; we can then
check that the kernel compiles with default features disabled.

The other alternative would be to make a separate trusted kernel crate, but this would make it more
difficult to, e.g., add additional methods to `Term` that we nevertheless do not want to
consider part of our TCB. We might consider this approach in the future.
*/

/// Data structures
pub mod data;

/// Generic API
pub mod api;

/// Implementation of derivations
pub mod kernel;

/// Core API for term stores
pub mod store;
