/*!
The kernel's trusted code base

This module is further subdivided into three primary components:
- `data`, which contains generic data structures and (trusted) functions for manipulating them
- `api`, which describes the generic API our rules are implemented over, including the API of the
  rules themselves
- `rules`, which implements an LCF-style kernel for `covalence` over an abstract datastore
- `store`, which is a specific, trusted implementation of our datastore API using `egg`
- `kernel`, which instantiates the kernel in `rules` with the datastore
*/

pub mod api;
pub mod data;
pub mod kernel;
pub mod sexpr;
pub mod store;
pub mod rules;