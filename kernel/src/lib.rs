/*!
The `covalence` kernel, parametrized by a datastore `D`
*/

pub mod data;
pub mod fact;
pub mod store;
pub mod theorem;
pub mod univ;

pub use theorem::{Kernel, Theorem};
