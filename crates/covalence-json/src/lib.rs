//! Centralised JSON imports for the covalence workspace.
//!
//! Wraps `serde_json` so workspace crates do not pin their own
//! version. `serde` itself stays a normal workspace dependency —
//! crates that need `Serialize` / `Deserialize` derives import it
//! directly, since the derive macros resolve `serde` by name and
//! re-exporting it through this crate buys nothing.

pub use serde_json::{
    self, Error, Map, Number, Value, from_reader, from_slice, from_str, from_value, json,
    to_string, to_string_pretty, to_value, to_vec, to_vec_pretty, to_writer, to_writer_pretty,
};
