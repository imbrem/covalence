mod error;

pub mod dimacs;
#[cfg(feature = "drat")]
pub mod drat;
#[cfg(feature = "lrat")]
pub mod lrat;

pub use error::ParseError;

pub use dimacs::{parse_dimacs, write_dimacs, write_dimacs_to_string};
#[cfg(feature = "drat")]
pub use drat::{
    parse_drat_binary, parse_drat_text, write_drat_binary, write_drat_binary_to_vec,
    write_drat_text, write_drat_text_to_string,
};
#[cfg(feature = "lrat")]
pub use lrat::parse_lrat_text;
