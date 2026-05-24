mod varint;

mod dir;
mod table;

pub use dir::{Dir, DirRow, DirRowRef};
pub use table::{
    DynSchema, FieldSpec, FieldType, RowSchema, TableBuilder, TableError, TableParser, min_bytes,
};
