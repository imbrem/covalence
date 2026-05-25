use pyo3::exceptions::{PyTypeError, PyValueError};
use pyo3::prelude::*;
use pyo3::types::{PyBytes, PyDict, PyList, PyString, PyTuple};

use covalence_object::{
    Dir, DirMode, DirRow, FieldSpec, FieldType, RowSchema, TableBuilder as RustTableBuilder,
    TableParser as RustTableParser,
};

use crate::backend::parse_hash;
use crate::hash::O256;

// ---------------------------------------------------------------------------
// RowSchema
// ---------------------------------------------------------------------------

/// Row schema: list of field specs for a table.
///
/// Each field is either `"blob"` (variable-length), `("ref", width)`, or
/// `("dep", width)`.
#[pyclass(frozen, name = "RowSchema")]
pub struct PyRowSchema {
    specs: Vec<FieldSpec>,
}

#[pymethods]
impl PyRowSchema {
    #[new]
    fn new(fields: &Bound<'_, PyList>) -> PyResult<Self> {
        let mut specs = Vec::with_capacity(fields.len());
        for item in fields.iter() {
            specs.push(parse_field_spec(&item)?);
        }
        Ok(Self { specs })
    }

    fn __len__(&self) -> usize {
        self.specs.len()
    }

    fn __repr__(&self) -> String {
        let fields: Vec<String> = self.specs.iter().map(format_field_spec).collect();
        format!("RowSchema([{}])", fields.join(", "))
    }
}

fn parse_field_spec(obj: &Bound<'_, PyAny>) -> PyResult<FieldSpec> {
    // "blob" -> FieldSpec::blob()
    if let Ok(s) = obj.cast::<PyString>() {
        let s = s.to_str()?;
        if s == "blob" {
            return Ok(FieldSpec::blob());
        }
        return Err(PyValueError::new_err(format!(
            "unknown field type string: {s:?} (expected \"blob\")"
        )));
    }
    // ("ref", width) or ("dep", width)
    if let Ok(tup) = obj.cast::<PyTuple>() {
        if tup.len() != 2 {
            return Err(PyValueError::new_err(
                "tuple field spec must be (type, width)",
            ));
        }
        let ty: String = tup.get_item(0)?.extract()?;
        let width: u8 = tup.get_item(1)?.extract()?;
        return match ty.as_str() {
            "ref" => Ok(FieldSpec::ref_index(width)),
            "dep" => Ok(FieldSpec::dep_index(width)),
            _ => Err(PyValueError::new_err(format!(
                "unknown field type: {ty:?} (expected \"ref\" or \"dep\")"
            ))),
        };
    }
    Err(PyTypeError::new_err(
        "field spec must be \"blob\" or (\"ref\"|\"dep\", width)",
    ))
}

fn format_field_spec(spec: &FieldSpec) -> String {
    match spec.field_type {
        FieldType::Blob => "\"blob\"".to_string(),
        FieldType::Ref => format!("(\"ref\", {})", spec.repr),
        FieldType::Dep => format!("(\"dep\", {})", spec.repr),
    }
}

// ---------------------------------------------------------------------------
// TableBuilder (dynamic schema)
// ---------------------------------------------------------------------------

/// Dynamic table builder using a RowSchema.
#[pyclass(name = "TableBuilder")]
pub struct PyTableBuilder {
    inner: Option<RustTableBuilder<RowSchema>>,
}

impl PyTableBuilder {
    fn builder_mut(&mut self) -> PyResult<&mut RustTableBuilder<RowSchema>> {
        self.inner
            .as_mut()
            .ok_or_else(|| PyValueError::new_err("builder already consumed by build()"))
    }
}

#[pymethods]
impl PyTableBuilder {
    #[new]
    fn new(schema: &PyRowSchema) -> Self {
        Self {
            inner: Some(RustTableBuilder::new(RowSchema::new(schema.specs.clone()))),
        }
    }

    /// Add a ref hash. Accepts O256 or hex string.
    fn push_ref(&mut self, key: &Bound<'_, PyAny>) -> PyResult<()> {
        let h = parse_hash(key)?;
        self.builder_mut()?.push_ref(h);
        Ok(())
    }

    /// Add a dep hash. Accepts O256 or hex string.
    fn push_dep(&mut self, key: &Bound<'_, PyAny>) -> PyResult<()> {
        let h = parse_hash(key)?;
        self.builder_mut()?.push_dep(h);
        Ok(())
    }

    /// Add a row of raw byte fields.
    fn push_row(&mut self, fields: &Bound<'_, PyList>) -> PyResult<()> {
        let mut row = Vec::with_capacity(fields.len());
        for item in fields.iter() {
            let bytes: Vec<u8> = item.extract()?;
            row.push(bytes);
        }
        self.builder_mut()?.push_row(row);
        Ok(())
    }

    /// Build the table blob (consumes the builder).
    fn build<'py>(&mut self, py: Python<'py>) -> PyResult<Bound<'py, PyBytes>> {
        let builder = self
            .inner
            .take()
            .ok_or_else(|| PyValueError::new_err("builder already consumed by build()"))?;
        let table = builder.build();
        Ok(PyBytes::new(py, table.as_bytes()))
    }

    /// Parse a table blob (dynamic schema auto-detected from header).
    /// Returns dict with schema, num_entries, refs, deps, rows.
    #[staticmethod]
    fn parse<'py>(py: Python<'py>, data: &[u8]) -> PyResult<Bound<'py, PyAny>> {
        let parser =
            RustTableParser::dynamic(data).map_err(|e| PyValueError::new_err(e.to_string()))?;

        let dict = PyDict::new(py);

        // schema — list of field spec descriptors
        let schema_list = PyList::empty(py);
        for spec in parser.field_specs() {
            schema_list.append(field_spec_to_py(py, spec)?)?;
        }
        dict.set_item("schema", schema_list)?;

        dict.set_item("num_entries", parser.num_entries())?;

        // refs
        let refs_list = PyList::empty(py);
        for h in parser.refs() {
            refs_list.append(O256(*h).into_pyobject(py)?)?;
        }
        dict.set_item("refs", refs_list)?;

        // deps
        let deps_list = PyList::empty(py);
        for h in parser.deps() {
            deps_list.append(O256(*h).into_pyobject(py)?)?;
        }
        dict.set_item("deps", deps_list)?;

        // rows
        let rows_list = PyList::empty(py);
        for i in 0..parser.num_entries() {
            let raw = parser
                .raw_row(i)
                .map_err(|e| PyValueError::new_err(e.to_string()))?;
            let row_list = PyList::empty(py);
            for field in raw {
                row_list.append(PyBytes::new(py, field))?;
            }
            rows_list.append(row_list)?;
        }
        dict.set_item("rows", rows_list)?;

        Ok(dict.into_any())
    }
}

fn field_spec_to_py<'py>(py: Python<'py>, spec: &FieldSpec) -> PyResult<Bound<'py, PyAny>> {
    match spec.field_type {
        FieldType::Blob => Ok(PyString::new(py, "blob").into_any()),
        FieldType::Ref => {
            let tup = PyTuple::new(
                py,
                &[
                    PyString::new(py, "ref").into_any(),
                    spec.repr.into_pyobject(py)?.into_any(),
                ],
            )?;
            Ok(tup.into_any())
        }
        FieldType::Dep => {
            let tup = PyTuple::new(
                py,
                &[
                    PyString::new(py, "dep").into_any(),
                    spec.repr.into_pyobject(py)?.into_any(),
                ],
            )?;
            Ok(tup.into_any())
        }
    }
}

// ---------------------------------------------------------------------------
// DirectoryBuilder (typed Dir schema)
// ---------------------------------------------------------------------------

/// Directory table builder using the typed Dir schema.
#[pyclass(name = "DirectoryBuilder")]
pub struct PyDirectoryBuilder {
    inner: Option<RustTableBuilder<Dir>>,
}

impl PyDirectoryBuilder {
    fn builder_mut(&mut self) -> PyResult<&mut RustTableBuilder<Dir>> {
        self.inner
            .as_mut()
            .ok_or_else(|| PyValueError::new_err("builder already consumed by build()"))
    }
}

#[pymethods]
impl PyDirectoryBuilder {
    #[new]
    fn new() -> Self {
        Self {
            inner: Some(RustTableBuilder::new(Dir)),
        }
    }

    /// Add a directory entry.
    ///
    /// - `name`: entry name (str or bytes)
    /// - `mode`: "blob" or "dir"
    /// - `child`: O256 hash or hex string
    fn push(
        &mut self,
        name: &Bound<'_, PyAny>,
        mode: &str,
        child: &Bound<'_, PyAny>,
    ) -> PyResult<()> {
        let name_bytes: Vec<u8> = if let Ok(s) = name.extract::<String>() {
            s.into_bytes()
        } else {
            name.extract::<Vec<u8>>()?
        };
        let dir_mode = match mode {
            "blob" | "regular" => DirMode::REGULAR,
            "executable" => DirMode::EXECUTABLE,
            "symlink" => DirMode::SYMLINK,
            "dir" => DirMode::DIR,
            "submodule" => DirMode::SUBMODULE,
            _ => {
                return Err(PyValueError::new_err(format!(
                    "unknown mode: {mode:?} (expected \"blob\", \"regular\", \"executable\", \"symlink\", \"dir\", or \"submodule\")"
                )));
            }
        };
        let child_hash = parse_hash(child)?;
        self.builder_mut()?.push_row(DirRow {
            name: name_bytes,
            mode: dir_mode,
            child: child_hash,
        });
        Ok(())
    }

    /// Build the directory table blob (consumes the builder).
    fn build<'py>(&mut self, py: Python<'py>) -> PyResult<Bound<'py, PyBytes>> {
        let builder = self
            .inner
            .take()
            .ok_or_else(|| PyValueError::new_err("builder already consumed by build()"))?;
        let table = builder.build();
        Ok(PyBytes::new(py, table.as_bytes()))
    }

    /// Parse a directory table blob.
    /// Returns dict with num_entries, refs, deps, rows.
    /// Each row is a dict with name (bytes), mode ("blob"|"dir"), child (O256).
    #[staticmethod]
    fn parse<'py>(py: Python<'py>, data: &[u8]) -> PyResult<Bound<'py, PyAny>> {
        let parser =
            RustTableParser::new(data, Dir).map_err(|e| PyValueError::new_err(e.to_string()))?;

        let dict = PyDict::new(py);
        dict.set_item("num_entries", parser.num_entries())?;

        // refs
        let refs_list = PyList::empty(py);
        for h in parser.refs() {
            refs_list.append(O256(*h).into_pyobject(py)?)?;
        }
        dict.set_item("refs", refs_list)?;

        // deps
        let deps_list = PyList::empty(py);
        for h in parser.deps() {
            deps_list.append(O256(*h).into_pyobject(py)?)?;
        }
        dict.set_item("deps", deps_list)?;

        // rows — typed DirRowRef
        let rows_list = PyList::empty(py);
        for i in 0..parser.num_entries() {
            let row = parser
                .row(i)
                .map_err(|e| PyValueError::new_err(e.to_string()))?;
            let row_dict = PyDict::new(py);
            row_dict.set_item("name", PyBytes::new(py, row.name))?;
            let mode_str = row.mode.name();
            row_dict.set_item("mode", mode_str)?;
            row_dict.set_item("child", O256(row.child).into_pyobject(py)?)?;
            rows_list.append(row_dict)?;
        }
        dict.set_item("rows", rows_list)?;

        Ok(dict.into_any())
    }
}
