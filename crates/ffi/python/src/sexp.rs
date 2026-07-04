use pyo3::exceptions::{PyIndexError, PyValueError};
use pyo3::prelude::*;
use pyo3::types::{PyBytes, PyList};

use covalence_sexp::{Atom, SExp, SExpr};

// ---------------------------------------------------------------------------
// PySExp — wraps SExp<Atom>
// ---------------------------------------------------------------------------

/// An S-expression node (symbol, string literal, or list).
#[pyclass(name = "SExp", from_py_object)]
#[derive(Clone)]
pub struct PySExp {
    inner: SExpr,
}

impl PySExp {
    fn from_inner(inner: SExpr) -> Self {
        PySExp { inner }
    }
}

#[pymethods]
impl PySExp {
    // --- Constructors ---

    /// Parse S-expressions from a string.
    ///
    /// dialect: "covalence" (default), "smt", or "wat"
    #[staticmethod]
    #[pyo3(signature = (input, dialect = "covalence"))]
    fn parse(input: &str, dialect: &str) -> PyResult<Vec<PySExp>> {
        let result = match dialect {
            "covalence" => covalence_sexp::parse(input),
            "smt" => covalence_sexp::parse_smt(input),
            "wat" => covalence_sexp::parse_wat(input),
            _ => {
                return Err(PyValueError::new_err(format!(
                    "unknown dialect: {dialect:?} (expected \"covalence\", \"smt\", or \"wat\")"
                )));
            }
        };
        let sexps = result.map_err(|e| PyValueError::new_err(e.to_string()))?;
        Ok(sexps.into_iter().map(PySExp::from_inner).collect())
    }

    /// Create a symbol atom.
    #[staticmethod]
    fn symbol(name: &str) -> PySExp {
        PySExp::from_inner(SExp::symbol(name))
    }

    /// Create a string literal atom.
    #[staticmethod]
    #[pyo3(signature = (data, format = ""))]
    fn string(data: &[u8], format: &str) -> PySExp {
        PySExp::from_inner(SExp::string(format, bytes::Bytes::copy_from_slice(data)))
    }

    /// Create a list node.
    #[staticmethod]
    fn list(children: Vec<PySExp>) -> PySExp {
        PySExp::from_inner(SExp::List(children.into_iter().map(|c| c.inner).collect()))
    }

    // --- Predicates ---

    /// True if this is an atom (symbol or string).
    fn is_atom(&self) -> bool {
        matches!(&self.inner, SExp::Atom(_))
    }

    /// True if this is a list.
    fn is_list(&self) -> bool {
        matches!(&self.inner, SExp::List(_))
    }

    /// True if this is a symbol atom.
    fn is_symbol(&self) -> bool {
        self.inner.as_symbol().is_some()
    }

    /// True if this is a string literal atom.
    fn is_string(&self) -> bool {
        self.inner.as_str().is_some()
    }

    // --- Accessors ---

    /// The symbol name, or None if not a symbol.
    #[getter]
    fn symbol_name(&self) -> Option<String> {
        self.inner.as_symbol().map(|s| s.to_owned())
    }

    /// The string bytes, or None if not a string literal.
    #[getter]
    fn string_bytes<'py>(&self, py: Python<'py>) -> Option<Bound<'py, PyBytes>> {
        self.inner
            .as_str()
            .map(|(_, bytes)| PyBytes::new(py, bytes))
    }

    /// The string format prefix, or None if not a string literal.
    #[getter]
    fn string_format(&self) -> Option<String> {
        self.inner.as_str().map(|(fmt, _)| fmt.to_owned())
    }

    /// The children if this is a list, or None.
    #[getter]
    fn children(&self) -> Option<Vec<PySExp>> {
        self.inner.as_list().map(|items| {
            items
                .iter()
                .map(|s| PySExp::from_inner(s.clone()))
                .collect()
        })
    }

    fn __len__(&self) -> PyResult<usize> {
        match &self.inner {
            SExp::List(items) => Ok(items.len()),
            SExp::Atom(_) => Err(PyValueError::new_err("atom has no length")),
        }
    }

    fn __getitem__(&self, index: isize) -> PyResult<PySExp> {
        match &self.inner {
            SExp::List(items) => normalize_index(items.len(), index)
                .and_then(|i| items.get(i))
                .map(|item| PySExp::from_inner(item.clone()))
                .ok_or_else(|| PyIndexError::new_err("index out of range")),
            SExp::Atom(_) => Err(PyValueError::new_err("atom is not subscriptable")),
        }
    }

    fn __eq__(&self, other: &PySExp) -> bool {
        self.inner == other.inner
    }

    // --- Output ---

    /// Pretty-print this S-expression.
    fn prettyprint(&self) -> PyResult<String> {
        let mut buf = Vec::new();
        covalence_sexp::prettyprint(std::slice::from_ref(&self.inner), &mut buf)
            .map_err(|e| PyValueError::new_err(e.to_string()))?;
        String::from_utf8(buf).map_err(|e| PyValueError::new_err(e.to_string()))
    }

    fn __repr__(&self) -> String {
        match &self.inner {
            SExp::Atom(Atom::Symbol(s)) => format!("SExp.symbol({s:?})"),
            SExp::Atom(Atom::Str { format, bytes }) => {
                format!("SExp.string({bytes:?}, format={format:?})")
            }
            SExp::List(items) => format!("SExp.list([...; {}])", items.len()),
        }
    }

    fn __str__(&self) -> PyResult<String> {
        self.prettyprint()
    }

    // --- Mapping ---

    /// Map atom SExps to Python objects, producing a PySExp.
    ///
    /// The callback receives each atom SExp and should return a Python object.
    fn map(&self, f: &Bound<'_, PyAny>) -> PyResult<PyPySExp> {
        map_sexp_to_pysexp(&self.inner, f)
    }

    /// Convert to PySExp with default mapping: Symbol→str, Str→bytes.
    fn to_py(&self, py: Python<'_>) -> PyResult<PyPySExp> {
        to_py_default(py, &self.inner)
    }
}

fn map_sexp_to_pysexp(sexp: &SExpr, f: &Bound<'_, PyAny>) -> PyResult<PyPySExp> {
    match sexp {
        SExp::Atom(_) => {
            let py_sexp = PySExp::from_inner(sexp.clone());
            let result = f.call1((py_sexp,))?;
            Ok(PyPySExp {
                inner: SExp::Atom(result.unbind()),
            })
        }
        SExp::List(items) => {
            let children: Vec<SExp<Py<PyAny>>> = items
                .iter()
                .map(|item| {
                    let mapped = map_sexp_to_pysexp(item, f)?;
                    Ok(mapped.inner)
                })
                .collect::<PyResult<_>>()?;
            Ok(PyPySExp {
                inner: SExp::List(children),
            })
        }
    }
}

fn to_py_default(py: Python<'_>, sexp: &SExpr) -> PyResult<PyPySExp> {
    match sexp {
        SExp::Atom(Atom::Symbol(s)) => Ok(PyPySExp {
            inner: SExp::Atom(s.as_str().into_pyobject(py)?.into_any().unbind()),
        }),
        SExp::Atom(Atom::Str { bytes, .. }) => Ok(PyPySExp {
            inner: SExp::Atom(PyBytes::new(py, bytes).into_any().unbind()),
        }),
        SExp::List(items) => {
            let children = items
                .iter()
                .map(|item| Ok(to_py_default(py, item)?.inner))
                .collect::<PyResult<_>>()?;
            Ok(PyPySExp {
                inner: SExp::List(children),
            })
        }
    }
}

// ---------------------------------------------------------------------------
// Helper: deep-clone SExp<Py<PyAny>> (requires GIL)
// ---------------------------------------------------------------------------

fn clone_py_sexp(py: Python<'_>, sexp: &SExp<Py<PyAny>>) -> SExp<Py<PyAny>> {
    match sexp {
        SExp::Atom(obj) => SExp::Atom(obj.clone_ref(py)),
        SExp::List(items) => SExp::List(items.iter().map(|item| clone_py_sexp(py, item)).collect()),
    }
}

// ---------------------------------------------------------------------------
// PyPySExp — wraps SExp<Py<PyAny>>
// ---------------------------------------------------------------------------

/// Resolve a Python-style (possibly negative) index into a positive index.
fn normalize_index(len: usize, index: isize) -> Option<usize> {
    if index < 0 {
        len.checked_sub((-index) as usize)
    } else {
        Some(index as usize)
    }
}

/// An S-expression node with Python object atoms.
#[pyclass(name = "PySExp", skip_from_py_object)]
pub struct PyPySExp {
    inner: SExp<Py<PyAny>>,
}

#[pymethods]
impl PyPySExp {
    // --- Constructors ---

    /// Create an atom wrapping a Python object.
    #[staticmethod]
    fn atom(value: Py<PyAny>) -> PyPySExp {
        PyPySExp {
            inner: SExp::Atom(value),
        }
    }

    /// Create a list node.
    #[staticmethod]
    fn list(py: Python<'_>, children: &Bound<'_, PyList>) -> PyResult<PyPySExp> {
        let items: Vec<SExp<Py<PyAny>>> = children
            .iter()
            .map(|c| {
                let borrowed = c.cast::<PyPySExp>()?;
                let inner = &borrowed.borrow().inner;
                Ok(clone_py_sexp(py, inner))
            })
            .collect::<PyResult<_>>()?;
        Ok(PyPySExp {
            inner: SExp::List(items),
        })
    }

    // --- Predicates ---

    fn is_atom(&self) -> bool {
        matches!(&self.inner, SExp::Atom(_))
    }

    fn is_list(&self) -> bool {
        matches!(&self.inner, SExp::List(_))
    }

    // --- Accessors ---

    /// The Python object value, or None if not an atom.
    #[getter]
    fn value(&self, py: Python<'_>) -> Option<Py<PyAny>> {
        match &self.inner {
            SExp::Atom(obj) => Some(obj.clone_ref(py)),
            SExp::List(_) => None,
        }
    }

    /// The children if this is a list, or None.
    #[getter]
    fn children(&self, py: Python<'_>) -> Option<Vec<PyPySExp>> {
        match &self.inner {
            SExp::List(items) => Some(
                items
                    .iter()
                    .map(|s| PyPySExp {
                        inner: clone_py_sexp(py, s),
                    })
                    .collect(),
            ),
            SExp::Atom(_) => None,
        }
    }

    fn __len__(&self) -> PyResult<usize> {
        match &self.inner {
            SExp::List(items) => Ok(items.len()),
            SExp::Atom(_) => Err(PyValueError::new_err("atom has no length")),
        }
    }

    fn __getitem__(&self, py: Python<'_>, index: isize) -> PyResult<PyPySExp> {
        match &self.inner {
            SExp::List(items) => normalize_index(items.len(), index)
                .and_then(|i| items.get(i))
                .map(|item| PyPySExp {
                    inner: clone_py_sexp(py, item),
                })
                .ok_or_else(|| PyIndexError::new_err("index out of range")),
            SExp::Atom(_) => Err(PyValueError::new_err("atom is not subscriptable")),
        }
    }

    // --- Mapping ---

    /// Map atom values through a Python callable.
    fn map(&self, py: Python<'_>, f: &Bound<'_, PyAny>) -> PyResult<PyPySExp> {
        map_pysexp(py, &self.inner, f)
    }

    fn __repr__(&self, py: Python<'_>) -> String {
        match &self.inner {
            SExp::Atom(obj) => {
                let repr = obj
                    .bind(py)
                    .repr()
                    .map(|s| s.to_string())
                    .unwrap_or_else(|_| "?".to_string());
                format!("PySExp.atom({repr})")
            }
            SExp::List(items) => format!("PySExp.list([...; {}])", items.len()),
        }
    }
}

fn map_pysexp(py: Python<'_>, sexp: &SExp<Py<PyAny>>, f: &Bound<'_, PyAny>) -> PyResult<PyPySExp> {
    match sexp {
        SExp::Atom(obj) => {
            let result = f.call1((obj.clone_ref(py),))?;
            Ok(PyPySExp {
                inner: SExp::Atom(result.unbind()),
            })
        }
        SExp::List(items) => {
            let children: Vec<SExp<Py<PyAny>>> = items
                .iter()
                .map(|item| {
                    let mapped = map_pysexp(py, item, f)?;
                    Ok(mapped.inner)
                })
                .collect::<PyResult<_>>()?;
            Ok(PyPySExp {
                inner: SExp::List(children),
            })
        }
    }
}

// ---------------------------------------------------------------------------
// Module-level parse functions
// ---------------------------------------------------------------------------

/// Parse S-expressions using the Covalence dialect.
#[pyfunction]
pub fn parse_sexp(input: &str) -> PyResult<Vec<PySExp>> {
    let sexps = covalence_sexp::parse(input).map_err(|e| PyValueError::new_err(e.to_string()))?;
    Ok(sexps.into_iter().map(PySExp::from_inner).collect())
}

/// Parse S-expressions using the SMT-LIB dialect.
#[pyfunction]
pub fn parse_sexp_smt(input: &str) -> PyResult<Vec<PySExp>> {
    let sexps =
        covalence_sexp::parse_smt(input).map_err(|e| PyValueError::new_err(e.to_string()))?;
    Ok(sexps.into_iter().map(PySExp::from_inner).collect())
}

/// Parse S-expressions using the WAT dialect.
#[pyfunction]
pub fn parse_sexp_wat(input: &str) -> PyResult<Vec<PySExp>> {
    let sexps =
        covalence_sexp::parse_wat(input).map_err(|e| PyValueError::new_err(e.to_string()))?;
    Ok(sexps.into_iter().map(PySExp::from_inner).collect())
}
