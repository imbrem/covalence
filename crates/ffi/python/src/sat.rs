use pyo3::prelude::*;

use covalence_sat::{
    check_proof,
    parse::{parse_dimacs, parse_drat_binary, parse_drat_text},
};

use crate::compression;

/// A CNF formula in DIMACS format.
#[pyclass(name = "Cnf")]
pub struct PyCnf(covalence_sat::Cnf);

#[pymethods]
impl PyCnf {
    /// Number of variables.
    #[getter]
    fn num_vars(&self) -> u32 {
        self.0.num_vars()
    }

    /// Number of clauses.
    #[getter]
    fn num_clauses(&self) -> usize {
        self.0.num_clauses()
    }

    /// Return clauses as a list of lists of DIMACS-format integers.
    fn clauses(&self) -> Vec<Vec<i32>> {
        self.0
            .clauses()
            .map(|c| c.lits().iter().map(|l| l.dimacs()).collect())
            .collect()
    }
}

/// A DRAT proof.
#[pyclass(name = "DratProof")]
pub struct PyDratProof(covalence_sat::DratProof);

#[pymethods]
impl PyDratProof {
    /// Number of proof steps.
    #[getter]
    fn num_steps(&self) -> usize {
        self.0.len()
    }
}

/// Parse a DIMACS CNF string.
#[pyfunction]
pub fn parse_dimacs_str(text: &str) -> PyResult<PyCnf> {
    parse_dimacs(text)
        .map(PyCnf)
        .map_err(|e| pyo3::exceptions::PyValueError::new_err(e.to_string()))
}

/// Parse a DRAT proof from text format.
#[pyfunction]
pub fn parse_drat_text_str(text: &str) -> PyResult<PyDratProof> {
    parse_drat_text(text)
        .map(PyDratProof)
        .map_err(|e| pyo3::exceptions::PyValueError::new_err(e.to_string()))
}

/// Parse a DRAT proof from binary format.
#[pyfunction]
pub fn parse_drat_binary_bytes(data: &[u8]) -> PyResult<PyDratProof> {
    parse_drat_binary(data)
        .map(PyDratProof)
        .map_err(|e| pyo3::exceptions::PyValueError::new_err(e.to_string()))
}

/// Check a DRAT proof against a CNF formula using the watched-literal checker.
/// Returns True if the proof is valid.
#[pyfunction]
pub fn check_drat(cnf: &PyCnf, proof: &PyDratProof) -> bool {
    let mut checker = covalence_sat::WatchedDratChecker::new(&cnf.0);
    check_proof(&mut checker, &proof.0)
}

/// Load a DIMACS CNF file (auto-decompresses .gz, .bz2, .zst).
#[pyfunction]
pub fn load_dimacs(path: &str) -> PyResult<PyCnf> {
    let data = compression::read_file(path)
        .map_err(|e| pyo3::exceptions::PyIOError::new_err(e.to_string()))?;
    let text = String::from_utf8(data)
        .map_err(|e| pyo3::exceptions::PyValueError::new_err(e.to_string()))?;
    parse_dimacs(&text)
        .map(PyCnf)
        .map_err(|e| pyo3::exceptions::PyValueError::new_err(e.to_string()))
}

/// Load a DRAT proof file (auto-decompresses .gz, .bz2, .zst).
///
/// If `binary` is True, parse as binary DRAT. If False, parse as text.
/// If None (default), try text first, fall back to binary.
#[pyfunction]
#[pyo3(signature = (path, binary=None))]
pub fn load_drat(path: &str, binary: Option<bool>) -> PyResult<PyDratProof> {
    let data = compression::read_file(path)
        .map_err(|e| pyo3::exceptions::PyIOError::new_err(e.to_string()))?;

    match binary {
        Some(true) => parse_drat_binary(&data)
            .map(PyDratProof)
            .map_err(|e| pyo3::exceptions::PyValueError::new_err(e.to_string())),
        Some(false) => {
            let text = String::from_utf8(data)
                .map_err(|e| pyo3::exceptions::PyValueError::new_err(e.to_string()))?;
            parse_drat_text(&text)
                .map(PyDratProof)
                .map_err(|e| pyo3::exceptions::PyValueError::new_err(e.to_string()))
        }
        None => {
            // Try text first, fall back to binary.
            if let Ok(text) = String::from_utf8(data.clone())
                && let Ok(proof) = parse_drat_text(&text)
            {
                return Ok(PyDratProof(proof));
            }
            parse_drat_binary(&data)
                .map(PyDratProof)
                .map_err(|e| pyo3::exceptions::PyValueError::new_err(e.to_string()))
        }
    }
}
