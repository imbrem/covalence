//! Python bindings for `covalence-graph`.
//!
//! Exposes `covalence.Graph` and `covalence.GraphBuilder` over the
//! `BytesGraph` (payload = `bytes`) flavor. Port names are `str`,
//! type ids are `int`, payloads are `bytes`.

use bytes::Bytes;
use covalence_graph::{
    BytesGraph, BytesGraphBuilder, CANONICAL_VERSION, Edge, NodeId, NodeKind, Port, PortId,
    PortKind, TypeId,
};
use pyo3::exceptions::{PyIndexError, PyValueError};
use pyo3::prelude::*;
use pyo3::types::{PyBytes, PyDict, PyList};

fn parse_port_kind(s: &str) -> PyResult<PortKind> {
    match s {
        "input" | "in" => Ok(PortKind::Input),
        "output" | "out" => Ok(PortKind::Output),
        _ => Err(PyValueError::new_err(format!(
            "port kind must be 'input' or 'output', got {s:?}"
        ))),
    }
}

fn port_kind_str(k: PortKind) -> &'static str {
    match k {
        PortKind::Input => "input",
        PortKind::Output => "output",
    }
}

fn parse_node_kind(s: &str) -> PyResult<NodeKind> {
    match s {
        "pure" => Ok(NodeKind::Pure),
        "ordered" => Ok(NodeKind::Ordered),
        _ => Err(PyValueError::new_err(format!(
            "node kind must be 'pure' or 'ordered', got {s:?}"
        ))),
    }
}

fn node_kind_str(k: NodeKind) -> &'static str {
    match k {
        NodeKind::Pure => "pure",
        NodeKind::Ordered => "ordered",
    }
}

/// Parse a port from a Python dict: {"name": str, "type_id": int,
/// "kind": "input" | "output"}.
fn parse_port(d: &Bound<'_, PyDict>) -> PyResult<Port> {
    let name: String = d
        .get_item("name")?
        .ok_or_else(|| PyValueError::new_err("port: missing 'name'"))?
        .extract()?;
    let type_id: u64 = d
        .get_item("type_id")?
        .ok_or_else(|| PyValueError::new_err("port: missing 'type_id'"))?
        .extract()?;
    let kind_str: String = d
        .get_item("kind")?
        .ok_or_else(|| PyValueError::new_err("port: missing 'kind'"))?
        .extract()?;
    Ok(Port {
        name,
        type_id: TypeId(type_id),
        kind: parse_port_kind(&kind_str)?,
    })
}

fn port_to_dict<'py>(py: Python<'py>, p: &Port) -> PyResult<Bound<'py, PyDict>> {
    let d = PyDict::new(py);
    d.set_item("name", &p.name)?;
    d.set_item("type_id", p.type_id.0)?;
    d.set_item("kind", port_kind_str(p.kind))?;
    Ok(d)
}

// ---------------------------------------------------------------------------
// Graph
// ---------------------------------------------------------------------------

/// An immutable, fully-built ordered graph (cov:graph@0.1.0).
#[pyclass(name = "Graph", frozen, from_py_object)]
#[derive(Clone)]
pub struct PyGraph {
    inner: BytesGraph,
}

#[pymethods]
impl PyGraph {
    /// Decode the canonical byte encoding (`COVG` v1).
    #[staticmethod]
    fn from_bytes(data: &[u8]) -> PyResult<Self> {
        BytesGraph::from_bytes(data)
            .map(|inner| Self { inner })
            .map_err(|e| PyValueError::new_err(e.to_string()))
    }

    fn to_bytes<'py>(&self, py: Python<'py>) -> Bound<'py, PyBytes> {
        PyBytes::new(py, &self.inner.to_bytes())
    }

    /// BLAKE3 keyed hash under the "ordered" domain. 32-byte digest.
    fn ordered_hash<'py>(&self, py: Python<'py>) -> Bound<'py, PyBytes> {
        PyBytes::new(py, self.inner.ordered_hash().as_bytes())
    }

    fn unordered_hash<'py>(&self, py: Python<'py>) -> Bound<'py, PyBytes> {
        PyBytes::new(py, self.inner.unordered_hash().as_bytes())
    }

    /// Hex of `ordered_hash`. Convenient for paste-into-URL workflows.
    fn ordered_hash_hex(&self) -> String {
        hex_lower(self.inner.ordered_hash().as_bytes())
    }

    fn unordered_hash_hex(&self) -> String {
        hex_lower(self.inner.unordered_hash().as_bytes())
    }

    #[getter]
    fn node_count(&self) -> u32 {
        self.inner.node_count()
    }

    #[getter]
    fn edge_count(&self) -> u32 {
        self.inner.edge_count()
    }

    /// Full snapshot as a Python dict:
    /// `{"version": 1, "nodes": [...], "edges": [...]}`.
    fn snapshot<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, PyDict>> {
        let out = PyDict::new(py);
        out.set_item("version", CANONICAL_VERSION)?;
        let nodes = PyList::empty(py);
        for n in self.inner.nodes() {
            let nd = PyDict::new(py);
            nd.set_item("kind", node_kind_str(n.kind))?;
            nd.set_item("label", n.label.clone())?;
            let ports = PyList::empty(py);
            for p in &n.ports {
                ports.append(port_to_dict(py, p)?)?;
            }
            nd.set_item("ports", ports)?;
            nd.set_item("payload", PyBytes::new(py, n.payload.as_ref()))?;
            nodes.append(nd)?;
        }
        out.set_item("nodes", nodes)?;
        let edges = PyList::empty(py);
        for e in self.inner.edges() {
            let ed = PyDict::new(py);
            ed.set_item("from_node", e.from_node.0)?;
            ed.set_item("from_port", e.from_port.0)?;
            ed.set_item("to_node", e.to_node.0)?;
            ed.set_item("to_port", e.to_port.0)?;
            edges.append(ed)?;
        }
        out.set_item("edges", edges)?;
        Ok(out)
    }

    fn get_node<'py>(&self, py: Python<'py>, id: u32) -> PyResult<Bound<'py, PyDict>> {
        let n = self
            .inner
            .get_node(NodeId(id))
            .ok_or_else(|| PyIndexError::new_err(format!("no node with id {id}")))?;
        let nd = PyDict::new(py);
        nd.set_item("kind", node_kind_str(n.kind))?;
        nd.set_item("label", n.label.clone())?;
        let ports = PyList::empty(py);
        for p in &n.ports {
            ports.append(port_to_dict(py, p)?)?;
        }
        nd.set_item("ports", ports)?;
        nd.set_item("payload", PyBytes::new(py, n.payload.as_ref()))?;
        Ok(nd)
    }

    /// Ids of `ordered`-kind nodes in insertion order.
    fn ordered_nodes(&self) -> Vec<u32> {
        self.inner.ordered_nodes().map(|n| n.0).collect()
    }

    /// Equality preserving insertion order of both nodes and edges.
    fn equal(&self, other: &PyGraph) -> bool {
        self.inner.equal(&other.inner)
    }

    fn __eq__(&self, other: &PyGraph) -> bool {
        self.equal(other)
    }

    fn __repr__(&self) -> String {
        format!(
            "Graph(nodes={}, edges={}, ordered_hash={})",
            self.inner.node_count(),
            self.inner.edge_count(),
            self.ordered_hash_hex(),
        )
    }
}

// ---------------------------------------------------------------------------
// GraphBuilder
// ---------------------------------------------------------------------------

/// Mutable graph under construction. One open builder produces one
/// `Graph` via `finish()`.
#[pyclass(name = "GraphBuilder", unsendable)]
pub struct PyGraphBuilder {
    inner: Option<BytesGraphBuilder>,
}

impl PyGraphBuilder {
    fn get(&mut self) -> PyResult<&mut BytesGraphBuilder> {
        self.inner
            .as_mut()
            .ok_or_else(|| PyValueError::new_err("builder already consumed by finish()"))
    }
}

#[pymethods]
impl PyGraphBuilder {
    #[new]
    fn new() -> Self {
        Self {
            inner: Some(BytesGraphBuilder::new()),
        }
    }

    /// Append a node and return its id.
    ///
    /// Args:
    ///   ports: list of `{"name": str, "type_id": int,
    ///                    "kind": "input"|"output"}` dicts
    ///   payload: opaque bytes
    ///   kind: "pure" (default) or "ordered"
    ///   label: optional free-form label
    #[pyo3(signature = (ports, payload, kind = "pure", label = None))]
    fn add_node(
        &mut self,
        ports: Vec<Bound<'_, PyDict>>,
        payload: &[u8],
        kind: &str,
        label: Option<String>,
    ) -> PyResult<u32> {
        let node_kind = parse_node_kind(kind)?;
        let mut parsed_ports = Vec::with_capacity(ports.len());
        for p in &ports {
            parsed_ports.push(parse_port(p)?);
        }
        let id = self.get()?.add_node(
            node_kind,
            label,
            parsed_ports,
            Bytes::copy_from_slice(payload),
        );
        Ok(id.0)
    }

    /// Wire output port (`from_node`, `from_port`) → input port
    /// (`to_node`, `to_port`). Raises on kind / type / linearity
    /// violations.
    fn wire(
        &mut self,
        from_node: u32,
        from_port: u32,
        to_node: u32,
        to_port: u32,
    ) -> PyResult<()> {
        self.get()?
            .wire(Edge {
                from_node: NodeId(from_node),
                from_port: PortId(from_port),
                to_node: NodeId(to_node),
                to_port: PortId(to_port),
            })
            .map_err(|e| PyValueError::new_err(e.to_string()))
    }

    /// Consume the builder and return an immutable Graph.
    fn finish(&mut self) -> PyResult<PyGraph> {
        let b = self
            .inner
            .take()
            .ok_or_else(|| PyValueError::new_err("builder already consumed by finish()"))?;
        b.finish()
            .map(|inner| PyGraph { inner })
            .map_err(|e| PyValueError::new_err(e.to_string()))
    }

    fn __repr__(&self) -> String {
        match &self.inner {
            Some(b) => format!(
                "GraphBuilder(nodes={}, edges={})",
                b.peek_nodes().len(),
                b.peek_edges().len(),
            ),
            None => "GraphBuilder(consumed)".into(),
        }
    }
}

fn hex_lower(bytes: &[u8]) -> String {
    let mut out = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        use std::fmt::Write as _;
        let _ = write!(out, "{b:02x}");
    }
    out
}

pub fn register(m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_class::<PyGraph>()?;
    m.add_class::<PyGraphBuilder>()?;
    Ok(())
}
