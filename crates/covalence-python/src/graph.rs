//! Python bindings for `covalence-graph`.
//!
//! Exposes:
//! - `covalence.Graph` / `covalence.GraphBuilder` — bare topology.
//! - `covalence.LabelList`, `covalence.KindFlags`, `covalence.StringDiagram`
//!   — overlay blobs and the composite.
//! - `covalence.render_svg(string_diagram_refs, graph, labels?, kinds?)`
//!   — produce SVG markup.

use bytes::Bytes;
use covalence_graph::{
    BytesGraph, BytesGraphBuilder, CANONICAL_VERSION, Edge, KindFlags, LabelList, LayoutOpts,
    NodeId, NodeKind, OverlayMap, Port, PortId, PortKind, ResolvedDiagram, SlotRef, StringDiagram,
    StringDiagramBuilder, TypeId, UniformTag, render_svg,
};
use pyo3::exceptions::{PyIndexError, PyValueError};
use pyo3::prelude::*;
use pyo3::types::{PyBytes, PyDict, PyList};

fn take_builder(inner: &mut Option<BytesGraphBuilder>) -> PyResult<BytesGraphBuilder> {
    inner
        .take()
        .ok_or_else(|| PyValueError::new_err("builder already consumed by finish()"))
}

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
    NodeKind::parse(s).ok_or_else(|| {
        PyValueError::new_err(format!("node kind must be 'pure' or 'ordered', got {s:?}"))
    })
}

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
    /// Decode the canonical byte encoding.
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
            nodes.append(node_to_dict(py, n)?)?;
        }
        out.set_item("nodes", nodes)?;
        let edges = PyList::empty(py);
        for e in self.inner.edges() {
            edges.append(edge_to_dict(py, e)?)?;
        }
        out.set_item("edges", edges)?;
        Ok(out)
    }

    fn get_node<'py>(&self, py: Python<'py>, id: u32) -> PyResult<Bound<'py, PyDict>> {
        let n = self
            .inner
            .get_node(NodeId(id))
            .ok_or_else(|| PyIndexError::new_err(format!("no node with id {id}")))?;
        node_to_dict(py, n)
    }

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

fn node_to_dict<'py>(
    py: Python<'py>,
    n: &covalence_graph::Node<Bytes>,
) -> PyResult<Bound<'py, PyDict>> {
    let nd = PyDict::new(py);
    let ports = PyList::empty(py);
    for p in &n.ports {
        ports.append(port_to_dict(py, p)?)?;
    }
    nd.set_item("ports", ports)?;
    nd.set_item("payload", PyBytes::new(py, n.payload.as_ref()))?;
    Ok(nd)
}

fn edge_to_dict<'py>(py: Python<'py>, e: &Edge) -> PyResult<Bound<'py, PyDict>> {
    let ed = PyDict::new(py);
    ed.set_item("from_node", e.from_node.0)?;
    ed.set_item("from_port", e.from_port.0)?;
    ed.set_item("to_node", e.to_node.0)?;
    ed.set_item("to_port", e.to_port.0)?;
    Ok(ed)
}

// ---------------------------------------------------------------------------
// GraphBuilder
// ---------------------------------------------------------------------------

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
    fn add_node(&mut self, ports: Vec<Bound<'_, PyDict>>, payload: &[u8]) -> PyResult<u32> {
        let mut parsed_ports = Vec::with_capacity(ports.len());
        for p in &ports {
            parsed_ports.push(parse_port(p)?);
        }
        let id = self
            .get()?
            .add_node(parsed_ports, Bytes::copy_from_slice(payload));
        Ok(id.0)
    }

    fn wire(&mut self, from_node: u32, from_port: u32, to_node: u32, to_port: u32) -> PyResult<()> {
        self.get()?
            .wire(Edge {
                from_node: NodeId(from_node),
                from_port: PortId(from_port),
                to_node: NodeId(to_node),
                to_port: PortId(to_port),
            })
            .map_err(|e| PyValueError::new_err(e.to_string()))
    }

    fn finish(&mut self) -> PyResult<PyGraph> {
        let b = take_builder(&mut self.inner)?;
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

// ---------------------------------------------------------------------------
// LabelList / KindFlags
// ---------------------------------------------------------------------------

#[pyclass(name = "LabelList", frozen, from_py_object)]
#[derive(Clone)]
pub struct PyLabelList {
    inner: LabelList,
}

#[pymethods]
impl PyLabelList {
    #[new]
    fn new(labels: Vec<Option<String>>) -> Self {
        Self {
            inner: LabelList::new(labels),
        }
    }

    #[staticmethod]
    fn from_bytes(data: &[u8]) -> PyResult<Self> {
        LabelList::from_bytes(data)
            .map(|inner| Self { inner })
            .map_err(|e| PyValueError::new_err(e.to_string()))
    }

    fn to_bytes<'py>(&self, py: Python<'py>) -> Bound<'py, PyBytes> {
        PyBytes::new(py, &self.inner.to_bytes())
    }

    fn hash<'py>(&self, py: Python<'py>) -> Bound<'py, PyBytes> {
        PyBytes::new(py, self.inner.hash().as_bytes())
    }

    fn __len__(&self) -> usize {
        self.inner.len()
    }

    fn get(&self, i: usize) -> Option<String> {
        self.inner.get(i).map(|s| s.to_string())
    }

    fn __repr__(&self) -> String {
        format!("LabelList(len={})", self.inner.len())
    }
}

#[pyclass(name = "KindFlags", frozen, from_py_object)]
#[derive(Clone)]
pub struct PyKindFlags {
    inner: KindFlags,
}

#[pymethods]
impl PyKindFlags {
    #[new]
    fn new(kinds: Vec<String>) -> PyResult<Self> {
        let parsed: Result<Vec<NodeKind>, _> = kinds.iter().map(|s| parse_node_kind(s)).collect();
        Ok(Self {
            inner: KindFlags::new(parsed?),
        })
    }

    #[staticmethod]
    fn uniform(n: u32, kind: &str) -> PyResult<Self> {
        Ok(Self {
            inner: KindFlags::uniform(n, parse_node_kind(kind)?),
        })
    }

    #[staticmethod]
    fn from_bytes(data: &[u8]) -> PyResult<Self> {
        KindFlags::from_bytes(data)
            .map(|inner| Self { inner })
            .map_err(|e| PyValueError::new_err(e.to_string()))
    }

    fn to_bytes<'py>(&self, py: Python<'py>) -> Bound<'py, PyBytes> {
        PyBytes::new(py, &self.inner.to_bytes())
    }

    fn hash<'py>(&self, py: Python<'py>) -> Bound<'py, PyBytes> {
        PyBytes::new(py, self.inner.hash().as_bytes())
    }

    fn __len__(&self) -> usize {
        self.inner.len()
    }

    fn get(&self, i: usize) -> Option<&'static str> {
        self.inner.get(i).map(|k| k.as_str())
    }

    fn ordered_indices(&self) -> Vec<u32> {
        self.inner.ordered_node_indices().collect()
    }

    fn __repr__(&self) -> String {
        format!("KindFlags(len={})", self.inner.len())
    }
}

// ---------------------------------------------------------------------------
// StringDiagram
// ---------------------------------------------------------------------------

#[pyclass(name = "StringDiagram", frozen, from_py_object)]
#[derive(Clone)]
pub struct PyStringDiagram {
    inner: StringDiagram,
}

#[pymethods]
impl PyStringDiagram {
    /// Build from a graph plus optional overlays. Inline overlay bytes
    /// can be retrieved via `labels_bytes` / `kinds_bytes` to store
    /// alongside the composite.
    #[staticmethod]
    #[pyo3(signature = (graph, labels = None, kinds = None, uniform_kind = None))]
    fn build(
        graph: &PyGraph,
        labels: Option<&PyLabelList>,
        kinds: Option<&PyKindFlags>,
        uniform_kind: Option<&str>,
    ) -> PyResult<Self> {
        let mut b = StringDiagramBuilder::new(&graph.inner);
        if let Some(ll) = labels {
            b = b.with_labels(ll.inner.clone());
        }
        if let Some(kf) = kinds {
            b = b.with_kinds(kf.inner.clone());
        }
        if let Some(uk) = uniform_kind {
            b = b.with_uniform_kind(parse_node_kind(uk)?);
        }
        Ok(Self { inner: b.build() })
    }

    #[staticmethod]
    fn from_bytes(data: &[u8]) -> PyResult<Self> {
        StringDiagram::from_bytes(data)
            .map(|inner| Self { inner })
            .map_err(|e| PyValueError::new_err(e.to_string()))
    }

    fn to_bytes<'py>(&self, py: Python<'py>) -> Bound<'py, PyBytes> {
        PyBytes::new(py, &self.inner.to_bytes())
    }

    fn hash<'py>(&self, py: Python<'py>) -> Bound<'py, PyBytes> {
        PyBytes::new(py, self.inner.hash().as_bytes())
    }

    fn graph_hash<'py>(&self, py: Python<'py>) -> Bound<'py, PyBytes> {
        PyBytes::new(py, self.inner.graph.as_bytes())
    }

    fn labels_slot(&self) -> String {
        slot_repr(self.inner.labels)
    }

    fn kinds_slot(&self) -> String {
        slot_repr(self.inner.kinds)
    }

    /// Render to standalone SVG markup. Inline overlays go through the
    /// same builder logic, so a caller that doesn't have the overlays
    /// stored anywhere can still render.
    #[pyo3(signature = (graph, labels = None, kinds = None))]
    fn render_svg(
        &self,
        graph: &PyGraph,
        labels: Option<&PyLabelList>,
        kinds: Option<&PyKindFlags>,
    ) -> PyResult<String> {
        let mut store = OverlayMap::default();
        if let Some(ll) = labels {
            store.blobs.insert(ll.inner.hash(), ll.inner.to_bytes());
        }
        if let Some(kf) = kinds {
            store.blobs.insert(kf.inner.hash(), kf.inner.to_bytes());
        }
        let resolved: ResolvedDiagram<Bytes> = self
            .inner
            .resolve(&graph.inner, &store)
            .map_err(|e| PyValueError::new_err(e.to_string()))?;
        Ok(render_svg(&resolved, &LayoutOpts::default()))
    }

    fn __repr__(&self) -> String {
        format!(
            "StringDiagram(graph={}, labels={}, kinds={})",
            hex_lower(self.inner.graph.as_bytes()),
            self.labels_slot(),
            self.kinds_slot(),
        )
    }
}

fn slot_repr(s: SlotRef) -> String {
    match s {
        SlotRef::Absent => "absent".into(),
        SlotRef::Uniform(UniformTag::AllPure) => "all-pure".into(),
        SlotRef::Uniform(UniformTag::AllOrdered) => "all-ordered".into(),
        SlotRef::Hash(h) => hex_lower(h.as_bytes()),
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
    m.add_class::<PyLabelList>()?;
    m.add_class::<PyKindFlags>()?;
    m.add_class::<PyStringDiagram>()?;
    Ok(())
}
