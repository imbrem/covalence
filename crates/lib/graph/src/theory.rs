//! Representation-independent finite graph capabilities and checked evidence.
//!
//! The traits in this module distinguish graph kinds rather than encoding them
//! as flags on one universal representation. They expose finite computational
//! views; theorem-producing interpretations belong in a logic backend.
//! Algorithms may produce [`PathWitness`] and [`TopologicalOrderWitness`], but
//! consumers should accept the corresponding checked certificates.

use core::fmt::Debug;

/// A finite collection of vertices.
pub trait FiniteVertices {
    type Vertex: Clone + Eq + Debug;

    fn vertices(&self) -> Vec<Self::Vertex>;
}

/// A finite undirected simple graph.
pub trait Graph: FiniteVertices {
    fn neighbors(&self, vertex: &Self::Vertex) -> Vec<Self::Vertex>;

    fn adjacent(&self, left: &Self::Vertex, right: &Self::Vertex) -> bool {
        self.neighbors(left).iter().any(|vertex| vertex == right)
    }
}

/// A finite directed simple graph.
pub trait DiGraph: FiniteVertices {
    fn successors(&self, vertex: &Self::Vertex) -> Vec<Self::Vertex>;

    fn has_arc(&self, source: &Self::Vertex, target: &Self::Vertex) -> bool {
        self.successors(source)
            .iter()
            .any(|vertex| vertex == target)
    }
}

/// A finite undirected graph whose parallel edges have identities.
pub trait MultiGraph: FiniteVertices {
    type Edge: Clone + Eq + Debug;

    fn edges(&self) -> Vec<Self::Edge>;
    fn endpoints(&self, edge: &Self::Edge) -> Option<(Self::Vertex, Self::Vertex)>;
}

/// A finite directed graph whose parallel arcs have identities.
pub trait MultiDiGraph: FiniteVertices {
    type Edge: Clone + Eq + Debug;

    fn edges(&self) -> Vec<Self::Edge>;
    fn endpoints(&self, edge: &Self::Edge) -> Option<(Self::Vertex, Self::Vertex)>;
}

/// A finite undirected hypergraph.
pub trait HyperGraph: FiniteVertices {
    type HyperEdge: Clone + Eq + Debug;

    fn hyperedges(&self) -> Vec<Self::HyperEdge>;
    fn incident_vertices(&self, edge: &Self::HyperEdge) -> Vec<Self::Vertex>;
}

/// A finite directed hypergraph with a tail and head for every hyperedge.
pub trait DirectedHyperGraph: FiniteVertices {
    type HyperEdge: Clone + Eq + Debug;

    fn hyperedges(&self) -> Vec<Self::HyperEdge>;
    fn tail(&self, edge: &Self::HyperEdge) -> Vec<Self::Vertex>;
    fn head(&self, edge: &Self::HyperEdge) -> Vec<Self::Vertex>;
}

/// Direction of a port in a port graph.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum PortDirection {
    Input,
    Output,
}

/// A graph with first-class ports and connections between ports.
///
/// Port ordering, typing, and linearity are deliberately backend-specific
/// capabilities rather than properties of every graph.
pub trait PortGraph: FiniteVertices {
    type Port: Clone + Eq + Debug;
    type PortType: Clone + Eq + Debug;
    type Connection: Clone + Eq + Debug;

    fn ports(&self, vertex: &Self::Vertex) -> Vec<Self::Port>;
    fn port_direction(&self, vertex: &Self::Vertex, port: &Self::Port) -> Option<PortDirection>;
    fn port_type(&self, vertex: &Self::Vertex, port: &Self::Port) -> Option<Self::PortType>;
    fn connections(&self) -> Vec<Self::Connection>;
    fn connection_endpoints(
        &self,
        connection: &Self::Connection,
    ) -> Option<((Self::Vertex, Self::Port), (Self::Vertex, Self::Port))>;
}

/// Orthogonal vertex labels.
pub trait VertexLabeled: FiniteVertices {
    type VertexLabel;

    fn vertex_label(&self, vertex: &Self::Vertex) -> Option<&Self::VertexLabel>;
}

/// Orthogonal edge labels for an edge-identified graph.
pub trait EdgeLabeled {
    type Edge;
    type EdgeLabel;

    fn edge_label(&self, edge: &Self::Edge) -> Option<&Self::EdgeLabel>;
}

/// Orthogonal edge weights. No arithmetic or ordering is assumed.
pub trait EdgeWeighted {
    type Edge;
    type Weight;

    fn edge_weight(&self, edge: &Self::Edge) -> Option<&Self::Weight>;
}

/// Owned, finite directed simple graph reference implementation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FiniteDiGraph<V> {
    vertices: Vec<V>,
    arcs: Vec<(V, V)>,
}

impl<V: Clone + Eq + Debug> FiniteDiGraph<V> {
    /// Construct a graph, rejecting duplicate vertices, unknown endpoints, and
    /// parallel arcs.
    pub fn new(vertices: Vec<V>, arcs: Vec<(V, V)>) -> Result<Self, FiniteGraphError<V>> {
        for (index, vertex) in vertices.iter().enumerate() {
            if vertices[..index].contains(vertex) {
                return Err(FiniteGraphError::DuplicateVertex(vertex.clone()));
            }
        }
        for (source, target) in &arcs {
            if !vertices.contains(source) {
                return Err(FiniteGraphError::UnknownVertex(source.clone()));
            }
            if !vertices.contains(target) {
                return Err(FiniteGraphError::UnknownVertex(target.clone()));
            }
        }
        for (index, arc) in arcs.iter().enumerate() {
            if arcs[..index].contains(arc) {
                return Err(FiniteGraphError::DuplicateEdge(arc.clone()));
            }
        }
        Ok(Self { vertices, arcs })
    }

    pub fn arcs(&self) -> &[(V, V)] {
        &self.arcs
    }
}

impl<V: Clone + Eq + Debug> FiniteVertices for FiniteDiGraph<V> {
    type Vertex = V;

    fn vertices(&self) -> Vec<V> {
        self.vertices.clone()
    }
}

impl<V: Clone + Eq + Debug> DiGraph for FiniteDiGraph<V> {
    fn successors(&self, vertex: &V) -> Vec<V> {
        self.arcs
            .iter()
            .filter(|(source, _)| source == vertex)
            .map(|(_, target)| target.clone())
            .collect()
    }
}

/// Owned, finite undirected simple graph reference implementation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FiniteGraph<V> {
    vertices: Vec<V>,
    edges: Vec<(V, V)>,
}

impl<V: Clone + Eq + Debug> FiniteGraph<V> {
    /// Construct an undirected graph. `(a, b)` and `(b, a)` are duplicates.
    pub fn new(vertices: Vec<V>, edges: Vec<(V, V)>) -> Result<Self, FiniteGraphError<V>> {
        let directed = FiniteDiGraph::new(vertices.clone(), edges.clone())?;
        for (index, (left, right)) in edges.iter().enumerate() {
            if edges[..index]
                .iter()
                .any(|(old_left, old_right)| old_left == right && old_right == left)
            {
                return Err(FiniteGraphError::DuplicateEdge((
                    left.clone(),
                    right.clone(),
                )));
            }
        }
        Ok(Self {
            vertices: directed.vertices,
            edges,
        })
    }

    pub fn edges(&self) -> &[(V, V)] {
        &self.edges
    }
}

impl<V: Clone + Eq + Debug> FiniteVertices for FiniteGraph<V> {
    type Vertex = V;

    fn vertices(&self) -> Vec<V> {
        self.vertices.clone()
    }
}

impl<V: Clone + Eq + Debug> Graph for FiniteGraph<V> {
    fn neighbors(&self, vertex: &V) -> Vec<V> {
        self.edges
            .iter()
            .filter_map(|(left, right)| {
                if left == vertex {
                    Some(right.clone())
                } else if right == vertex {
                    Some(left.clone())
                } else {
                    None
                }
            })
            .collect()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FiniteGraphError<V> {
    DuplicateVertex(V),
    UnknownVertex(V),
    DuplicateEdge((V, V)),
}

impl<V: Debug> core::fmt::Display for FiniteGraphError<V> {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl<V: Debug> std::error::Error for FiniteGraphError<V> {}

/// Supplied evidence for a nonempty directed path.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PathWitness<V> {
    pub vertices: Vec<V>,
}

/// Checked positive evidence that every consecutive pair is an arc.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReachabilityCertificate<V> {
    witness: PathWitness<V>,
}

impl<V> ReachabilityCertificate<V> {
    pub fn witness(&self) -> &PathWitness<V> {
        &self.witness
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PathCheckError<V> {
    Empty,
    UnknownVertex(V),
    MissingArc { source: V, target: V },
}

/// Check positive path evidence. This never infers non-reachability from a
/// failed search.
pub fn check_path<G>(
    graph: &G,
    witness: PathWitness<G::Vertex>,
) -> Result<ReachabilityCertificate<G::Vertex>, PathCheckError<G::Vertex>>
where
    G: DiGraph,
{
    if witness.vertices.is_empty() {
        return Err(PathCheckError::Empty);
    }
    let vertices = graph.vertices();
    for vertex in &witness.vertices {
        if !vertices.contains(vertex) {
            return Err(PathCheckError::UnknownVertex(vertex.clone()));
        }
    }
    for pair in witness.vertices.windows(2) {
        if !graph.has_arc(&pair[0], &pair[1]) {
            return Err(PathCheckError::MissingArc {
                source: pair[0].clone(),
                target: pair[1].clone(),
            });
        }
    }
    Ok(ReachabilityCertificate { witness })
}

/// Supplied evidence that a directed graph is acyclic.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TopologicalOrderWitness<V> {
    pub vertices: Vec<V>,
}

/// Checked positive evidence that an order contains every vertex exactly once
/// and places every arc's source before its target.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AcyclicityCertificate<V> {
    witness: TopologicalOrderWitness<V>,
}

impl<V> AcyclicityCertificate<V> {
    pub fn witness(&self) -> &TopologicalOrderWitness<V> {
        &self.witness
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TopologicalOrderCheckError<V> {
    MissingVertex(V),
    DuplicateVertex(V),
    UnknownVertex(V),
    BackwardArc { source: V, target: V },
}

/// Check a topological order without trusting the algorithm that produced it.
pub fn check_topological_order<G>(
    graph: &G,
    witness: TopologicalOrderWitness<G::Vertex>,
) -> Result<AcyclicityCertificate<G::Vertex>, TopologicalOrderCheckError<G::Vertex>>
where
    G: DiGraph,
{
    let graph_vertices = graph.vertices();
    for (index, vertex) in witness.vertices.iter().enumerate() {
        if !graph_vertices.contains(vertex) {
            return Err(TopologicalOrderCheckError::UnknownVertex(vertex.clone()));
        }
        if witness.vertices[..index].contains(vertex) {
            return Err(TopologicalOrderCheckError::DuplicateVertex(vertex.clone()));
        }
    }
    for vertex in &graph_vertices {
        if !witness.vertices.contains(vertex) {
            return Err(TopologicalOrderCheckError::MissingVertex(vertex.clone()));
        }
    }
    for source in &graph_vertices {
        let source_index = witness
            .vertices
            .iter()
            .position(|vertex| vertex == source)
            .expect("membership checked above");
        for target in graph.successors(source) {
            let target_index = witness
                .vertices
                .iter()
                .position(|vertex| vertex == &target)
                .ok_or_else(|| TopologicalOrderCheckError::UnknownVertex(target.clone()))?;
            if source_index >= target_index {
                return Err(TopologicalOrderCheckError::BackwardArc {
                    source: source.clone(),
                    target,
                });
            }
        }
    }
    Ok(AcyclicityCertificate { witness })
}

impl<P> FiniteVertices for crate::Graph<P> {
    type Vertex = crate::NodeId;

    fn vertices(&self) -> Vec<Self::Vertex> {
        (0..self.node_count()).map(crate::NodeId).collect()
    }
}

impl<P> PortGraph for crate::Graph<P> {
    type Port = crate::PortId;
    type PortType = crate::TypeId;
    type Connection = crate::Edge;

    fn ports(&self, vertex: &Self::Vertex) -> Vec<Self::Port> {
        self.get_node(*vertex)
            .map(|node| (0..node.ports.len() as u32).map(crate::PortId).collect())
            .unwrap_or_default()
    }

    fn port_direction(&self, vertex: &Self::Vertex, port: &Self::Port) -> Option<PortDirection> {
        self.get_node(*vertex)?
            .ports
            .get(port.0 as usize)
            .map(|port| match port.kind {
                crate::PortKind::Input => PortDirection::Input,
                crate::PortKind::Output => PortDirection::Output,
            })
    }

    fn port_type(&self, vertex: &Self::Vertex, port: &Self::Port) -> Option<Self::PortType> {
        self.get_node(*vertex)?
            .ports
            .get(port.0 as usize)
            .map(|port| port.type_id)
    }

    fn connections(&self) -> Vec<Self::Connection> {
        self.edges().to_vec()
    }

    fn connection_endpoints(
        &self,
        connection: &Self::Connection,
    ) -> Option<((Self::Vertex, Self::Port), (Self::Vertex, Self::Port))> {
        self.edges().contains(connection).then_some((
            (connection.from_node, connection.from_port),
            (connection.to_node, connection.to_port),
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn checks_path_evidence_edge_by_edge() {
        let graph = FiniteDiGraph::new(vec!['a', 'b', 'c'], vec![('a', 'b'), ('b', 'c')]).unwrap();
        let checked = check_path(
            &graph,
            PathWitness {
                vertices: vec!['a', 'b', 'c'],
            },
        )
        .unwrap();
        assert_eq!(checked.witness().vertices.first(), Some(&'a'));

        assert_eq!(
            check_path(
                &graph,
                PathWitness {
                    vertices: vec!['a', 'c']
                }
            ),
            Err(PathCheckError::MissingArc {
                source: 'a',
                target: 'c'
            })
        );
    }

    #[test]
    fn topological_order_is_a_positive_acyclicity_certificate() {
        let graph = FiniteDiGraph::new(vec![0, 1, 2], vec![(0, 1), (1, 2)]).unwrap();
        check_topological_order(
            &graph,
            TopologicalOrderWitness {
                vertices: vec![0, 1, 2],
            },
        )
        .unwrap();

        assert_eq!(
            check_topological_order(
                &graph,
                TopologicalOrderWitness {
                    vertices: vec![1, 0, 2]
                }
            ),
            Err(TopologicalOrderCheckError::BackwardArc {
                source: 0,
                target: 1
            })
        );
    }

    #[test]
    fn undirected_adjacency_is_symmetric() {
        let graph = FiniteGraph::new(vec![1, 2], vec![(1, 2)]).unwrap();
        assert!(graph.adjacent(&1, &2));
        assert!(graph.adjacent(&2, &1));
    }
}
