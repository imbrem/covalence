//! Text interchange seams for graph representations.
//!
//! Parsing and printing establish facts about syntax.  They do not by
//! themselves prove that an interpreted graph is equal or isomorphic to
//! another graph.  [`GraphIsomorphismWitness`] makes that second obligation
//! explicit and independently checkable.

use core::fmt::Debug;

use crate::theory::{DiGraph, FiniteDiGraph, FiniteGraphError, FiniteVertices};

/// A deterministic text format with a parser and canonical printer.
pub trait TextCodec {
    type Value;
    type Error;

    fn parse(&self, source: &str) -> Result<Self::Value, Self::Error>;
    fn print(&self, value: &Self::Value) -> Result<String, Self::Error>;
}

/// Evidence produced by checking `parse(print(value)) == value`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SyntaxRoundTripWitness<T> {
    value: T,
    canonical_text: String,
}

impl<T> SyntaxRoundTripWitness<T> {
    pub fn value(&self) -> &T {
        &self.value
    }

    pub fn canonical_text(&self) -> &str {
        &self.canonical_text
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SyntaxRoundTripError<E, T> {
    Codec(E),
    Disagreement { expected: T, parsed: T },
}

pub fn check_syntax_round_trip<C>(
    codec: &C,
    value: C::Value,
) -> Result<SyntaxRoundTripWitness<C::Value>, SyntaxRoundTripError<C::Error, C::Value>>
where
    C: TextCodec,
    C::Value: PartialEq + Debug,
{
    let canonical_text = codec.print(&value).map_err(SyntaxRoundTripError::Codec)?;
    let reparsed = codec
        .parse(&canonical_text)
        .map_err(SyntaxRoundTripError::Codec)?;
    if reparsed != value {
        return Err(SyntaxRoundTripError::Disagreement {
            expected: value,
            parsed: reparsed,
        });
    }
    Ok(SyntaxRoundTripWitness {
        value,
        canonical_text,
    })
}

/// A proposed vertex bijection between two finite directed graphs.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GraphIsomorphismWitness<L, R> {
    pub vertices: Vec<(L, R)>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum IsomorphismError<L, R> {
    MissingLeft(L),
    MissingRight(R),
    UnknownLeft(L),
    UnknownRight(R),
    DuplicateLeft(L),
    DuplicateRight(R),
    ArcDisagreement { left: (L, L), right: (R, R) },
}

/// Check a supplied finite directed-graph isomorphism.
///
/// This is computationally checked evidence, not a theorem minted by the TCB.
pub fn check_digraph_isomorphism<L, R>(
    left: &L,
    right: &R,
    witness: GraphIsomorphismWitness<L::Vertex, R::Vertex>,
) -> Result<GraphIsomorphismWitness<L::Vertex, R::Vertex>, IsomorphismError<L::Vertex, R::Vertex>>
where
    L: DiGraph,
    R: DiGraph,
{
    let left_vertices = left.vertices();
    let right_vertices = right.vertices();
    for vertex in &left_vertices {
        if !witness
            .vertices
            .iter()
            .any(|(candidate, _)| candidate == vertex)
        {
            return Err(IsomorphismError::MissingLeft(vertex.clone()));
        }
    }
    for vertex in &right_vertices {
        if !witness
            .vertices
            .iter()
            .any(|(_, candidate)| candidate == vertex)
        {
            return Err(IsomorphismError::MissingRight(vertex.clone()));
        }
    }
    for (index, (left_vertex, right_vertex)) in witness.vertices.iter().enumerate() {
        if !left_vertices.contains(left_vertex) {
            return Err(IsomorphismError::UnknownLeft(left_vertex.clone()));
        }
        if !right_vertices.contains(right_vertex) {
            return Err(IsomorphismError::UnknownRight(right_vertex.clone()));
        }
        if witness.vertices[..index]
            .iter()
            .any(|(candidate, _)| candidate == left_vertex)
        {
            return Err(IsomorphismError::DuplicateLeft(left_vertex.clone()));
        }
        if witness.vertices[..index]
            .iter()
            .any(|(_, candidate)| candidate == right_vertex)
        {
            return Err(IsomorphismError::DuplicateRight(right_vertex.clone()));
        }
    }
    for (left_source, right_source) in &witness.vertices {
        for (left_target, right_target) in &witness.vertices {
            if left.has_arc(left_source, left_target) != right.has_arc(right_source, right_target) {
                return Err(IsomorphismError::ArcDisagreement {
                    left: (left_source.clone(), left_target.clone()),
                    right: (right_source.clone(), right_target.clone()),
                });
            }
        }
    }
    Ok(witness)
}

/// A deliberately bounded, canonical DOT subset.
///
/// It supports `strict digraph`, quoted graph/node identifiers, standalone
/// nodes, directed edges, and no attributes or subgraphs.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DotDiGraph {
    pub strict: bool,
    pub id: Option<String>,
    pub nodes: Vec<String>,
    pub arcs: Vec<(String, String)>,
}

#[derive(Clone, Copy, Debug, Default)]
pub struct DotSubset;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DotError {
    pub offset: usize,
    pub message: &'static str,
}

impl TextCodec for DotSubset {
    type Value = DotDiGraph;
    type Error = DotError;

    fn parse(&self, source: &str) -> Result<DotDiGraph, DotError> {
        let mut parser = DotParser { source, offset: 0 };
        parser.parse()
    }

    fn print(&self, value: &DotDiGraph) -> Result<String, DotError> {
        let mut text = String::new();
        if value.strict {
            text.push_str("strict ");
        }
        text.push_str("digraph");
        if let Some(id) = &value.id {
            text.push(' ');
            push_quoted(&mut text, id);
        }
        text.push_str(" {\n");
        for node in &value.nodes {
            text.push_str("  ");
            push_quoted(&mut text, node);
            text.push_str(";\n");
        }
        for (source, target) in &value.arcs {
            text.push_str("  ");
            push_quoted(&mut text, source);
            text.push_str(" -> ");
            push_quoted(&mut text, target);
            text.push_str(";\n");
        }
        text.push_str("}\n");
        Ok(text)
    }
}

struct DotParser<'a> {
    source: &'a str,
    offset: usize,
}

impl DotParser<'_> {
    fn parse(&mut self) -> Result<DotDiGraph, DotError> {
        self.space();
        let strict = self.keyword("strict");
        self.space();
        self.expect_keyword("digraph")?;
        self.space();
        let id = if self.peek() == Some('"') {
            Some(self.quoted()?)
        } else {
            None
        };
        self.space();
        self.expect('{')?;
        let mut nodes = Vec::new();
        let mut arcs = Vec::new();
        loop {
            self.space();
            if self.take('}') {
                break;
            }
            let source = self.quoted()?;
            self.space();
            if self.source[self.offset..].starts_with("->") {
                self.offset += 2;
                self.space();
                let target = self.quoted()?;
                arcs.push((source, target));
            } else {
                nodes.push(source);
            }
            self.space();
            self.expect(';')?;
        }
        self.space();
        if self.offset != self.source.len() {
            return Err(self.error("trailing input"));
        }
        Ok(DotDiGraph {
            strict,
            id,
            nodes,
            arcs,
        })
    }

    fn quoted(&mut self) -> Result<String, DotError> {
        self.expect('"')?;
        let mut value = String::new();
        while let Some(character) = self.peek() {
            self.offset += character.len_utf8();
            match character {
                '"' => return Ok(value),
                '\\' => {
                    let escaped = self
                        .peek()
                        .ok_or_else(|| self.error("unterminated escape"))?;
                    self.offset += escaped.len_utf8();
                    match escaped {
                        '"' | '\\' => value.push(escaped),
                        'n' => value.push('\n'),
                        _ => return Err(self.error("unsupported escape")),
                    }
                }
                _ => value.push(character),
            }
        }
        Err(self.error("unterminated quoted identifier"))
    }

    fn space(&mut self) {
        while self.peek().is_some_and(char::is_whitespace) {
            self.offset += self.peek().unwrap().len_utf8();
        }
    }

    fn keyword(&mut self, keyword: &str) -> bool {
        if self.source[self.offset..].starts_with(keyword) {
            self.offset += keyword.len();
            true
        } else {
            false
        }
    }

    fn expect_keyword(&mut self, keyword: &str) -> Result<(), DotError> {
        if self.keyword(keyword) {
            Ok(())
        } else {
            Err(self.error("expected keyword"))
        }
    }

    fn expect(&mut self, expected: char) -> Result<(), DotError> {
        if self.take(expected) {
            Ok(())
        } else {
            Err(self.error("unexpected token"))
        }
    }

    fn take(&mut self, expected: char) -> bool {
        if self.peek() == Some(expected) {
            self.offset += expected.len_utf8();
            true
        } else {
            false
        }
    }

    fn peek(&self) -> Option<char> {
        self.source[self.offset..].chars().next()
    }

    fn error(&self, message: &'static str) -> DotError {
        DotError {
            offset: self.offset,
            message,
        }
    }
}

fn push_quoted(output: &mut String, value: &str) {
    output.push('"');
    for character in value.chars() {
        match character {
            '"' => output.push_str("\\\""),
            '\\' => output.push_str("\\\\"),
            '\n' => output.push_str("\\n"),
            _ => output.push(character),
        }
    }
    output.push('"');
}

/// NetworkX-compatible adjacency-list syntax for directed string graphs.
///
/// Each line is `source target...`; `#` starts a comment.  This initial seam
/// deliberately rejects labels containing whitespace or `#`.
#[derive(Clone, Copy, Debug, Default)]
pub struct NetworkxAdjacencyList;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AdjacencyListError {
    InvalidLabel(String),
    Graph(FiniteGraphError<String>),
}

impl TextCodec for NetworkxAdjacencyList {
    type Value = FiniteDiGraph<String>;
    type Error = AdjacencyListError;

    fn parse(&self, source: &str) -> Result<Self::Value, Self::Error> {
        let mut vertices = Vec::new();
        let mut arcs = Vec::new();
        for line in source.lines() {
            let content = line.split_once('#').map_or(line, |(before, _)| before);
            let mut fields = content.split_whitespace();
            let Some(source) = fields.next() else {
                continue;
            };
            insert_once(&mut vertices, source.to_owned());
            for target in fields {
                insert_once(&mut vertices, target.to_owned());
                arcs.push((source.to_owned(), target.to_owned()));
            }
        }
        FiniteDiGraph::new(vertices, arcs).map_err(AdjacencyListError::Graph)
    }

    fn print(&self, graph: &Self::Value) -> Result<String, Self::Error> {
        let mut output = String::new();
        for vertex in graph.vertices() {
            if !valid_adjacency_label(&vertex) {
                return Err(AdjacencyListError::InvalidLabel(vertex));
            }
            output.push_str(&vertex);
            for successor in graph.successors(&vertex) {
                if !valid_adjacency_label(&successor) {
                    return Err(AdjacencyListError::InvalidLabel(successor));
                }
                output.push(' ');
                output.push_str(&successor);
            }
            output.push('\n');
        }
        Ok(output)
    }
}

fn valid_adjacency_label(label: &str) -> bool {
    !label.is_empty() && !label.contains(char::is_whitespace) && !label.contains('#')
}

fn insert_once<T: Eq>(values: &mut Vec<T>, value: T) {
    if !values.contains(&value) {
        values.push(value);
    }
}

/// NetworkX-compatible directed edge-list syntax.
///
/// Each non-comment line contains exactly two whitespace-separated labels.
/// This syntax cannot represent isolated vertices, so the codec's value is a
/// syntax document rather than a graph.  [`interpret_networkx_edge_list`]
/// performs the separate, checked interpretation into a [`FiniteDiGraph`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NetworkxEdgeListDocument {
    pub arcs: Vec<(String, String)>,
}

#[derive(Clone, Copy, Debug, Default)]
pub struct NetworkxEdgeList;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EdgeListError {
    InvalidArity {
        line: usize,
        fields: usize,
    },
    InvalidLabel(String),
    UnrepresentedVertex(String),
    Graph(FiniteGraphError<String>),
    SemanticDisagreement {
        expected: FiniteDiGraph<String>,
        interpreted: FiniteDiGraph<String>,
    },
}

impl TextCodec for NetworkxEdgeList {
    type Value = NetworkxEdgeListDocument;
    type Error = EdgeListError;

    fn parse(&self, source: &str) -> Result<Self::Value, Self::Error> {
        let mut arcs = Vec::new();
        for (line_index, line) in source.lines().enumerate() {
            let content = line.split_once('#').map_or(line, |(before, _)| before);
            let fields: Vec<_> = content.split_whitespace().collect();
            if fields.is_empty() {
                continue;
            }
            if fields.len() != 2 {
                return Err(EdgeListError::InvalidArity {
                    line: line_index + 1,
                    fields: fields.len(),
                });
            }
            arcs.push((fields[0].to_owned(), fields[1].to_owned()));
        }
        Ok(NetworkxEdgeListDocument { arcs })
    }

    fn print(&self, document: &Self::Value) -> Result<String, Self::Error> {
        let mut output = String::new();
        for (source, target) in &document.arcs {
            if !valid_adjacency_label(source) {
                return Err(EdgeListError::InvalidLabel(source.clone()));
            }
            if !valid_adjacency_label(target) {
                return Err(EdgeListError::InvalidLabel(target.clone()));
            }
            output.push_str(source);
            output.push(' ');
            output.push_str(target);
            output.push('\n');
        }
        Ok(output)
    }
}

/// Checked result of interpreting an edge-list document as a directed graph.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EdgeListInterpretationWitness {
    document: NetworkxEdgeListDocument,
    graph: FiniteDiGraph<String>,
}

impl EdgeListInterpretationWitness {
    pub fn document(&self) -> &NetworkxEdgeListDocument {
        &self.document
    }

    pub fn graph(&self) -> &FiniteDiGraph<String> {
        &self.graph
    }
}

/// Interpret edge-list syntax, preserving first-appearance vertex and arc
/// order and rejecting duplicate arcs.
///
/// The returned value witnesses only this computational interpretation. It
/// does not mint a theorem or claim equality with any independently supplied
/// graph.
pub fn interpret_networkx_edge_list(
    document: NetworkxEdgeListDocument,
) -> Result<EdgeListInterpretationWitness, EdgeListError> {
    let mut vertices = Vec::new();
    for (source, target) in &document.arcs {
        insert_once(&mut vertices, source.clone());
        insert_once(&mut vertices, target.clone());
    }
    let graph =
        FiniteDiGraph::new(vertices, document.arcs.clone()).map_err(EdgeListError::Graph)?;
    Ok(EdgeListInterpretationWitness { document, graph })
}

/// Checked evidence that a finite digraph survives edge-list encoding and
/// interpretation without changing its ordered representation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EdgeListSemanticRoundTripWitness {
    graph: FiniteDiGraph<String>,
    document: NetworkxEdgeListDocument,
}

impl EdgeListSemanticRoundTripWitness {
    pub fn graph(&self) -> &FiniteDiGraph<String> {
        &self.graph
    }

    pub fn document(&self) -> &NetworkxEdgeListDocument {
        &self.document
    }
}

/// Check the semantic round trip
/// `graph -> edge-list document -> interpreted graph`.
///
/// Edge-list syntax has no standalone-node form, so isolated vertices are
/// rejected explicitly. Ordered graph representations whose vertex order is
/// not first-appearance order are likewise reported as a disagreement.
pub fn check_networkx_edge_list_semantic_round_trip(
    graph: FiniteDiGraph<String>,
) -> Result<EdgeListSemanticRoundTripWitness, EdgeListError> {
    for vertex in graph.vertices() {
        if !graph
            .arcs()
            .iter()
            .any(|(source, target)| source == &vertex || target == &vertex)
        {
            return Err(EdgeListError::UnrepresentedVertex(vertex));
        }
    }
    let document = NetworkxEdgeListDocument {
        arcs: graph.arcs().to_vec(),
    };
    NetworkxEdgeList.print(&document)?;
    let interpreted = interpret_networkx_edge_list(document.clone())?
        .graph()
        .clone();
    if interpreted != graph {
        return Err(EdgeListError::SemanticDisagreement {
            expected: graph,
            interpreted,
        });
    }
    Ok(EdgeListSemanticRoundTripWitness { graph, document })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn dot_subset_has_checked_syntax_round_trip() {
        let value = DotDiGraph {
            strict: true,
            id: Some("a graph".into()),
            nodes: vec!["isolated".into()],
            arcs: vec![("a".into(), "b\nquoted".into())],
        };
        let witness = check_syntax_round_trip(&DotSubset, value.clone()).unwrap();
        assert_eq!(witness.value(), &value);
        assert!(witness.canonical_text().starts_with("strict digraph"));
    }

    #[test]
    fn networkx_adjacency_list_round_trips() {
        let graph = FiniteDiGraph::new(
            vec!["a".into(), "b".into(), "alone".into()],
            vec![("a".into(), "b".into())],
        )
        .unwrap();
        let witness = check_syntax_round_trip(&NetworkxAdjacencyList, graph.clone()).unwrap();
        assert_eq!(witness.value(), &graph);
    }

    #[test]
    fn networkx_adjacency_list_rejects_ambiguous_labels() {
        let graph = FiniteDiGraph::new(vec!["not one token".into()], vec![]).unwrap();
        assert!(matches!(
            NetworkxAdjacencyList.print(&graph),
            Err(AdjacencyListError::InvalidLabel(_))
        ));
    }

    #[test]
    fn networkx_edge_list_has_checked_syntax_and_semantic_layers() {
        let document = NetworkxEdgeListDocument {
            arcs: vec![
                ("source".into(), "middle".into()),
                ("middle".into(), "target".into()),
            ],
        };
        let syntax = check_syntax_round_trip(&NetworkxEdgeList, document.clone()).unwrap();
        assert_eq!(syntax.value(), &document);

        let interpretation = interpret_networkx_edge_list(document).unwrap();
        assert_eq!(
            interpretation.graph().vertices(),
            vec!["source", "middle", "target"]
        );
        assert_eq!(
            interpretation.graph().arcs(),
            &[
                ("source".into(), "middle".into()),
                ("middle".into(), "target".into())
            ]
        );
    }

    #[test]
    fn networkx_edge_list_accepts_comments_but_prints_canonical_text() {
        let parsed = NetworkxEdgeList
            .parse("# path\na b # first arc\n\n b c\n")
            .unwrap();
        assert_eq!(NetworkxEdgeList.print(&parsed).unwrap(), "a b\nb c\n");
    }

    #[test]
    fn networkx_edge_list_rejects_attributes_at_the_unweighted_layer() {
        assert_eq!(
            NetworkxEdgeList.parse("a b 3.5\n"),
            Err(EdgeListError::InvalidArity { line: 1, fields: 3 })
        );
    }

    #[test]
    fn networkx_edge_list_interpretation_rejects_duplicate_arcs() {
        let document = NetworkxEdgeListDocument {
            arcs: vec![("a".into(), "b".into()), ("a".into(), "b".into())],
        };
        assert!(matches!(
            interpret_networkx_edge_list(document),
            Err(EdgeListError::Graph(FiniteGraphError::DuplicateEdge(_)))
        ));
    }

    #[test]
    fn networkx_edge_list_has_checked_semantic_round_trip() {
        let graph = FiniteDiGraph::new(
            vec!["a".into(), "b".into(), "c".into()],
            vec![("a".into(), "b".into()), ("b".into(), "c".into())],
        )
        .unwrap();
        let witness = check_networkx_edge_list_semantic_round_trip(graph.clone()).unwrap();
        assert_eq!(witness.graph(), &graph);
        assert_eq!(witness.document().arcs, graph.arcs());
    }

    #[test]
    fn networkx_edge_list_reports_unrepresentable_isolated_vertex() {
        let graph = FiniteDiGraph::new(
            vec!["a".into(), "isolated".into()],
            vec![("a".into(), "a".into())],
        )
        .unwrap();
        assert_eq!(
            check_networkx_edge_list_semantic_round_trip(graph),
            Err(EdgeListError::UnrepresentedVertex("isolated".into()))
        );
    }

    #[test]
    fn graph_isomorphism_is_checked_separately_from_text() {
        let left = FiniteDiGraph::new(vec![0, 1], vec![(0, 1)]).unwrap();
        let right =
            FiniteDiGraph::new(vec!["target", "source"], vec![("source", "target")]).unwrap();
        let witness = GraphIsomorphismWitness {
            vertices: vec![(0, "source"), (1, "target")],
        };
        assert!(check_digraph_isomorphism(&left, &right, witness).is_ok());
    }

    #[test]
    fn graph_isomorphism_rejects_arc_disagreement() {
        let left = FiniteDiGraph::new(vec![0, 1], vec![(0, 1)]).unwrap();
        let right = FiniteDiGraph::new(vec!["a", "b"], vec![("b", "a")]).unwrap();
        let witness = GraphIsomorphismWitness {
            vertices: vec![(0, "a"), (1, "b")],
        };
        assert!(matches!(
            check_digraph_isomorphism(&left, &right, witness),
            Err(IsomorphismError::ArcDisagreement { .. })
        ));
    }
}
