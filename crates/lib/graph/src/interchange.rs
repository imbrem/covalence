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
