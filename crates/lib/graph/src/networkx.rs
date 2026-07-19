//! Bounded NetworkX-style text formats.
//!
//! These codecs operate on syntax documents rather than choosing a graph
//! backend. Directed simple and directed multigraph documents are distinct
//! types. Interpretation into a particular graph representation is a separate
//! layer.

use crate::interchange::TextCodec;

/// How labels and weights become whitespace-delimited fields.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum FieldEscaping {
    /// NetworkX-compatible whitespace splitting. Whitespace, `#`, and `\` in
    /// fields are rejected because the source syntax cannot represent them
    /// unambiguously.
    #[default]
    Strict,
    /// A Covalence extension using `\s`, `\t`, `\n`, `\#`, and `\\`.
    ///
    /// This mode round-trips arbitrary nonempty fields but is not accepted by
    /// NetworkX's stock readers without a corresponding preprocessing step.
    Backslash,
}

/// Reusable field layer shared by graph text formats.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct NetworkxFields {
    pub escaping: FieldEscaping,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NetworkxFormatError {
    EmptyField,
    AmbiguousField(String),
    InvalidEscape {
        line: usize,
        escape: Option<char>,
    },
    InvalidArity {
        line: usize,
        expected: &'static str,
        fields: usize,
    },
    InvalidCount {
        line: usize,
        value: String,
    },
    DuplicateSource {
        line: usize,
        source: String,
    },
    DuplicateArc {
        line: usize,
        source: String,
        target: String,
    },
    UnexpectedEnd {
        source: String,
        expected: usize,
        found: usize,
    },
}

impl core::fmt::Display for NetworkxFormatError {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for NetworkxFormatError {}

impl NetworkxFields {
    fn parse_line(&self, line: &str, number: usize) -> Result<Vec<String>, NetworkxFormatError> {
        match self.escaping {
            FieldEscaping::Strict => {
                let fields: Vec<_> = line
                    .split_once('#')
                    .map_or(line, |(before, _)| before)
                    .split_whitespace()
                    .map(str::to_owned)
                    .collect();
                if let Some(field) = fields.iter().find(|field| field.contains('\\')) {
                    return Err(NetworkxFormatError::AmbiguousField(field.clone()));
                }
                Ok(fields)
            }
            FieldEscaping::Backslash => parse_backslash_fields(line, number),
        }
    }

    fn push(&self, output: &mut String, field: &str) -> Result<(), NetworkxFormatError> {
        if field.is_empty() {
            return Err(NetworkxFormatError::EmptyField);
        }
        match self.escaping {
            FieldEscaping::Strict => {
                if field.contains(char::is_whitespace)
                    || field.contains('#')
                    || field.contains('\\')
                {
                    return Err(NetworkxFormatError::AmbiguousField(field.to_owned()));
                }
                output.push_str(field);
            }
            FieldEscaping::Backslash => {
                for character in field.chars() {
                    match character {
                        ' ' => output.push_str("\\s"),
                        '\t' => output.push_str("\\t"),
                        '\n' => output.push_str("\\n"),
                        '#' => output.push_str("\\#"),
                        '\\' => output.push_str("\\\\"),
                        other => output.push(other),
                    }
                }
            }
        }
        Ok(())
    }
}

fn parse_backslash_fields(line: &str, number: usize) -> Result<Vec<String>, NetworkxFormatError> {
    let mut fields = Vec::new();
    let mut field = String::new();
    let mut characters = line.chars();
    while let Some(character) = characters.next() {
        match character {
            '#' => break,
            character if character.is_whitespace() => {
                if !field.is_empty() {
                    fields.push(core::mem::take(&mut field));
                }
            }
            '\\' => {
                let escaped = characters.next();
                match escaped {
                    Some('s') => field.push(' '),
                    Some('t') => field.push('\t'),
                    Some('n') => field.push('\n'),
                    Some('#') => field.push('#'),
                    Some('\\') => field.push('\\'),
                    _ => {
                        return Err(NetworkxFormatError::InvalidEscape {
                            line: number,
                            escape: escaped,
                        });
                    }
                }
            }
            other => field.push(other),
        }
    }
    if !field.is_empty() {
        fields.push(field);
    }
    Ok(fields)
}

/// One arc in a weighted directed-simple-graph edge-list document.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WeightedDiEdge {
    pub source: String,
    pub target: String,
    pub weight: String,
}

/// NetworkX weighted edge-list syntax for a directed simple graph.
///
/// Each line is `source target weight`. Duplicate ordered endpoint pairs are
/// rejected rather than silently interpreted as parallel arcs. Weights remain
/// opaque fields for a later numeric interpretation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WeightedDiEdgeListDocument {
    pub arcs: Vec<WeightedDiEdge>,
}

#[derive(Clone, Copy, Debug, Default)]
pub struct NetworkxWeightedDiEdgeList {
    pub fields: NetworkxFields,
}

impl TextCodec for NetworkxWeightedDiEdgeList {
    type Value = WeightedDiEdgeListDocument;
    type Error = NetworkxFormatError;

    fn parse(&self, source: &str) -> Result<Self::Value, Self::Error> {
        let mut arcs: Vec<WeightedDiEdge> = Vec::new();
        for (index, line) in source.lines().enumerate() {
            let line_number = index + 1;
            let fields = self.fields.parse_line(line, line_number)?;
            if fields.is_empty() {
                continue;
            }
            if fields.len() != 3 {
                return Err(NetworkxFormatError::InvalidArity {
                    line: line_number,
                    expected: "source, target, and weight",
                    fields: fields.len(),
                });
            }
            if arcs
                .iter()
                .any(|arc| arc.source == fields[0] && arc.target == fields[1])
            {
                return Err(NetworkxFormatError::DuplicateArc {
                    line: line_number,
                    source: fields[0].clone(),
                    target: fields[1].clone(),
                });
            }
            arcs.push(WeightedDiEdge {
                source: fields[0].clone(),
                target: fields[1].clone(),
                weight: fields[2].clone(),
            });
        }
        Ok(WeightedDiEdgeListDocument { arcs })
    }

    fn print(&self, document: &Self::Value) -> Result<String, Self::Error> {
        let mut output = String::new();
        for (index, arc) in document.arcs.iter().enumerate() {
            if document.arcs[..index]
                .iter()
                .any(|previous| previous.source == arc.source && previous.target == arc.target)
            {
                return Err(NetworkxFormatError::DuplicateArc {
                    line: index + 1,
                    source: arc.source.clone(),
                    target: arc.target.clone(),
                });
            }
            self.fields.push(&mut output, &arc.source)?;
            output.push(' ');
            self.fields.push(&mut output, &arc.target)?;
            output.push(' ');
            self.fields.push(&mut output, &arc.weight)?;
            output.push('\n');
        }
        Ok(output)
    }
}

/// One parallel arc occurrence in a directed multigraph multiline document.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MultiArc {
    pub target: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MultilineMultiDiAdjacencyRow {
    pub source: String,
    pub arcs: Vec<MultiArc>,
}

/// NetworkX-style multiline adjacency for a directed multigraph.
///
/// A source line is `source count`; exactly `count` following lines contain
/// one `target`. Repeated targets are preserved as distinct, ordinal edge
/// occurrences. Edge-attribute dictionaries are outside this bounded subset;
/// weighted data uses [`NetworkxWeightedDiEdgeList`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MultilineMultiDiAdjacencyDocument {
    pub rows: Vec<MultilineMultiDiAdjacencyRow>,
}

#[derive(Clone, Copy, Debug, Default)]
pub struct NetworkxMultilineMultiDiAdjacency {
    pub fields: NetworkxFields,
}

impl TextCodec for NetworkxMultilineMultiDiAdjacency {
    type Value = MultilineMultiDiAdjacencyDocument;
    type Error = NetworkxFormatError;

    fn parse(&self, source: &str) -> Result<Self::Value, Self::Error> {
        let lines: Vec<_> = source.lines().enumerate().collect();
        let mut cursor = 0;
        let mut rows: Vec<MultilineMultiDiAdjacencyRow> = Vec::new();
        while cursor < lines.len() {
            let (index, line) = lines[cursor];
            cursor += 1;
            let fields = self.fields.parse_line(line, index + 1)?;
            if fields.is_empty() {
                continue;
            }
            if fields.len() != 2 {
                return Err(NetworkxFormatError::InvalidArity {
                    line: index + 1,
                    expected: "source and arc count",
                    fields: fields.len(),
                });
            }
            if rows.iter().any(|row| row.source == fields[0]) {
                return Err(NetworkxFormatError::DuplicateSource {
                    line: index + 1,
                    source: fields[0].clone(),
                });
            }
            let count =
                fields[1]
                    .parse::<usize>()
                    .map_err(|_| NetworkxFormatError::InvalidCount {
                        line: index + 1,
                        value: fields[1].clone(),
                    })?;
            let mut arcs = Vec::with_capacity(count);
            while arcs.len() < count && cursor < lines.len() {
                let (neighbor_index, neighbor_line) = lines[cursor];
                cursor += 1;
                let neighbor = self.fields.parse_line(neighbor_line, neighbor_index + 1)?;
                if neighbor.is_empty() {
                    continue;
                }
                if neighbor.len() != 1 {
                    return Err(NetworkxFormatError::InvalidArity {
                        line: neighbor_index + 1,
                        expected: "one target",
                        fields: neighbor.len(),
                    });
                }
                arcs.push(MultiArc {
                    target: neighbor[0].clone(),
                });
            }
            if arcs.len() != count {
                return Err(NetworkxFormatError::UnexpectedEnd {
                    source: fields[0].clone(),
                    expected: count,
                    found: arcs.len(),
                });
            }
            rows.push(MultilineMultiDiAdjacencyRow {
                source: fields[0].clone(),
                arcs,
            });
        }
        Ok(MultilineMultiDiAdjacencyDocument { rows })
    }

    fn print(&self, document: &Self::Value) -> Result<String, Self::Error> {
        let mut output = String::new();
        for (index, row) in document.rows.iter().enumerate() {
            if document.rows[..index]
                .iter()
                .any(|previous| previous.source == row.source)
            {
                return Err(NetworkxFormatError::DuplicateSource {
                    line: index + 1,
                    source: row.source.clone(),
                });
            }
            self.fields.push(&mut output, &row.source)?;
            output.push(' ');
            output.push_str(&row.arcs.len().to_string());
            output.push('\n');
            for arc in &row.arcs {
                self.fields.push(&mut output, &arc.target)?;
                output.push('\n');
            }
        }
        Ok(output)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::interchange::check_syntax_round_trip;

    #[test]
    fn weighted_diedge_list_round_trips_and_rejects_parallel_arcs() {
        let value = WeightedDiEdgeListDocument {
            arcs: vec![
                WeightedDiEdge {
                    source: "a".into(),
                    target: "b".into(),
                    weight: "2.5".into(),
                },
                WeightedDiEdge {
                    source: "a".into(),
                    target: "c".into(),
                    weight: "-1".into(),
                },
            ],
        };
        let witness =
            check_syntax_round_trip(&NetworkxWeightedDiEdgeList::default(), value.clone()).unwrap();
        assert_eq!(witness.value(), &value);

        assert!(matches!(
            NetworkxWeightedDiEdgeList::default().parse("a b 1\na b 2\n"),
            Err(NetworkxFormatError::DuplicateArc { .. })
        ));
    }

    #[test]
    fn multiline_multidigraph_preserves_parallel_arcs() {
        let value = MultilineMultiDiAdjacencyDocument {
            rows: vec![MultilineMultiDiAdjacencyRow {
                source: "a".into(),
                arcs: vec![
                    MultiArc { target: "b".into() },
                    MultiArc { target: "b".into() },
                ],
            }],
        };
        let witness =
            check_syntax_round_trip(&NetworkxMultilineMultiDiAdjacency::default(), value.clone())
                .unwrap();
        assert_eq!(witness.value(), &value);
    }

    #[test]
    fn multiline_reports_truncation_and_bad_counts() {
        let codec = NetworkxMultilineMultiDiAdjacency::default();
        assert!(matches!(
            codec.parse("a many\n"),
            Err(NetworkxFormatError::InvalidCount { .. })
        ));
        assert_eq!(
            codec.parse("a 2\nb\n"),
            Err(NetworkxFormatError::UnexpectedEnd {
                source: "a".into(),
                expected: 2,
                found: 1,
            })
        );
    }

    #[test]
    fn escaping_policy_is_explicit_and_round_trips() {
        let value = WeightedDiEdgeListDocument {
            arcs: vec![WeightedDiEdge {
                source: "source node".into(),
                target: "hash#target".into(),
                weight: "a\\weight".into(),
            }],
        };
        assert!(matches!(
            NetworkxWeightedDiEdgeList::default().print(&value),
            Err(NetworkxFormatError::AmbiguousField(_))
        ));

        let extended = NetworkxWeightedDiEdgeList {
            fields: NetworkxFields {
                escaping: FieldEscaping::Backslash,
            },
        };
        let witness = check_syntax_round_trip(&extended, value.clone()).unwrap();
        assert_eq!(witness.value(), &value);
        assert_eq!(
            witness.canonical_text(),
            "source\\snode hash\\#target a\\\\weight\n"
        );
    }

    #[test]
    fn malformed_escape_is_source_located() {
        let codec = NetworkxWeightedDiEdgeList {
            fields: NetworkxFields {
                escaping: FieldEscaping::Backslash,
            },
        };
        assert_eq!(
            codec.parse("a b bad\\q\n"),
            Err(NetworkxFormatError::InvalidEscape {
                line: 1,
                escape: Some('q'),
            })
        );
    }
}
