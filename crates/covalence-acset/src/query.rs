//! Conjunctive queries over an ACSet instance.
//!
//! A conjunctive query is a pattern — a set of typed variables plus a
//! *conjunction* of atoms — and an answer is a homomorphism from the pattern
//! into the instance (a variable→[`Part`] assignment satisfying every atom).
//! Two atom kinds are supported:
//!
//! - **morphism** `hom(a) = b` — the foreign key `hom` carries variable `a`'s
//!   binding to variable `b`'s binding;
//! - **attribute** `attr(v) = value` — `v`'s attribute equals a constant.
//!
//! Build with [`Query::builder`]; run with [`Instance::query`]. Evaluation is a
//! backtracking join: a variable forced by an already-bound morphism source is
//! pinned to a single candidate, so chained foreign keys evaluate as joins
//! rather than full cross products. This is the relational / Datalog-flavoured
//! reading of an ACSet instance.

use std::collections::HashMap;

use crate::{AttrVal, Instance, Part, Schema};

/// Ways a [`Query`] is ill-typed against a [`Schema`].
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum QueryError {
    #[error("variable `{var}` has undeclared object `{obj}`")]
    UnknownObject {
        var: &'static str,
        obj: &'static str,
    },
    #[error("atom references unknown variable `{var}`")]
    UnknownVar { var: &'static str },
    #[error("atom uses unknown morphism `{hom}`")]
    UnknownHom { hom: &'static str },
    #[error("atom uses unknown attribute `{attr}`")]
    UnknownAttr { attr: &'static str },
    #[error("morphism `{hom}`: variable `{var}` has object `{got}`, expected `{expected}`")]
    HomTypeMismatch {
        hom: &'static str,
        var: &'static str,
        expected: &'static str,
        got: &'static str,
    },
    #[error("attribute `{attr}`: variable `{var}` has object `{got}`, expected `{expected}`")]
    AttrTypeMismatch {
        attr: &'static str,
        var: &'static str,
        expected: &'static str,
        got: &'static str,
    },
}

#[derive(Debug, Clone)]
enum Atom {
    Hom {
        src: &'static str,
        hom: &'static str,
        dst: &'static str,
    },
    AttrEq {
        var: &'static str,
        attr: &'static str,
        value: AttrVal,
    },
}

/// A conjunctive query: typed variables + a conjunction of atoms.
#[derive(Debug, Clone, Default)]
pub struct Query {
    vars: Vec<(&'static str, &'static str)>, // (variable, object)
    atoms: Vec<Atom>,
}

/// Fluent builder for a [`Query`].
#[derive(Debug, Default)]
pub struct QueryBuilder {
    query: Query,
}

impl Query {
    /// Start a new query.
    pub fn builder() -> QueryBuilder {
        QueryBuilder::default()
    }

    fn object_of(&self, var: &str) -> Option<&'static str> {
        self.vars.iter().find(|(v, _)| *v == var).map(|(_, o)| *o)
    }

    /// Type-check the query against `schema`.
    pub fn check(&self, schema: &Schema) -> Result<(), Vec<QueryError>> {
        let mut errs = Vec::new();
        for &(var, obj) in &self.vars {
            if !schema.objects().contains(&obj) {
                errs.push(QueryError::UnknownObject { var, obj });
            }
        }
        for atom in &self.atoms {
            match atom {
                Atom::Hom { src, hom, dst } => {
                    let (Some(so), Some(dobj)) = (self.object_of(src), self.object_of(dst)) else {
                        errs.push(QueryError::UnknownVar {
                            var: if self.object_of(src).is_none() {
                                src
                            } else {
                                dst
                            },
                        });
                        continue;
                    };
                    match schema.hom(hom) {
                        None => errs.push(QueryError::UnknownHom { hom }),
                        Some(h) => {
                            if h.dom != so {
                                errs.push(QueryError::HomTypeMismatch {
                                    hom,
                                    var: src,
                                    expected: h.dom,
                                    got: so,
                                });
                            }
                            if h.cod != dobj {
                                errs.push(QueryError::HomTypeMismatch {
                                    hom,
                                    var: dst,
                                    expected: h.cod,
                                    got: dobj,
                                });
                            }
                        }
                    }
                }
                Atom::AttrEq { var, attr, .. } => {
                    let Some(vo) = self.object_of(var) else {
                        errs.push(QueryError::UnknownVar { var });
                        continue;
                    };
                    match schema.attr(attr) {
                        None => errs.push(QueryError::UnknownAttr { attr }),
                        Some(a) if a.dom != vo => errs.push(QueryError::AttrTypeMismatch {
                            attr,
                            var,
                            expected: a.dom,
                            got: vo,
                        }),
                        Some(_) => {}
                    }
                }
            }
        }
        if errs.is_empty() { Ok(()) } else { Err(errs) }
    }
}

impl QueryBuilder {
    /// Declare a variable `name` ranging over object `obj`.
    pub fn var(mut self, name: &'static str, obj: &'static str) -> Self {
        self.query.vars.push((name, obj));
        self
    }
    /// Atom `hom(src) = dst`.
    pub fn hom(mut self, src: &'static str, hom: &'static str, dst: &'static str) -> Self {
        self.query.atoms.push(Atom::Hom { src, hom, dst });
        self
    }
    /// Atom `attr(var) = value`.
    pub fn attr_eq(
        mut self,
        var: &'static str,
        attr: &'static str,
        value: impl Into<AttrVal>,
    ) -> Self {
        self.query.atoms.push(Atom::AttrEq {
            var,
            attr,
            value: value.into(),
        });
        self
    }
    pub fn build(self) -> Query {
        self.query
    }
}

/// One answer to a [`Query`]: a binding of each variable to a [`Part`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Match {
    binds: HashMap<&'static str, Part>,
}

impl Match {
    /// The part bound to `var`, if any.
    pub fn get(&self, var: &str) -> Option<Part> {
        self.binds.get(var).copied()
    }
}

impl Instance {
    /// Run a conjunctive `query`, returning every satisfying binding.
    pub fn query(&self, query: &Query) -> Vec<Match> {
        let mut results = Vec::new();
        let mut bind: HashMap<&'static str, Part> = HashMap::new();
        self.search(query, 0, &mut bind, &mut results);
        results
    }

    fn search(
        &self,
        q: &Query,
        i: usize,
        bind: &mut HashMap<&'static str, Part>,
        out: &mut Vec<Match>,
    ) {
        if i == q.vars.len() {
            out.push(Match {
                binds: bind.clone(),
            });
            return;
        }
        let (name, obj) = q.vars[i];

        // Candidate generation: if some morphism atom `hom(src) = name` has `src`
        // already bound, `name` is forced to a single part (a join step);
        // otherwise it ranges over all parts of its object.
        let forced = q.atoms.iter().find_map(|a| match a {
            Atom::Hom { src, hom, dst } if *dst == name => {
                bind.get(src).map(|&s| self.hom_image(s, hom))
            }
            _ => None,
        });
        let candidates: Vec<usize> = match forced {
            Some(Some(p)) => vec![p.index],
            Some(None) => vec![], // forced but undefined → no match
            None => (0..self.nparts(obj)).collect(),
        };

        for index in candidates {
            bind.insert(name, Part { obj, index });
            if self.consistent(q, bind) {
                self.search(q, i + 1, bind, out);
            }
            bind.remove(name);
        }
    }

    /// Every atom all of whose variables are bound must hold.
    fn consistent(&self, q: &Query, bind: &HashMap<&'static str, Part>) -> bool {
        for atom in &q.atoms {
            match atom {
                Atom::Hom { src, hom, dst } => {
                    if let (Some(&s), Some(&d)) = (bind.get(src), bind.get(dst)) {
                        if self.hom_image(s, hom) != Some(d) {
                            return false;
                        }
                    }
                }
                Atom::AttrEq { var, attr, value } => {
                    if let Some(&v) = bind.get(var) {
                        if self.attr_value(v, attr) != Some(value) {
                            return false;
                        }
                    }
                }
            }
        }
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Schema;

    fn schema() -> Schema {
        Schema::builder()
            .object("V")
            .object("E")
            .attr_type("Color")
            .hom("src", "E", "V")
            .hom("dst", "E", "V")
            .attr("color", "V", "Color")
            .build()
    }

    fn diamond() -> Instance {
        // V0 --e0--> V1 --e1--> V2 ; V0 colored "red", others "blue".
        let mut g = Instance::new(schema());
        let v0 = g.add_part("V");
        let v1 = g.add_part("V");
        let v2 = g.add_part("V");
        g.set_attr(v0, "color", "red");
        g.set_attr(v1, "color", "blue");
        g.set_attr(v2, "color", "blue");
        let e0 = g.add_part("E");
        g.set_hom(e0, "src", v0);
        g.set_hom(e0, "dst", v1);
        let e1 = g.add_part("E");
        g.set_hom(e1, "src", v1);
        g.set_hom(e1, "dst", v2);
        g
    }

    #[test]
    fn query_finds_edges_from_red() {
        let g = diamond();
        // find e, a, b with src(e)=a, dst(e)=b, color(a)=red
        let q = Query::builder()
            .var("e", "E")
            .var("a", "V")
            .var("b", "V")
            .hom("e", "src", "a")
            .hom("e", "dst", "b")
            .attr_eq("a", "color", "red")
            .build();
        assert_eq!(q.check(&schema()), Ok(()));
        let answers = g.query(&q);
        assert_eq!(answers.len(), 1);
        assert_eq!(answers[0].get("a"), Some(Part { obj: "V", index: 0 }));
        assert_eq!(answers[0].get("b"), Some(Part { obj: "V", index: 1 }));
    }

    #[test]
    fn query_join_two_hops() {
        let g = diamond();
        // length-2 path a -e0-> b -e1-> c
        let q = Query::builder()
            .var("e0", "E")
            .var("e1", "E")
            .var("a", "V")
            .var("b", "V")
            .var("c", "V")
            .hom("e0", "src", "a")
            .hom("e0", "dst", "b")
            .hom("e1", "src", "b")
            .hom("e1", "dst", "c")
            .build();
        let answers = g.query(&q);
        assert_eq!(answers.len(), 1);
        assert_eq!(answers[0].get("a"), Some(Part { obj: "V", index: 0 }));
        assert_eq!(answers[0].get("c"), Some(Part { obj: "V", index: 2 }));
    }

    #[test]
    fn no_match_returns_empty() {
        let g = diamond();
        let q = Query::builder()
            .var("a", "V")
            .attr_eq("a", "color", "green")
            .build();
        assert!(g.query(&q).is_empty());
    }

    #[test]
    fn ill_typed_query_is_caught() {
        let q = Query::builder()
            .var("a", "V")
            .attr_eq("a", "nope", "x")
            .build();
        assert!(q.check(&schema()).is_err());
    }
}
