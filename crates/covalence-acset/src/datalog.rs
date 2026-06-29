//! Recursive (Datalog) queries over an ACSet instance — least-fixpoint
//! evaluation of derived relations.
//!
//! The conjunctive [`query`](crate::query) layer answers a single pattern. This
//! layer adds **derived relations** defined by rules that may reference each
//! other (and themselves), evaluated to a least fixpoint. A [`Rule`] is
//! `head :- body`, where the body conjoins three atom kinds:
//!
//! - **morphism** `hom(a) = b` and **attribute** `attr(v) = value` over the
//!   instance (the EDB), exactly as in a conjunctive query;
//! - **relation** `pred(a, b, …)` referencing a derived relation (the IDB),
//!   which is what enables recursion.
//!
//! Evaluation is naive bottom-up: repeatedly fire every rule against the
//! previous round's relations until nothing new is derived. Because parts are
//! finite, the derivable tuples form a finite lattice under ⊆ and each round is
//! monotone, so the least fixpoint is reached in finitely many rounds.
//!
//! # Where Datafun fits
//!
//! This is the *semantic core* Datafun (Arntzenius & Krishnaswami) denotes: a
//! monotone map on a semilattice (sets of tuples under union) iterated to its
//! least fixpoint. A future Datafun-style surface — monotone functions, set
//! comprehensions, and a `fix` whose **monotonicity is enforced by the type
//! system** — would *compile to* this engine, replacing hand-written [`Rule`]s
//! and guaranteeing the monotonicity this layer currently assumes. See
//! `notes/sketches/acset-datalog-datafun.md`.

use std::collections::{HashMap, HashSet};

use crate::{AttrVal, Instance, Part, Schema};

/// Ways a [`Program`] is ill-formed against a [`Schema`].
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum DatalogError {
    #[error("relation `{rel}` column {col} has undeclared object `{obj}`")]
    UnknownColObject {
        rel: &'static str,
        col: usize,
        obj: &'static str,
    },
    #[error("rule head references undeclared relation `{rel}`")]
    UnknownHeadRelation { rel: &'static str },
    #[error("body references undeclared relation `{rel}`")]
    UnknownBodyRelation { rel: &'static str },
    #[error("relation `{rel}`: expected arity {expected}, got {got}")]
    ArityMismatch {
        rel: &'static str,
        expected: usize,
        got: usize,
    },
    #[error("rule uses unbound variable `{var}`")]
    UnknownVar { var: &'static str },
    #[error("variable `{var}` has undeclared object `{obj}`")]
    UnknownVarObject {
        var: &'static str,
        obj: &'static str,
    },
    #[error("morphism `{hom}` is unknown or ill-typed at variable `{var}`")]
    BadHom {
        hom: &'static str,
        var: &'static str,
    },
    #[error("attribute `{attr}` is unknown or ill-typed at variable `{var}`")]
    BadAttr {
        attr: &'static str,
        var: &'static str,
    },
    #[error("relation `{rel}` column {col} expects `{expected}`, variable `{var}` is `{got}`")]
    ColTypeMismatch {
        rel: &'static str,
        col: usize,
        var: &'static str,
        expected: &'static str,
        got: &'static str,
    },
}

#[derive(Debug, Clone)]
enum Body {
    Hom {
        src: &'static str,
        hom: &'static str,
        dst: &'static str,
    },
    Attr {
        var: &'static str,
        attr: &'static str,
        value: AttrVal,
    },
    Rel {
        rel: &'static str,
        args: Vec<&'static str>,
    },
}

/// A derived-relation declaration: a name and its column object types.
#[derive(Debug, Clone)]
struct Relation {
    name: &'static str,
    cols: Vec<&'static str>,
}

/// A rule `head(args) :- body`.
#[derive(Debug, Clone)]
pub struct Rule {
    vars: Vec<(&'static str, &'static str)>,
    head_rel: &'static str,
    head_args: Vec<&'static str>,
    body: Vec<Body>,
}

/// Fluent builder for a [`Rule`].
#[derive(Debug, Default)]
pub struct RuleBuilder {
    vars: Vec<(&'static str, &'static str)>,
    head_rel: Option<&'static str>,
    head_args: Vec<&'static str>,
    body: Vec<Body>,
}

impl Rule {
    /// Start a new rule.
    pub fn builder() -> RuleBuilder {
        RuleBuilder::default()
    }
    fn object_of(&self, var: &str) -> Option<&'static str> {
        self.vars.iter().find(|(v, _)| *v == var).map(|(_, o)| *o)
    }
}

impl RuleBuilder {
    /// Declare a variable `name` over object `obj`.
    pub fn var(mut self, name: &'static str, obj: &'static str) -> Self {
        self.vars.push((name, obj));
        self
    }
    /// Set the head `rel(args)`.
    pub fn head(mut self, rel: &'static str, args: &[&'static str]) -> Self {
        self.head_rel = Some(rel);
        self.head_args = args.to_vec();
        self
    }
    /// Body atom `hom(src) = dst` (an instance morphism).
    pub fn hom(mut self, src: &'static str, hom: &'static str, dst: &'static str) -> Self {
        self.body.push(Body::Hom { src, hom, dst });
        self
    }
    /// Body atom `attr(var) = value` (an instance attribute).
    pub fn attr_eq(
        mut self,
        var: &'static str,
        attr: &'static str,
        value: impl Into<AttrVal>,
    ) -> Self {
        self.body.push(Body::Attr {
            var,
            attr,
            value: value.into(),
        });
        self
    }
    /// Body atom `rel(args)` (a derived relation — recursion).
    pub fn rel(mut self, rel: &'static str, args: &[&'static str]) -> Self {
        self.body.push(Body::Rel {
            rel,
            args: args.to_vec(),
        });
        self
    }
    /// Finish. Panics if no head was set.
    pub fn build(self) -> Rule {
        Rule {
            vars: self.vars,
            head_rel: self.head_rel.expect("rule needs a head"),
            head_args: self.head_args,
            body: self.body,
        }
    }
}

/// A Datalog program: derived relations + rules.
#[derive(Debug, Clone, Default)]
pub struct Program {
    rels: Vec<Relation>,
    rules: Vec<Rule>,
}

/// Fluent builder for a [`Program`].
#[derive(Debug, Default)]
pub struct ProgramBuilder {
    program: Program,
}

impl Program {
    /// Start a new program.
    pub fn builder() -> ProgramBuilder {
        ProgramBuilder::default()
    }

    fn relation(&self, name: &str) -> Option<&Relation> {
        self.rels.iter().find(|r| r.name == name)
    }

    /// Type-check the program against `schema`.
    pub fn check(&self, schema: &Schema) -> Result<(), Vec<DatalogError>> {
        let mut errs = Vec::new();
        for r in &self.rels {
            for (col, &obj) in r.cols.iter().enumerate() {
                if !schema.objects().contains(&obj) {
                    errs.push(DatalogError::UnknownColObject {
                        rel: r.name,
                        col,
                        obj,
                    });
                }
            }
        }
        for rule in &self.rules {
            for &(var, obj) in &rule.vars {
                if !schema.objects().contains(&obj) {
                    errs.push(DatalogError::UnknownVarObject { var, obj });
                }
            }
            let check_rel = |rel: &'static str,
                             args: &[&'static str],
                             errs: &mut Vec<DatalogError>,
                             head: bool| {
                match self.relation(rel) {
                    None => errs.push(if head {
                        DatalogError::UnknownHeadRelation { rel }
                    } else {
                        DatalogError::UnknownBodyRelation { rel }
                    }),
                    Some(decl) => {
                        if decl.cols.len() != args.len() {
                            errs.push(DatalogError::ArityMismatch {
                                rel,
                                expected: decl.cols.len(),
                                got: args.len(),
                            });
                        } else {
                            for (col, &v) in args.iter().enumerate() {
                                match rule.object_of(v) {
                                    None => errs.push(DatalogError::UnknownVar { var: v }),
                                    Some(vo) if vo != decl.cols[col] => {
                                        errs.push(DatalogError::ColTypeMismatch {
                                            rel,
                                            col,
                                            var: v,
                                            expected: decl.cols[col],
                                            got: vo,
                                        })
                                    }
                                    Some(_) => {}
                                }
                            }
                        }
                    }
                }
            };
            check_rel(rule.head_rel, &rule.head_args, &mut errs, true);
            for atom in &rule.body {
                match atom {
                    Body::Rel { rel, args } => check_rel(rel, args, &mut errs, false),
                    Body::Hom { src, hom, dst } => {
                        match (rule.object_of(src), rule.object_of(dst), schema.hom(hom)) {
                            (Some(so), Some(dobj), Some(h)) if h.dom == so && h.cod == dobj => {}
                            (None, _, _) => errs.push(DatalogError::UnknownVar { var: src }),
                            (_, None, _) => errs.push(DatalogError::UnknownVar { var: dst }),
                            _ => errs.push(DatalogError::BadHom { hom, var: src }),
                        }
                    }
                    Body::Attr { var, attr, .. } => {
                        match (rule.object_of(var), schema.attr(attr)) {
                            (Some(vo), Some(a)) if a.dom == vo => {}
                            (None, _) => errs.push(DatalogError::UnknownVar { var }),
                            _ => errs.push(DatalogError::BadAttr { attr, var }),
                        }
                    }
                }
            }
        }
        if errs.is_empty() { Ok(()) } else { Err(errs) }
    }
}

impl ProgramBuilder {
    /// Declare a derived relation `name` with the given column object types.
    pub fn relation(mut self, name: &'static str, cols: &[&'static str]) -> Self {
        self.program.rels.push(Relation {
            name,
            cols: cols.to_vec(),
        });
        self
    }
    /// Add a rule.
    pub fn rule(mut self, rule: Rule) -> Self {
        self.program.rules.push(rule);
        self
    }
    pub fn build(self) -> Program {
        self.program
    }
}

/// The least-fixpoint extension of every derived relation.
#[derive(Debug, Clone, Default)]
pub struct Solution {
    facts: HashMap<&'static str, HashSet<Vec<Part>>>,
}

impl Solution {
    /// Tuples derived for `rel`.
    pub fn tuples(&self, rel: &str) -> impl Iterator<Item = &Vec<Part>> {
        self.facts.get(rel).into_iter().flat_map(|s| s.iter())
    }
    /// Number of tuples derived for `rel`.
    pub fn len(&self, rel: &str) -> usize {
        self.facts.get(rel).map_or(0, HashSet::len)
    }
    /// Whether `rel` contains `tuple`.
    pub fn contains(&self, rel: &str, tuple: &[Part]) -> bool {
        self.facts.get(rel).is_some_and(|s| s.contains(tuple))
    }
    /// Whether nothing at all was derived.
    pub fn is_empty(&self) -> bool {
        self.facts.values().all(HashSet::is_empty)
    }
}

impl Instance {
    /// Evaluate a Datalog `program` over this instance to its least fixpoint.
    pub fn solve(&self, program: &Program) -> Solution {
        let mut sol = Solution::default();
        for r in &program.rels {
            sol.facts.entry(r.name).or_default();
        }
        loop {
            let mut derived: Vec<(&'static str, Vec<Part>)> = Vec::new();
            for rule in &program.rules {
                let mut bind: HashMap<&'static str, Part> = HashMap::new();
                self.fire(rule, &sol, 0, &mut bind, &mut |b| {
                    let tuple = rule.head_args.iter().map(|v| b[v]).collect();
                    derived.push((rule.head_rel, tuple));
                });
            }
            let mut changed = false;
            for (rel, tuple) in derived {
                if sol.facts.entry(rel).or_default().insert(tuple) {
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        sol
    }

    /// Enumerate body solutions of one rule against the current `sol` (reads the
    /// previous round's relations — naive evaluation).
    fn fire(
        &self,
        rule: &Rule,
        sol: &Solution,
        i: usize,
        bind: &mut HashMap<&'static str, Part>,
        emit: &mut dyn FnMut(&HashMap<&'static str, Part>),
    ) {
        if i == rule.vars.len() {
            emit(bind);
            return;
        }
        let (name, obj) = rule.vars[i];
        // forced-by-morphism candidate (join step), else the whole object
        let forced = rule.body.iter().find_map(|a| match a {
            Body::Hom { src, hom, dst } if *dst == name => {
                bind.get(src).map(|&s| self.hom_image(s, hom))
            }
            _ => None,
        });
        let candidates: Vec<usize> = match forced {
            Some(Some(p)) => vec![p.index],
            Some(None) => vec![],
            None => (0..self.nparts(obj)).collect(),
        };
        for index in candidates {
            bind.insert(name, Part { obj, index });
            if self.body_consistent(rule, sol, bind) {
                self.fire(rule, sol, i + 1, bind, emit);
            }
            bind.remove(name);
        }
    }

    /// Every body atom all of whose variables are bound must hold.
    fn body_consistent(
        &self,
        rule: &Rule,
        sol: &Solution,
        bind: &HashMap<&'static str, Part>,
    ) -> bool {
        for atom in &rule.body {
            match atom {
                Body::Hom { src, hom, dst } => {
                    if let (Some(&s), Some(&d)) = (bind.get(src), bind.get(dst)) {
                        if self.hom_image(s, hom) != Some(d) {
                            return false;
                        }
                    }
                }
                Body::Attr { var, attr, value } => {
                    if let Some(&v) = bind.get(var) {
                        if self.attr_value(v, attr) != Some(value) {
                            return false;
                        }
                    }
                }
                Body::Rel { rel, args } => {
                    if args.iter().all(|a| bind.contains_key(a)) {
                        let tuple: Vec<Part> = args.iter().map(|a| bind[a]).collect();
                        if !sol.contains(rel, &tuple) {
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

    fn graph() -> Schema {
        Schema::builder()
            .object("V")
            .object("E")
            .hom("src", "E", "V")
            .hom("dst", "E", "V")
            .build()
    }

    /// path 0 → 1 → 2 → 3
    fn chain() -> Instance {
        let mut g = Instance::new(graph());
        let vs: Vec<Part> = (0..4).map(|_| g.add_part("V")).collect();
        for w in vs.windows(2) {
            let e = g.add_part("E");
            g.set_hom(e, "src", w[0]);
            g.set_hom(e, "dst", w[1]);
        }
        g
    }

    fn reachability() -> Program {
        Program::builder()
            .relation("edge", &["V", "V"])
            .relation("reach", &["V", "V"])
            // edge(a,b) :- src(e)=a, dst(e)=b
            .rule(
                Rule::builder()
                    .var("e", "E")
                    .var("a", "V")
                    .var("b", "V")
                    .head("edge", &["a", "b"])
                    .hom("e", "src", "a")
                    .hom("e", "dst", "b")
                    .build(),
            )
            // reach(a,b) :- edge(a,b)
            .rule(
                Rule::builder()
                    .var("a", "V")
                    .var("b", "V")
                    .head("reach", &["a", "b"])
                    .rel("edge", &["a", "b"])
                    .build(),
            )
            // reach(a,c) :- edge(a,b), reach(b,c)
            .rule(
                Rule::builder()
                    .var("a", "V")
                    .var("b", "V")
                    .var("c", "V")
                    .head("reach", &["a", "c"])
                    .rel("edge", &["a", "b"])
                    .rel("reach", &["b", "c"])
                    .build(),
            )
            .build()
    }

    #[test]
    fn program_type_checks() {
        assert_eq!(reachability().check(&graph()), Ok(()));
    }

    #[test]
    fn transitive_closure() {
        let g = chain();
        let sol = g.solve(&reachability());
        // 3 direct edges; reach = all ordered pairs i<j in a 4-chain = 6.
        assert_eq!(sol.len("edge"), 3);
        assert_eq!(sol.len("reach"), 6);
        let v = |i| Part { obj: "V", index: i };
        assert!(sol.contains("reach", &[v(0), v(3)])); // transitive
        assert!(!sol.contains("reach", &[v(3), v(0)])); // not backwards
    }

    #[test]
    fn solve_matches_generic_lfp() {
        use crate::lattice::lfp;
        use std::collections::BTreeSet;
        let g = chain();
        let sol = g.solve(&reachability());
        let from_solve: BTreeSet<(usize, usize)> = sol
            .tuples("reach")
            .map(|t| (t[0].index, t[1].index))
            .collect();
        // the same transitive closure, computed by the generic lattice fixpoint
        let edges: BTreeSet<(usize, usize)> = [(0, 1), (1, 2), (2, 3)].into_iter().collect();
        let from_lfp = lfp(|r: &BTreeSet<(usize, usize)>| {
            let mut out = edges.clone();
            for &(a, b) in r {
                for &(c, d) in &edges {
                    if b == c {
                        out.insert((a, d));
                    }
                }
            }
            out
        });
        assert_eq!(from_solve, from_lfp);
    }

    #[test]
    fn ill_typed_program_is_caught() {
        let bad = Program::builder()
            .relation("reach", &["V", "V"])
            .rule(
                Rule::builder()
                    .var("a", "V")
                    .head("reach", &["a", "missing"])
                    .build(),
            )
            .build();
        assert!(bad.check(&graph()).is_err());
    }
}
