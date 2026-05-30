use covalence_sexp::SExpr;

/// A single command in an Alethe proof.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AletheCommand {
    /// `(assume <id> <formula>)`
    Assume { id: String, term: SExpr },

    /// `(step <id> (cl <literals>...) :rule <name> [:premises (<ids>...)]
    ///   [:args (<args>...)] [:discharge (<ids>...)])`
    Step {
        id: String,
        clause: Vec<SExpr>,
        rule: String,
        premises: Vec<String>,
        args: Vec<SExpr>,
        discharge: Vec<String>,
    },

    /// `(anchor :step <id> [:args (<bindings>...)])`
    Anchor { step: String, args: Vec<SExpr> },

    /// `(define-fun <name> (<params>...) <sort> <body>)`
    DefineFun {
        name: String,
        params: Vec<SExpr>,
        sort: SExpr,
        body: SExpr,
    },
}

/// An Alethe proof — a sequence of commands.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AletheProof(Vec<AletheCommand>);

impl AletheProof {
    /// Create a proof from an iterator of commands.
    pub fn new(commands: impl IntoIterator<Item = AletheCommand>) -> Self {
        AletheProof(commands.into_iter().collect())
    }

    /// The commands of this proof.
    pub fn commands(&self) -> &[AletheCommand] {
        &self.0
    }

    /// Number of commands.
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Is the proof empty?
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}
