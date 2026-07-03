use bytes::Bytes;
use smol_str::SmolStr;

use crate::Atom;
use crate::SExpr;
use crate::dialect::Dialect;
use crate::types::SExp;
use crate::visitor::SExpVisitor;

/// Bottom-up builder for S-expression trees.
pub trait SExpBuilder {
    type Output;

    fn build_atom(&mut self, text: &str) -> Self::Output;
    fn build_string(&mut self, format: &str, bytes: &[u8]) -> Self::Output;
    fn build_quoted_symbol(&mut self, content: &str) -> Self::Output;
    fn build_list(&mut self, children: Vec<Self::Output>) -> Self::Output;
}

/// Default builder that produces `SExpr` values.
pub struct DefaultBuilder;

impl SExpBuilder for DefaultBuilder {
    type Output = SExpr;

    fn build_atom(&mut self, text: &str) -> SExpr {
        SExp::Atom(Atom::Symbol(SmolStr::from(text)))
    }

    fn build_string(&mut self, format: &str, bytes: &[u8]) -> SExpr {
        SExp::Atom(Atom::Str {
            format: SmolStr::from(format),
            bytes: Bytes::copy_from_slice(bytes),
        })
    }

    fn build_quoted_symbol(&mut self, content: &str) -> SExpr {
        SExp::Atom(Atom::Symbol(SmolStr::from(content)))
    }

    fn build_list(&mut self, children: Vec<SExpr>) -> SExpr {
        SExp::List(children)
    }
}

/// Generic tree builder that implements `SExpVisitor` using a `SExpBuilder`
/// for node construction and a `Dialect` for configuration.
pub struct TreeBuilder<B: SExpBuilder, D: Dialect> {
    builder: B,
    dialect: D,
    stack: Vec<Vec<B::Output>>,
}

impl<B: SExpBuilder, D: Dialect> TreeBuilder<B, D> {
    pub fn new(builder: B, dialect: D) -> Self {
        TreeBuilder {
            builder,
            dialect,
            stack: vec![vec![]],
        }
    }

    /// Consume the builder and return the top-level results.
    pub fn into_results(mut self) -> Vec<B::Output> {
        self.stack.pop().unwrap_or_default()
    }
}

impl<B: SExpBuilder, D: Dialect> SExpVisitor for TreeBuilder<B, D> {
    fn parse_trivia(&mut self, input: &mut &str) {
        self.dialect.parse_trivia(input);
    }

    fn quoted_symbol_delim(&self) -> Option<u8> {
        self.dialect.quoted_symbol_delim()
    }

    fn open_list(&mut self) {
        self.stack.push(vec![]);
    }

    fn close_list(&mut self) {
        let children = self.stack.pop().unwrap();
        let node = self.builder.build_list(children);
        self.stack.last_mut().unwrap().push(node);
    }

    fn atom(&mut self, text: &str) {
        let node = self.builder.build_atom(text);
        self.stack.last_mut().unwrap().push(node);
    }

    fn string(&mut self, format: &str, bytes: &[u8]) {
        let node = self.builder.build_string(format, bytes);
        self.stack.last_mut().unwrap().push(node);
    }

    fn quoted_symbol(&mut self, content: &str) {
        let node = self.builder.build_quoted_symbol(content);
        self.stack.last_mut().unwrap().push(node);
    }
}
