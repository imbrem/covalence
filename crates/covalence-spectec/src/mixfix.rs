//! Mixfix operator parser.
//!
//! One specific approach — **precedence-climbing Pratt + multi-fragment
//! operator templates** — written as an example, not as the canonical
//! mixfix implementation for Covalence. The user has their own ideas
//! about mixfix that they'll explore separately; this module exists so
//! that Phase 2c has something to lean on for SpecTec elaboration today,
//! and so that the design space has at least one concrete data point.
//!
//! # Model
//!
//! An [`Op`] is a named operator with a [`Fragment`] sequence:
//!
//! - `Lit(Token)` — a literal token that appears in the source.
//! - `Hole(Precedence)` — an operand slot, parsed recursively with the
//!   given minimum binding power.
//!
//! Examples (precedences chosen arbitrarily for illustration):
//!
//! | Fragments | Reads as | Use |
//! |---|---|---|
//! | `[Lit("not"), Hole(50)]` | `not X` | Prefix unary |
//! | `[Hole(40), Lit("+"), Hole(41)]` | `X + Y` | Left-assoc binary |
//! | `[Hole(0), Lit("|-"), Hole(0), Lit(":"), Hole(0)]` | `X \|- Y : Z` | 3-place mixfix |
//! | `[Hole(60), Lit("*")]` | `X *` | Postfix |
//! | `[Lit("REF"), Hole(99), Hole(99)]` | `REF X Y` | Prefix application |
//!
//! Whether an op is "prefix-like" (starts with a literal) or
//! "infix/postfix-like" (starts with a hole) is determined by the first
//! fragment.
//!
//! # API
//!
//! [`parse_term`] consumes an `&mut &[Spanned]` cursor, an [`OpTable`],
//! a minimum binding power, and a leaf parser callback. It returns a
//! [`Tree`] over whatever the leaf parser produces, or a [`Diagnostic`].
//!
//! Style: pure functions; local `&mut` slice cursors only; no globals,
//! no `unsafe`. Kernel-liftable on the same terms as the rest of
//! `covalence-spectec`.

use crate::source::{Diagnostic, Span};
use crate::token::{Spanned, Token};

pub type Precedence = u16;

/// Operator fragment: either a literal token or an operand hole with a
/// minimum binding power.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Fragment {
    Lit(Token),
    Hole(Precedence),
}

/// Stable identifier into an [`OpTable`].
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct OpId(u32);

/// A named mixfix operator declaration.
#[derive(Clone, Debug)]
pub struct Op {
    pub id: OpId,
    pub name: String,
    pub fragments: Vec<Fragment>,
}

impl Op {
    /// True if this operator starts with a hole (used as infix, postfix,
    /// or mixfix-after-leading-operand).
    pub fn is_left_extending(&self) -> bool {
        matches!(self.fragments.first(), Some(Fragment::Hole(_)))
    }

    /// True if this operator starts with a literal (prefix or closed).
    pub fn is_prefix_or_closed(&self) -> bool {
        matches!(self.fragments.first(), Some(Fragment::Lit(_)))
    }

    /// For left-extending ops: the literal that immediately follows the
    /// leading hole. This is the token the Pratt loop looks for to know
    /// whether to continue extending the LHS.
    pub fn first_lit_after_lead_hole(&self) -> Option<&Token> {
        if !self.is_left_extending() {
            return None;
        }
        match self.fragments.get(1)? {
            Fragment::Lit(t) => Some(t),
            Fragment::Hole(_) => None, // pure prefix isn't possible here
        }
    }

    /// For prefix/closed ops: the leading literal.
    pub fn leading_lit(&self) -> Option<&Token> {
        match self.fragments.first()? {
            Fragment::Lit(t) => Some(t),
            Fragment::Hole(_) => None,
        }
    }

    /// The binding power of the LEFT operand of a left-extending op
    /// (the precedence threshold the Pratt loop compares against).
    /// For prefix/closed ops, this returns the maximum precedence
    /// (they don't compete for LHS extension).
    pub fn left_binding_power(&self) -> Precedence {
        match self.fragments.first() {
            Some(Fragment::Hole(p)) => *p,
            _ => Precedence::MAX,
        }
    }

    /// True if this op is "postfix" — its trailing fragment is the
    /// leading hole's terminator with no further holes (e.g. `_*`).
    pub fn is_postfix(&self) -> bool {
        self.is_left_extending()
            && self
                .fragments
                .iter()
                .skip(1)
                .all(|f| matches!(f, Fragment::Lit(_)))
    }
}

/// Operator table — a flat list of declarations.
///
/// Lookups are O(n) linear scans; the table is small in practice
/// (~hundreds of relations + ~hundreds of constructors in a full WASM
/// spec ingest). Add indices when measurement says it matters.
#[derive(Default, Debug, Clone)]
pub struct OpTable {
    ops: Vec<Op>,
}

impl OpTable {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn add(&mut self, name: impl Into<String>, fragments: Vec<Fragment>) -> OpId {
        let id = OpId(u32::try_from(self.ops.len()).expect("op table size in u32"));
        self.ops.push(Op {
            id,
            name: name.into(),
            fragments,
        });
        id
    }

    pub fn get(&self, id: OpId) -> &Op {
        &self.ops[id.0 as usize]
    }

    pub fn iter(&self) -> impl Iterator<Item = &Op> {
        self.ops.iter()
    }

    /// Find a left-extending op whose first-lit-after-lead-hole matches
    /// `tok` AND whose left binding power is `>= min_prec`. Returns the
    /// first match, so callers should order declarations meaningfully
    /// (longest-match first, higher-precedence first) when ambiguity
    /// matters.
    pub fn find_left_extending(&self, tok: &Token, min_prec: Precedence) -> Option<&Op> {
        self.ops.iter().find(|op| {
            op.first_lit_after_lead_hole() == Some(tok) && op.left_binding_power() >= min_prec
        })
    }

    /// All left-extending ops whose first-lit-after-lead-hole matches
    /// `tok` AND whose left binding power is `>= min_prec`. Sorted
    /// longest-fragment-list first so [`parse_term`] can try the most
    /// specific op (e.g. `T ->_(M) U`) before falling back to a
    /// shorter declaration sharing the same lead literal (e.g. the
    /// short form `T -> U`).
    pub fn find_all_left_extending(&self, tok: &Token, min_prec: Precedence) -> Vec<&Op> {
        let mut out: Vec<&Op> = self
            .ops
            .iter()
            .filter(|op| {
                op.first_lit_after_lead_hole() == Some(tok) && op.left_binding_power() >= min_prec
            })
            .collect();
        out.sort_by(|a, b| b.fragments.len().cmp(&a.fragments.len()));
        out
    }

    /// Find a prefix/closed op whose leading literal matches `tok`.
    pub fn find_prefix(&self, tok: &Token) -> Option<&Op> {
        self.ops.iter().find(|op| op.leading_lit() == Some(tok))
    }

    /// All prefix/closed ops whose leading literal matches `tok`.
    /// Used to enable backtracking when multiple ops share a head
    /// (e.g. `FUNC` declared as both a 0-arg variant case and a
    /// `FUNC arg -> arg` mixfix). `parse_term` tries longer
    /// declarations first and falls back to shorter ones.
    pub fn find_all_prefix(&self, tok: &Token) -> Vec<&Op> {
        let mut out: Vec<&Op> = self
            .ops
            .iter()
            .filter(|op| op.leading_lit() == Some(tok))
            .collect();
        // Longest fragment list first — prefer mixfix consumption,
        // fall back to closed singleton on failure.
        out.sort_by(|a, b| b.fragments.len().cmp(&a.fragments.len()));
        out
    }
}

/// Parse output. Generic over the leaf type produced by the user's leaf
/// parser, so this module stays SpecTec-agnostic.
#[derive(Clone, Debug)]
pub enum Tree<L> {
    Leaf(L),
    /// `App(op, args)` where `args.len()` == number of `Hole` fragments
    /// in `op`'s declaration.
    App(OpId, Vec<Tree<L>>),
}

impl<L> Tree<L> {
    pub fn args(&self) -> &[Tree<L>] {
        match self {
            Tree::Leaf(_) => &[],
            Tree::App(_, args) => args,
        }
    }
}

/// Parse one term. Threads `&mut &[Spanned]` through recursive descent
/// (standard slice-cursor style; the residual slice is the rest of the
/// input after the term).
///
/// Pratt protocol:
///
/// 1. If the next token starts a prefix/closed op, parse that op fully.
///    Otherwise call `leaf` to produce the initial LHS.
/// 2. Repeatedly: if the next token starts a left-extending op with
///    `left_binding_power() >= min_prec`, fold the current LHS into the
///    op as its leading hole and continue building from there.
/// 3. Stop when no in-scope op matches.
///
/// `leaf` is invoked exactly when the parser needs an atomic operand it
/// cannot satisfy from the op table. It receives the cursor and the
/// table (so it can recursively call back into `parse_term` for
/// parenthesised groups, if it wants).
pub fn parse_term<L, F>(
    input: &mut &[Spanned],
    table: &OpTable,
    min_prec: Precedence,
    leaf: &mut F,
) -> Result<Tree<L>, Diagnostic>
where
    L: Clone,
    F: FnMut(&mut &[Spanned], &OpTable) -> Result<Tree<L>, Diagnostic>,
{
    // Step 1: prefix/closed op, or leaf.
    let head = input.first().ok_or_else(|| eof("expected term"))?.clone();
    let candidates = table.find_all_prefix(&head.token);
    let mut lhs: Tree<L> = if !candidates.is_empty() {
        // Try each candidate (longest fragments first), keeping the
        // first that fully parses. Save+restore `input` on failure.
        let saved = *input;
        let mut chosen: Option<Tree<L>> = None;
        let mut last_err: Option<Diagnostic> = None;
        for op in &candidates {
            *input = saved;
            *input = &input[1..]; // consume the leading literal
            match consume_remaining(input, table, op.id, Vec::new(), 1, leaf) {
                Ok(tree) => {
                    chosen = Some(tree);
                    break;
                }
                Err(e) => {
                    last_err = Some(e);
                }
            }
        }
        match chosen {
            Some(t) => t,
            None => {
                *input = saved;
                return Err(last_err.unwrap_or_else(|| eof("no matching prefix op")));
            }
        }
    } else {
        leaf(input, table)?
    };

    // Step 2: Pratt loop for left-extending ops.
    while let Some(next) = input.first() {
        let candidates = table.find_all_left_extending(&next.token, min_prec);
        if candidates.is_empty() {
            break;
        }
        // Try each candidate (longest fragments first) with save+restore
        // semantics — mirrors the prefix-op backtracking above. Lets one
        // lead literal serve multiple declarations (e.g. the long form
        // `T ->_(M) U` and the short form `T -> U` of the instrtype
        // mixfix, both registered under the same op name).
        let saved = *input;
        let mut chosen: Option<Tree<L>> = None;
        let mut last_err: Option<Diagnostic> = None;
        for op in &candidates {
            *input = saved;
            *input = &input[1..]; // consume the matched literal
            let initial_args = vec![lhs.clone()];
            match consume_remaining(input, table, op.id, initial_args, 2, leaf) {
                Ok(tree) => {
                    chosen = Some(tree);
                    break;
                }
                Err(e) => {
                    last_err = Some(e);
                }
            }
        }
        match chosen {
            Some(t) => lhs = t,
            None => {
                *input = saved;
                // No candidate matched. If a single candidate previously
                // would have errored hard, surface that error; otherwise
                // stop extending (the caller can use the LHS as-is).
                if candidates.len() == 1 {
                    return Err(last_err.unwrap_or_else(|| eof("left-extending op failed")));
                }
                break;
            }
        }
    }

    Ok(lhs)
}

/// After we've matched and consumed some prefix of an op's fragments,
/// finish the rest. `args` holds any holes filled so far; `next_idx` is
/// the index of the next fragment in `op.fragments` to consume.
fn consume_remaining<L, F>(
    input: &mut &[Spanned],
    table: &OpTable,
    op_id: OpId,
    mut args: Vec<Tree<L>>,
    next_idx: usize,
    leaf: &mut F,
) -> Result<Tree<L>, Diagnostic>
where
    L: Clone,
    F: FnMut(&mut &[Spanned], &OpTable) -> Result<Tree<L>, Diagnostic>,
{
    let op = table.get(op_id).clone();
    let mut i = next_idx;
    while i < op.fragments.len() {
        match &op.fragments[i] {
            Fragment::Lit(expected) => {
                let span = expect_lit(input, expected)?;
                let _ = span; // span captured only for error messages
            }
            Fragment::Hole(prec) => {
                let sub = parse_term(input, table, *prec, leaf)?;
                args.push(sub);
            }
        }
        i += 1;
    }
    Ok(Tree::App(op_id, args))
}

fn expect_lit(input: &mut &[Spanned], expected: &Token) -> Result<Span, Diagnostic> {
    match input.first() {
        Some(s) if &s.token == expected => {
            let span = s.span;
            *input = &input[1..];
            Ok(span)
        }
        Some(s) => Err(Diagnostic::error(
            s.span,
            format!(
                "expected {} in mixfix operator template, found {}",
                expected.describe(),
                s.token.describe()
            ),
        )),
        None => Err(eof(format!(
            "expected {} in mixfix operator template",
            expected.describe()
        ))),
    }
}

fn eof(msg: impl Into<String>) -> Diagnostic {
    Diagnostic::error(
        Span::new(crate::source::FileId::new(0), u32::MAX, u32::MAX),
        msg,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::source::{FileId, SourceMap};

    // ---------- helpers ----------

    fn fid() -> FileId {
        let mut map = SourceMap::new();
        map.add("<mixfix-test>", "")
    }

    fn t(token: Token) -> Spanned {
        Spanned {
            token,
            span: Span::new(fid(), 0, 0),
        }
    }

    /// Leaf parser: take the next token if it's `Ident` or `Nat`, wrap
    /// as `Tree::Leaf(text)`. Errors otherwise.
    fn leaf_atom(input: &mut &[Spanned], _table: &OpTable) -> Result<Tree<String>, Diagnostic> {
        match input.first() {
            Some(Spanned {
                token: Token::Ident(t),
                ..
            }) => {
                let s = t.clone();
                *input = &input[1..];
                Ok(Tree::Leaf(s))
            }
            Some(Spanned {
                token: Token::Nat(n),
                ..
            }) => {
                let s = n.to_string();
                *input = &input[1..];
                Ok(Tree::Leaf(s))
            }
            Some(s) => Err(Diagnostic::error(
                s.span,
                format!("leaf: cannot start with {}", s.token.describe()),
            )),
            None => Err(eof("leaf: unexpected EOF")),
        }
    }

    fn parse_all(tokens: Vec<Spanned>, table: &OpTable) -> Result<Tree<String>, Diagnostic> {
        let mut input: &[Spanned] = &tokens;
        let tree = parse_term(&mut input, table, 0, &mut leaf_atom)?;
        if !input.is_empty() {
            return Err(eof("leftover input"));
        }
        Ok(tree)
    }

    fn fmt(tree: &Tree<String>, table: &OpTable) -> String {
        match tree {
            Tree::Leaf(s) => s.clone(),
            Tree::App(id, args) => {
                let op = table.get(*id);
                let arg_strs: Vec<String> = args.iter().map(|a| fmt(a, table)).collect();
                format!("{}({})", op.name, arg_strs.join(", "))
            }
        }
    }

    // ---------- single-op cases ----------

    #[test]
    fn just_a_leaf() {
        let table = OpTable::new();
        let tree = parse_all(vec![t(Token::Ident("x".into()))], &table).unwrap();
        assert_eq!(fmt(&tree, &table), "x");
    }

    #[test]
    fn prefix_unary() {
        let mut table = OpTable::new();
        // `not X`
        table.add(
            "not",
            vec![
                Fragment::Lit(Token::Ident("not".into())),
                Fragment::Hole(50),
            ],
        );
        let tree = parse_all(
            vec![t(Token::Ident("not".into())), t(Token::Ident("x".into()))],
            &table,
        )
        .unwrap();
        assert_eq!(fmt(&tree, &table), "not(x)");
    }

    #[test]
    fn infix_binary_left_assoc() {
        let mut table = OpTable::new();
        // `X + Y` with left-assoc (right hole is prec+1)
        table.add(
            "+",
            vec![
                Fragment::Hole(40),
                Fragment::Lit(Token::Plus),
                Fragment::Hole(41),
            ],
        );
        let tree = parse_all(
            vec![
                t(Token::Ident("a".into())),
                t(Token::Plus),
                t(Token::Ident("b".into())),
                t(Token::Plus),
                t(Token::Ident("c".into())),
            ],
            &table,
        )
        .unwrap();
        assert_eq!(fmt(&tree, &table), "+(+(a, b), c)");
    }

    #[test]
    fn infix_binary_right_assoc() {
        let mut table = OpTable::new();
        // `X -> Y` right-assoc (right hole is prec)
        table.add(
            "->",
            vec![
                Fragment::Hole(30),
                Fragment::Lit(Token::Arrow),
                Fragment::Hole(30),
            ],
        );
        let tree = parse_all(
            vec![
                t(Token::Ident("a".into())),
                t(Token::Arrow),
                t(Token::Ident("b".into())),
                t(Token::Arrow),
                t(Token::Ident("c".into())),
            ],
            &table,
        )
        .unwrap();
        assert_eq!(fmt(&tree, &table), "->(a, ->(b, c))");
    }

    #[test]
    fn precedence_climbing() {
        let mut table = OpTable::new();
        // `+` low, `*` high — both left-assoc.
        table.add(
            "+",
            vec![
                Fragment::Hole(40),
                Fragment::Lit(Token::Plus),
                Fragment::Hole(41),
            ],
        );
        table.add(
            "*",
            vec![
                Fragment::Hole(60),
                Fragment::Lit(Token::Star),
                Fragment::Hole(61),
            ],
        );
        let tree = parse_all(
            vec![
                t(Token::Ident("a".into())),
                t(Token::Plus),
                t(Token::Ident("b".into())),
                t(Token::Star),
                t(Token::Ident("c".into())),
            ],
            &table,
        )
        .unwrap();
        assert_eq!(fmt(&tree, &table), "+(a, *(b, c))");
    }

    #[test]
    fn postfix_unary() {
        let mut table = OpTable::new();
        // `X *` (kleene postfix)
        table.add(
            "kleene",
            vec![Fragment::Hole(70), Fragment::Lit(Token::Star)],
        );
        let tree = parse_all(vec![t(Token::Ident("x".into())), t(Token::Star)], &table).unwrap();
        assert_eq!(fmt(&tree, &table), "kleene(x)");
    }

    #[test]
    fn three_place_mixfix() {
        let mut table = OpTable::new();
        // `X |- Y : Z`
        table.add(
            "judge",
            vec![
                Fragment::Hole(0),
                Fragment::Lit(Token::Turnstile),
                Fragment::Hole(0),
                Fragment::Lit(Token::Colon),
                Fragment::Hole(0),
            ],
        );
        let tree = parse_all(
            vec![
                t(Token::Ident("ctx".into())),
                t(Token::Turnstile),
                t(Token::Ident("e".into())),
                t(Token::Colon),
                t(Token::Ident("ty".into())),
            ],
            &table,
        )
        .unwrap();
        assert_eq!(fmt(&tree, &table), "judge(ctx, e, ty)");
    }

    #[test]
    fn mixfix_with_subtype_arrow() {
        let mut table = OpTable::new();
        // `X |- Y <: Z`
        table.add(
            "sub",
            vec![
                Fragment::Hole(0),
                Fragment::Lit(Token::Turnstile),
                Fragment::Hole(0),
                Fragment::Lit(Token::Subtype),
                Fragment::Hole(0),
            ],
        );
        let tree = parse_all(
            vec![
                t(Token::Ident("C".into())),
                t(Token::Turnstile),
                t(Token::Ident("t1".into())),
                t(Token::Subtype),
                t(Token::Ident("t2".into())),
            ],
            &table,
        )
        .unwrap();
        assert_eq!(fmt(&tree, &table), "sub(C, t1, t2)");
    }

    #[test]
    fn prefix_application_two_args() {
        let mut table = OpTable::new();
        // `REF X Y` — multi-arg prefix; high precedences keep operands atomic.
        table.add(
            "REF",
            vec![
                Fragment::Lit(Token::Ident("REF".into())),
                Fragment::Hole(99),
                Fragment::Hole(99),
            ],
        );
        let tree = parse_all(
            vec![
                t(Token::Ident("REF".into())),
                t(Token::Ident("x".into())),
                t(Token::Ident("y".into())),
            ],
            &table,
        )
        .unwrap();
        assert_eq!(fmt(&tree, &table), "REF(x, y)");
    }

    #[test]
    fn missing_literal_in_mixfix_errors() {
        let mut table = OpTable::new();
        table.add(
            "judge",
            vec![
                Fragment::Hole(0),
                Fragment::Lit(Token::Turnstile),
                Fragment::Hole(0),
                Fragment::Lit(Token::Colon),
                Fragment::Hole(0),
            ],
        );
        // `ctx |- e` — missing `: ty` part
        let result = parse_all(
            vec![
                t(Token::Ident("ctx".into())),
                t(Token::Turnstile),
                t(Token::Ident("e".into())),
            ],
            &table,
        );
        assert!(result.is_err(), "expected error for incomplete mixfix");
    }

    #[test]
    fn precedence_blocks_inner_binding() {
        // `X + Y -> Z` should parse as `(X + Y) -> Z` if `->` has lower
        // precedence than `+`, and `X + (Y -> Z)` if higher.
        let mut table = OpTable::new();
        table.add(
            "+",
            vec![
                Fragment::Hole(40),
                Fragment::Lit(Token::Plus),
                Fragment::Hole(41),
            ],
        );
        // `->` higher precedence than `+`.
        table.add(
            "->",
            vec![
                Fragment::Hole(60),
                Fragment::Lit(Token::Arrow),
                Fragment::Hole(60),
            ],
        );
        let tree = parse_all(
            vec![
                t(Token::Ident("a".into())),
                t(Token::Plus),
                t(Token::Ident("b".into())),
                t(Token::Arrow),
                t(Token::Ident("c".into())),
            ],
            &table,
        )
        .unwrap();
        // `b -> c` binds first because `->` has higher precedence.
        assert_eq!(fmt(&tree, &table), "+(a, ->(b, c))");
    }

    #[test]
    fn op_introspection() {
        let mut table = OpTable::new();
        let id = table.add("post", vec![Fragment::Hole(70), Fragment::Lit(Token::Star)]);
        let op = table.get(id);
        assert!(op.is_postfix());
        assert!(op.is_left_extending());
        assert!(!op.is_prefix_or_closed());
        assert_eq!(op.first_lit_after_lead_hole(), Some(&Token::Star));
        assert_eq!(op.leading_lit(), None);
        assert_eq!(op.left_binding_power(), 70);
    }

    #[test]
    fn leftover_input_after_parse() {
        // `parse_term` itself doesn't require EOF; the wrapper does.
        let table = OpTable::new();
        let tokens = vec![t(Token::Ident("x".into())), t(Token::Ident("y".into()))];
        let result = parse_all(tokens, &table);
        assert!(result.is_err(), "expected leftover-input error");
    }
}
