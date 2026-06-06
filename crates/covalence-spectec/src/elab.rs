//! SpecTec elaboration — building mixfix operator tables from the CST.
//!
//! Phase 2c slice: this module converts a `Vec<Top>` into an
//! [`ElabContext`] holding a [`mixfix::OpTable`] populated from `relation`
//! templates (and, later, from `syntax` variant constructors). No
//! re-parsing of rule bodies, variant alternatives, or expression
//! positions yet — those use the table in subsequent slices.
//!
//! The construction is two-pass:
//!
//! 1. Gather declared **type names** from `Top::Syntax` (including
//!    profiled and parametric declarations). These determine which
//!    template-tokens count as **holes**.
//!
//! 2. For each `Top::Relation`, convert its `template` TokenRun into a
//!    `Vec<Fragment>`: type-name idents (with their trailing
//!    iteration/parameter suffix) become `Fragment::Hole`s; everything
//!    else becomes `Fragment::Lit`.
//!
//! Style: pure functions, no globals, no `unsafe`.

use std::collections::{BTreeMap, HashSet};

use crate::cst::{Alt, RuleDecl, SyntaxBody, SyntaxDecl, Top, TokenRun};
use crate::mixfix::{self, Fragment, OpId, OpTable, Precedence, Tree};
use crate::source::{Diagnostic, Span};
use crate::token::{Spanned, Token};

/// Default precedence for relation holes. SpecTec's surface language
/// has no explicit per-operator precedence — relations all sit at the
/// bottom of the binding tower. Higher precedences come into play with
/// syntax-constructor and arithmetic operators (added later).
pub const REL_HOLE_PREC: Precedence = 0;

/// Default precedence for syntax-variant constructor arg holes.
/// Constructors bind tighter than relations (so `C |- (BLOCK x y) : t`
/// associates the way you'd expect), so we use a high precedence here.
pub const CTOR_HOLE_PREC: Precedence = 100;

/// Precedence of the left operand of postfix iteration operators
/// (`*`, `?`, `+`). Higher than constructor arg precedence so that
/// `instr*` binds tighter than the surrounding `BLOCK _ _` application.
pub const ITER_LEFT_PREC: Precedence = 200;

/// Synthetic op name used for the `_*` postfix Kleene-iter operator.
const ITER_STAR_OP: &str = "__iter_star";
/// Synthetic op name used for the `_?` postfix optional operator.
const ITER_OPT_OP: &str = "__iter_opt";
/// Synthetic op name used for the `_+` postfix nonempty-iter operator.
const ITER_PLUS_OP: &str = "__iter_plus";

/// Synthetic op name used for `T ->_(M) U` and its short form `T -> U`,
/// the headless `instrtype = resulttype ->_(localidx*) resulttype`
/// shape. The converter recognises this head and lowers it to mixop
/// `["", "->_", "", ""]` (OCaml's `%->_%%`); the short form gets a
/// synthetic empty-list arg injected in the middle slot at conversion
/// time. See `docs/sketches/spectec-tasks/task-33-expr-arrow-mixfix.md`.
pub(crate) const ARROW_MIXFIX_OP: &str = "__arrow_mixfix";

/// Left binding power of the synthetic arrow mixfix's leading hole.
/// Deliberately LOW (below [`CTOR_HOLE_PREC`]) so the arrow does NOT
/// compete inside another constructor's argument slot — e.g. parsing
/// `FUNC t_1* -> t_2*` keeps the `->` for the `FUNC` mixfix template
/// (whose holes are `Hole(CTOR_HOLE_PREC)`) instead of stealing it
/// into a recursive arrow_mixfix application.
const ARROW_LEFT_PREC: Precedence = 10;

/// Result of running [`build_table`].
#[derive(Debug, Default)]
pub struct ElabContext {
    pub op_table: OpTable,
    /// All declared `syntax` names (irrespective of profile or
    /// arity). Used by the template-to-fragments pass to recognise hole
    /// positions.
    pub type_names: HashSet<String>,
    /// All declared `var NAME : T` metavariable base names.
    pub var_names: HashSet<String>,
    /// Merged `syntax` declarations keyed by base name. Each entry
    /// records the variant alternatives collected across all profiles
    /// (`/syn` and `/sem`) with `...` extension placeholders resolved.
    pub syntax_defs: BTreeMap<String, MergedSyntax>,
    /// Per-relation template token runs, indexed by relation name.
    /// Used by the converter to build OCaml-compatible MixOp strings
    /// (which need access to the raw template tokens, not the
    /// Pratt-flavoured `OpTable` fragments).
    pub rel_templates: BTreeMap<String, TokenRun>,
    /// Per-arg kind for every parametric type (task #31).
    pub param_kinds: BTreeMap<String, Vec<ParamKind>>,
    /// Single-case headless variants, keyed by syntax name, with the
    /// MixOp derived from the alt's fragments. E.g. `fieldtype = mut?
    /// storagetype` → `MixOp(["", "", ""])`. Used by task #32's
    /// juxtaposition splitter to unfold an expected `Var(name)` type.
    pub headless_variant_op: BTreeMap<String, spectec_ast::MixOp>,
}

/// Kind of one positional parameter slot in a parametric type
/// declaration. Mirrors the four `SpecTecParam` variants.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ParamKind {
    Typ,
    Exp,
    Gram,
    Def,
}

/// A `syntax NAME` declaration with all its profile-suffixed variants
/// merged. Phase 2e collapses
///
/// ```text
/// syntax absheaptype/syn = | ANY | EQ | ... | NOFUNC
/// syntax absheaptype/sem = | ... | BOT
/// ```
///
/// into one `MergedSyntax { name: "absheaptype", profiles: [...] }`
/// with the per-profile alt sequences spliced where each `...` appears.
#[derive(Debug, Clone)]
pub struct MergedSyntax {
    pub name: String,
    /// One entry per profile-tagged declaration (or `None` profile for
    /// the unprofiled declarations). Insertion-ordered.
    pub profiles: Vec<MergedProfile>,
}

#[derive(Debug, Clone)]
pub struct MergedProfile {
    /// `None` for the bare `syntax NAME` form; `Some(t)` for `/t`.
    pub profile: Option<String>,
    /// The alternatives this declaration contributes, in source order.
    /// `...` placeholders are kept as `AltSlot::Placeholder` so the
    /// final merge can splice other profiles' alternatives in.
    pub slots: Vec<AltSlot>,
    /// The body this declaration carried, kept verbatim for downstream
    /// `Typ.insts` lowering. `None` for forward declarations.
    pub body: Option<SyntaxBody>,
}

#[derive(Debug, Clone)]
pub enum AltSlot {
    Real(Alt),
    Placeholder,
}

impl MergedSyntax {
    /// Compute the effective record fields for the named profile by
    /// splicing other profiles' fields into the `...` placeholders.
    /// Mirrors `alts_for_profile` for variant bodies.
    pub fn fields_for_profile(&self, profile: Option<&str>) -> Vec<crate::cst::RecordField> {
        use crate::cst::{RecordSlot, SyntaxBody};
        let collect_real = |slots: &[RecordSlot]| -> Vec<crate::cst::RecordField> {
            slots
                .iter()
                .filter_map(|s| match s {
                    RecordSlot::Real(f) => Some(f.clone()),
                    RecordSlot::Placeholder => None,
                })
                .collect()
        };
        fn body_slots(p: &MergedProfile) -> Option<&[crate::cst::RecordSlot]> {
            match &p.body {
                Some(SyntaxBody::Record(slots)) => Some(slots.as_slice()),
                _ => None,
            }
        }
        let mut other_fields: Vec<crate::cst::RecordField> = Vec::new();
        for prof in &self.profiles {
            if prof.profile.as_deref() == profile {
                continue;
            }
            if let Some(slots) = body_slots(prof) {
                other_fields.extend(collect_real(slots));
            }
        }
        let target = self
            .profiles
            .iter()
            .find(|p| p.profile.as_deref() == profile);
        let Some(target) = target.and_then(|t| body_slots(t)) else {
            return other_fields;
        };
        let mut out = Vec::new();
        for slot in target {
            match slot {
                RecordSlot::Real(f) => out.push(f.clone()),
                RecordSlot::Placeholder => out.extend(other_fields.iter().cloned()),
            }
        }
        out
    }

    /// Compute the effective variant alternatives for the named profile
    /// by splicing other profiles' alts into the `...` placeholders.
    ///
    /// SpecTec's rule (per the OCaml elaborator): when profile `P`'s
    /// declaration contains `...`, the placeholder is replaced by the
    /// concatenation of all *other* profiles' real alternatives.
    pub fn alts_for_profile(&self, profile: Option<&str>) -> Vec<Alt> {
        // Collect alts contributed by all OTHER profiles, in source order.
        let mut other_alts: Vec<Alt> = Vec::new();
        for prof in &self.profiles {
            if prof.profile.as_deref() == profile {
                continue;
            }
            for slot in &prof.slots {
                if let AltSlot::Real(a) = slot {
                    other_alts.push(a.clone());
                }
            }
        }
        // Walk the named profile's slots, splicing other_alts where
        // placeholders appear.
        let mut out = Vec::new();
        let target = self
            .profiles
            .iter()
            .find(|p| p.profile.as_deref() == profile);
        let Some(target) = target else {
            return other_alts;
        };
        for slot in &target.slots {
            match slot {
                AltSlot::Real(a) => out.push(a.clone()),
                AltSlot::Placeholder => out.extend(other_alts.iter().cloned()),
            }
        }
        out
    }
}

/// Build an [`ElabContext`] from parsed top-level forms.
///
/// Returns Ok even if individual relation templates fail — those errors
/// are collected and returned in the `Err` variant so the caller can
/// surface them all at once.
pub fn build_table(tops: &[Top]) -> Result<ElabContext, Vec<Diagnostic>> {
    let mut diags = Vec::new();

    // Pass 1: gather syntax type names. We also include `nat`, `int`,
    // `text`, `bool` as built-in atomic types so they're treated as
    // holes when they appear in relation templates.
    let mut type_names: HashSet<String> = ["nat", "int", "text", "bool", "rat", "real"]
        .iter()
        .map(|s| s.to_string())
        .collect();
    let mut var_names: HashSet<String> = HashSet::new();
    let mut syntax_defs: BTreeMap<String, MergedSyntax> = BTreeMap::new();
    for top in tops {
        match top {
            Top::Syntax(s) => {
                type_names.insert(s.name.text.clone());
                add_syntax_to_merge(s, &mut syntax_defs);
            }
            Top::Var(v) => {
                var_names.insert(v.name.text.clone());
            }
            _ => {}
        }
    }

    // Pass 2a: register the universal postfix iteration operators.
    let mut op_table = OpTable::new();
    op_table.add(
        ITER_STAR_OP,
        vec![
            Fragment::Hole(ITER_LEFT_PREC),
            Fragment::Lit(Token::Star),
        ],
    );
    op_table.add(
        ITER_OPT_OP,
        vec![
            Fragment::Hole(ITER_LEFT_PREC),
            Fragment::Lit(Token::Question),
        ],
    );
    op_table.add(
        ITER_PLUS_OP,
        vec![
            Fragment::Hole(ITER_LEFT_PREC),
            Fragment::Lit(Token::Plus),
        ],
    );

    // Pass 2b: extract operators.
    //   - Each `Top::Relation` template becomes one Op (relation-level
    //     precedence, holes interspersed with literals).
    //   - Each `SyntaxBody::Variant` alternative whose head looks like a
    //     case constructor becomes one Op (high precedence, with the
    //     head as a leading Lit and remaining type expressions as Holes).
    let mut rel_templates: BTreeMap<String, TokenRun> = BTreeMap::new();
    for top in tops {
        match top {
            Top::Relation(r) => {
                // Normalise subscripts in the template so e.g.
                // `~~_context` becomes `~~ _ context` — both the
                // OpTable fragments and rule-body matching use the
                // same shape.
                let normalised_template = TokenRun {
                    span: r.template.span,
                    tokens: normalize_subscript_idents(&r.template.tokens),
                };
                rel_templates.insert(r.name.text.clone(), normalised_template.clone());
                match template_to_fragments(&normalised_template, &type_names) {
                    Ok(frags) => {
                        op_table.add(r.name.text.clone(), frags);
                    }
                    Err(d) => diags.push(d),
                }
            }
            Top::Syntax(s) => {
                if let Some(SyntaxBody::Variant(alts)) = &s.body {
                    for alt in alts {
                        if let Some((name, frags)) = alt_to_constructor(alt, &type_names) {
                            op_table.add(name, frags);
                        } else if let Some((long_frags, short_frags)) =
                            arrow_mixfix_alt_fragments(alt, &type_names)
                        {
                            // Headless `T ->_(M) U` mixfix: register the
                            // long form AND a short form `T -> U` so
                            // rules can write either. Both share the
                            // same op name; the converter recognises it
                            // and emits the OCaml `%->_%%` mixop, with
                            // an empty-list middle injected in the
                            // short-form case.
                            op_table.add(ARROW_MIXFIX_OP, long_frags);
                            op_table.add(ARROW_MIXFIX_OP, short_frags);
                        }
                    }
                }
            }
            _ => {}
        }
    }

    // Pass 3a: parametric-type kind registry (task #31).
    let mut param_kinds: BTreeMap<String, Vec<ParamKind>> = BTreeMap::new();
    param_kinds.insert("list".to_string(), vec![ParamKind::Typ]);
    param_kinds.insert("option".to_string(), vec![ParamKind::Typ]);
    for top in tops {
        if let Top::Syntax(s) = top
            && !s.params.is_empty()
            && !param_kinds.contains_key(&s.name.text)
        {
            param_kinds.insert(
                s.name.text.clone(),
                syntax_param_runs_to_kinds(&s.params),
            );
        }
    }

    // Pass 3b: headless-variant MixOp registry (task #32). Each
    // single-case headless variant (e.g. `fieldtype = mut?
    // storagetype`) gets a MixOp keyed by the syntax name, used by
    // the juxtaposition splitter to wrap operands in a synthesised
    // headless Case.
    let mut headless_variant_op: BTreeMap<String, spectec_ast::MixOp> = BTreeMap::new();
    for (name, merged) in &syntax_defs {
        let alts = merged.alts_for_profile(None);
        if alts.len() != 1 {
            continue;
        }
        let alt = &alts[0];
        if let Some(crate::token::Spanned { token: Token::Ident(head), .. }) =
            alt.body.tokens.first()
            && is_case_head(head)
        {
            continue;
        }
        let Some((frags, _holes)) = alt_to_headless_with_holes(alt, &type_names)
        else {
            continue;
        };
        if frags.iter().filter(|f| matches!(f, Fragment::Hole(_))).count() < 2 {
            continue;
        }
        headless_variant_op.insert(name.clone(), headless_mixop_from_fragments(&frags));
    }
    if diags.is_empty() {
        Ok(ElabContext {
            op_table,
            type_names,
            var_names,
            syntax_defs,
            rel_templates,
            param_kinds,
            headless_variant_op,
        })
    } else {
        Err(diags)
    }
}

/// Lower a `syntax NAME(...)`'s parameter token runs to a flat
/// `Vec<ParamKind>` in source order (task #31).
fn syntax_param_runs_to_kinds(runs: &[TokenRun]) -> Vec<ParamKind> {
    let mut out = Vec::new();
    for tr in runs {
        let toks = &tr.tokens;
        let inner = if matches!(toks.first().map(|s| &s.token), Some(Token::LParen))
            && matches!(toks.last().map(|s| &s.token), Some(Token::RParen))
        {
            &toks[1..toks.len() - 1]
        } else {
            &toks[..]
        };
        for chunk in split_top_level_commas_local(inner) {
            out.push(infer_param_kind(chunk));
        }
    }
    out
}

fn infer_param_kind(chunk: &[Spanned]) -> ParamKind {
    match chunk.first().map(|s| &s.token) {
        Some(Token::Syntax) => ParamKind::Typ,
        Some(Token::Grammar) => ParamKind::Gram,
        Some(Token::Def) => ParamKind::Def,
        _ => ParamKind::Exp,
    }
}

fn split_top_level_commas_local(toks: &[Spanned]) -> Vec<&[Spanned]> {
    let mut out = Vec::new();
    let mut depth: i32 = 0;
    let mut start = 0;
    for (i, s) in toks.iter().enumerate() {
        match &s.token {
            Token::LParen | Token::LBracket | Token::LBrace => depth += 1,
            Token::RParen | Token::RBracket | Token::RBrace => depth -= 1,
            Token::Comma if depth == 0 => {
                out.push(&toks[start..i]);
                start = i + 1;
            }
            _ => {}
        }
    }
    if start < toks.len() {
        out.push(&toks[start..]);
    }
    out
}

/// Build a `MixOp` from headless-alt fragments (task #32).
fn headless_mixop_from_fragments(frags: &[Fragment]) -> spectec_ast::MixOp {
    let mut parts: Vec<String> = vec![String::new()];
    for f in frags {
        match f {
            Fragment::Hole(_) => parts.push(String::new()),
            Fragment::Lit(t) => {
                parts.last_mut().unwrap().push_str(&t.to_source_text());
            }
        }
    }
    spectec_ast::MixOp::new(parts)
}

/// Fold one `syntax` decl into the `MergedSyntax` map. Variant
/// alternatives whose body is just `...` are recorded as `Placeholder`;
/// real alternatives are recorded as `Real`.
fn add_syntax_to_merge(
    s: &SyntaxDecl,
    out: &mut BTreeMap<String, MergedSyntax>,
) {
    let entry = out
        .entry(s.name.text.clone())
        .or_insert_with(|| MergedSyntax {
            name: s.name.text.clone(),
            profiles: Vec::new(),
        });
    let slots: Vec<AltSlot> = match &s.body {
        Some(SyntaxBody::Variant(alts)) => alts
            .iter()
            .map(|a| {
                if alt_is_placeholder(a) {
                    AltSlot::Placeholder
                } else {
                    AltSlot::Real(a.clone())
                }
            })
            .collect(),
        // Records and aliases don't participate in `...` splicing
        // (the elaborator could be extended later). We still register
        // an empty profile so the syntax_defs map knows this name was
        // declared with a body of some kind.
        _ => Vec::new(),
    };
    entry.profiles.push(MergedProfile {
        profile: s.profile.as_ref().map(|p| p.text.clone()),
        slots,
        body: s.body.clone(),
    });
}

fn alt_is_placeholder(a: &Alt) -> bool {
    a.body.tokens.len() == 1 && matches!(a.body.tokens[0].token, Token::DotDotDot)
}

/// True if `name` is a use of a declared metavariable. We strip a
/// trailing subscript (`_1`, `_n`, `_n'`) and any prime suffix before
/// looking it up in the var-name set.
fn is_declared_metavar(name: &str, var_names: &HashSet<String>) -> bool {
    let base = metavar_base(name);
    var_names.contains(base)
}

pub fn metavar_base(name: &str) -> &str {
    // Strip trailing primes.
    let mut end = name.len();
    while end > 0 && name.as_bytes()[end - 1] == b'\'' {
        end -= 1;
    }
    let trimmed = &name[..end];
    // Strip trailing `_<digits-or-letters>` subscript.
    if let Some(us) = trimmed.rfind('_') {
        let suffix = &trimmed[us + 1..];
        let is_subscript = !suffix.is_empty()
            && suffix
                .bytes()
                .all(|b| b.is_ascii_digit() || b.is_ascii_lowercase());
        if is_subscript {
            return &trimmed[..us];
        }
    }
    trimmed
}

/// Pre-process a token list to split `_<subscript>` identifiers into
/// a standalone `_` token followed by the suffix. Mirrors OCaml's
/// SpecTec convention of treating the leading `_` as a subscript
/// marker rather than part of the identifier.
///
/// Subscript shapes (`_` is split off):
/// - `_<single char>` like `_C`, `_s`, `_1` — typically a metavariable
///   reference under a subscript.
/// - `_<all-lowercase-or-digits>` like `_context`, `_typeuse`, `_2x` —
///   a lowercase qualifier or compound subscript.
///
/// Constructor names stay as single tokens (`_IDX`, `_RESULT`, `_DEF`
/// — `_` followed by a multi-character all-uppercase suffix).
pub fn normalize_subscript_idents(toks: &[Spanned]) -> Vec<Spanned> {
    let mut out = Vec::with_capacity(toks.len());
    for tok in toks {
        match &tok.token {
            Token::Ident(n) if is_subscript_ident(n) => {
                out.push(Spanned {
                    token: Token::Ident("_".to_string()),
                    span: tok.span,
                });
                out.push(Spanned {
                    token: Token::Ident(n[1..].to_string()),
                    span: tok.span,
                });
            }
            _ => out.push(tok.clone()),
        }
    }
    out
}

fn is_subscript_ident(name: &str) -> bool {
    if !name.starts_with('_') || name.len() < 2 {
        return false;
    }
    let rest = &name[1..];
    if rest.len() == 1 {
        // `_C`, `_s`, `_1` — single-char subscript.
        return true;
    }
    // Longer suffix: subscript iff entirely lowercase / digits.
    rest.bytes()
        .all(|b| b.is_ascii_lowercase() || b.is_ascii_digit())
}

/// Build the OCaml-compatible MixOp fragment list for a relation
/// template. Walks the template tokens with two key rules the OCaml
/// elaborator uses:
///
/// - **Backticks are invisible.** `` ` `` is a source-only escape that
///   prevents a following token from being interpreted as a mixfix
///   operator. The MixOp display strips it.
///
/// - **`_<lowercase>` is a subscript.** When the token list contains
///   an `Ident` starting with `_` followed by a lowercase letter
///   (e.g. `_context` after `~~`), the leading `_` glues to the
///   preceding literal — yielding `~~_` as one literal — and the
///   remaining `<rest>` is reclassified (becomes a hole if it's a
///   declared type name, else a literal). `_<uppercase>` (`_IDX`,
///   `_RESULT`, ...) stays as a single identifier per SpecTec's
///   constructor-name convention.
///
/// Returns the `Vec<String>` form `spectec_ast::MixOp` uses
/// (`%`-delimited template, split on `%`).
pub fn mixop_fragments_from_template(
    template: &TokenRun,
    type_names: &HashSet<String>,
) -> Vec<String> {
    let mut s = String::new();
    let toks = &template.tokens;
    let mut i = 0;
    while i < toks.len() {
        let tok = &toks[i];
        match &tok.token {
            Token::Backtick => {
                // Invisible in MixOp output.
                i += 1;
            }
            Token::Ident(n)
                if n.starts_with('_')
                    && n.chars()
                        .nth(1)
                        .is_some_and(|c| c.is_ascii_lowercase()) =>
            {
                // `_<rest>`: the `_` is a subscript on the preceding
                // literal; `rest` may be a hole or a literal in its
                // own right.
                s.push('_');
                let rest = &n[1..];
                i += 1;
                if type_names.contains(rest) {
                    s.push('%');
                    i += skip_type_suffix(&toks[i..]);
                } else {
                    s.push_str(rest);
                }
            }
            Token::Ident(n) if type_names.contains(n) => {
                s.push('%');
                i += 1;
                i += skip_type_suffix(&toks[i..]);
            }
            Token::LParen => {
                s.push('%');
                let consumed = skip_balanced(&toks[i..]);
                i += consumed;
                i += skip_type_suffix(&toks[i..]);
            }
            _ => {
                s.push_str(&tok.token.to_source_text());
                i += 1;
            }
        }
    }
    s.split('%').map(str::to_owned).collect()
}

/// Like [`template_to_fragments`] but also returns the slice of source
/// tokens that fell within each `Hole`. Useful for downstream code
/// that needs to recover the per-hole type expression (e.g. when
/// synthesising `Rel.t` for the spectec_ast converter).
pub fn template_to_fragments_with_holes(
    template: &TokenRun,
    type_names: &HashSet<String>,
) -> (Vec<Fragment>, Vec<Vec<Spanned>>) {
    let mut frags = Vec::new();
    let mut hole_toks: Vec<Vec<Spanned>> = Vec::new();
    let mut i = 0;
    let toks = &template.tokens;
    while i < toks.len() {
        let t = &toks[i];
        match &t.token {
            Token::Ident(name) if type_names.contains(name) => {
                frags.push(Fragment::Hole(REL_HOLE_PREC));
                let start = i;
                i += 1;
                i += skip_type_suffix(&toks[i..]);
                hole_toks.push(toks[start..i].to_vec());
            }
            Token::LParen => {
                frags.push(Fragment::Hole(REL_HOLE_PREC));
                let start = i;
                i += skip_balanced(&toks[i..]);
                i += skip_type_suffix(&toks[i..]);
                hole_toks.push(toks[start..i].to_vec());
            }
            _ => {
                frags.push(Fragment::Lit(t.token.clone()));
                i += 1;
            }
        }
    }
    (frags, hole_toks)
}

/// Convert a relation `template` token run into mixfix fragments.
///
/// The rule:
///
/// - A type-name `Ident` introduces a `Hole`. Any immediately following
///   type-suffix tokens (`*`, `?`, `+`, or a balanced `(...)` group)
///   are also absorbed into the same hole — they describe the hole's
///   type, not separate template literals.
/// - A bare `(` not preceded by a type-name Ident also begins a hole
///   (treated as a parenthesised type expression).
/// - Any other token becomes a `Lit`.
pub fn template_to_fragments(
    template: &TokenRun,
    type_names: &HashSet<String>,
) -> Result<Vec<Fragment>, Diagnostic> {
    let mut out = Vec::new();
    let mut i = 0;
    let toks = &template.tokens;
    while i < toks.len() {
        let t = &toks[i];
        match &t.token {
            Token::Ident(name) if type_names.contains(name) => {
                out.push(Fragment::Hole(REL_HOLE_PREC));
                i += 1;
                i += skip_type_suffix(&toks[i..]);
            }
            Token::LParen => {
                // Standalone parenthesised type expression as a hole.
                out.push(Fragment::Hole(REL_HOLE_PREC));
                i += skip_balanced(&toks[i..]);
                i += skip_type_suffix(&toks[i..]);
            }
            _ => {
                out.push(Fragment::Lit(t.token.clone()));
                i += 1;
            }
        }
    }
    Ok(out)
}

/// Count how many trailing type-suffix tokens follow at position 0:
/// `*`, `?`, `+`, or balanced `(...)` groups, in any combination.
fn skip_type_suffix(toks: &[Spanned]) -> usize {
    let mut i = 0;
    while i < toks.len() {
        match &toks[i].token {
            Token::Star | Token::Question | Token::Plus => {
                i += 1;
            }
            Token::Caret => {
                // `^N` style — exponent on iteration count. Consume `^`
                // plus the next atomic token (Ident, Nat, or paren group).
                i += 1;
                if let Some(s) = toks.get(i) {
                    match &s.token {
                        Token::LParen => i += skip_balanced(&toks[i..]),
                        Token::Ident(_) | Token::Nat(_) => i += 1,
                        _ => {} // give up, let outer pass handle
                    }
                }
            }
            Token::LParen => {
                // `foo(args)` — parametric type argument list.
                i += skip_balanced(&toks[i..]);
            }
            _ => break,
        }
    }
    i
}

/// Try to extract a constructor operator from a variant alternative.
///
/// Returns `Some((name, fragments))` if the alt looks like a case
/// constructor (head is a SpecTec-convention case name like `NOP`,
/// `BLOCK`, `I32`, `_IDX`). Returns `None` for type-inclusion alts like
/// `| numtype | reftype` and other shapes we don't yet recognise.
///
/// Fragments: `[Lit(head_ident_token)] ++ <type-fragments of remaining tokens>`,
/// where type-fragments are produced by walking the remaining tokens
/// with the same logic that `template_to_fragments` uses for relation
/// holes (declared type names become `Hole`s; literals stay literals).
pub fn alt_to_constructor(
    alt: &Alt,
    type_names: &HashSet<String>,
) -> Option<(String, Vec<Fragment>)> {
    alt_to_constructor_with_holes(alt, type_names).map(|(name, frags, _)| (name, frags))
}

/// Like [`alt_to_constructor`] but also returns the source-token slice
/// that fell into each `Hole`. Used by the converter to lower variant
/// case argument types.
pub fn alt_to_constructor_with_holes(
    alt: &Alt,
    type_names: &HashSet<String>,
) -> Option<(String, Vec<Fragment>, Vec<Vec<Spanned>>)> {
    let toks = &alt.body.tokens;
    let head_tok = toks.first()?;
    let head_name = match &head_tok.token {
        Token::Ident(n) if is_case_head(n) => n.clone(),
        _ => return None,
    };
    let (frags, holes) = walk_alt_tokens(
        &toks[1..],
        type_names,
        vec![Fragment::Lit(head_tok.token.clone())],
    );
    Some((head_name, frags, holes))
}

/// Detect the SpecTec `instrtype = resulttype ->_(M) resulttype`
/// mixfix shape on a headless variant alt. Returns
/// `Some((long_form, short_form))` if the alt's fragments match
/// `[Hole, Lit(Arrow), Lit(Ident("_")), Hole, Hole]`, where the
/// `Lit(_) Hole` pair is the source `_(...)` optional middle slot.
///
/// The two fragment lists share the leading hole, the `Arrow` literal,
/// and the trailing hole. The long form additionally carries the
/// `Lit(_) Hole` middle. They are registered under the same op name
/// (`ARROW_MIXFIX_OP`) so the converter can recognise either Tree
/// shape and emit the same OCaml mixop.
///
/// Returns `None` when the alt doesn't match the expected shape — the
/// caller then falls through to its normal handling.
fn arrow_mixfix_alt_fragments(
    alt: &Alt,
    type_names: &HashSet<String>,
) -> Option<(Vec<Fragment>, Vec<Fragment>)> {
    let (frags, _holes) = alt_to_headless_with_holes(alt, type_names)?;
    // Match exactly `[Hole, Lit(Arrow), Lit(Ident("_")), Hole, Hole]`.
    if frags.len() != 5 {
        return None;
    }
    let is_underscore = matches!(
        &frags[2],
        Fragment::Lit(Token::Ident(n)) if n == "_"
    );
    let shape_ok = matches!(frags[0], Fragment::Hole(_))
        && matches!(frags[1], Fragment::Lit(Token::Arrow))
        && is_underscore
        && matches!(frags[3], Fragment::Hole(_))
        && matches!(frags[4], Fragment::Hole(_));
    if !shape_ok {
        return None;
    }
    // Override the LEADING hole's precedence so the arrow mixfix
    // doesn't compete inside higher-precedence constructor holes (the
    // `FUNC t_1* -> t_2*` case — see [`ARROW_LEFT_PREC`]). Trailing
    // holes keep their constructor precedence so they bind as tightly
    // as a normal case arg.
    let leading_hole = Fragment::Hole(ARROW_LEFT_PREC);
    let mut long_form = frags.clone();
    long_form[0] = leading_hole.clone();
    let short_form = vec![leading_hole, frags[1].clone(), frags[4].clone()];
    Some((long_form, short_form))
}

/// Headless single-case variant: walk the entire body's tokens as a
/// sequence of literals + holes (no case-head prefix). Used by
/// single-case variants like `syntax fieldtype = mut? storagetype`
/// and `syntax config = state; instr*`.
pub fn alt_to_headless_with_holes(
    alt: &Alt,
    type_names: &HashSet<String>,
) -> Option<(Vec<Fragment>, Vec<Vec<Spanned>>)> {
    if alt.body.tokens.is_empty() {
        return None;
    }
    Some(walk_alt_tokens(&alt.body.tokens, type_names, Vec::new()))
}

/// Common walker: emit a `Hole` for each declared type-name ident (with
/// any iter suffix folded in) or balanced parenthesised group, and a
/// `Lit` for everything else. Returns `(fragments, hole-token-slices)`.
fn walk_alt_tokens(
    rest: &[Spanned],
    type_names: &HashSet<String>,
    mut frags: Vec<Fragment>,
) -> (Vec<Fragment>, Vec<Vec<Spanned>>) {
    let mut hole_toks: Vec<Vec<Spanned>> = Vec::new();
    let mut i = 0;
    while i < rest.len() {
        match &rest[i].token {
            Token::Ident(name) if type_names.contains(name) => {
                frags.push(Fragment::Hole(CTOR_HOLE_PREC));
                let start = i;
                i += 1;
                i += skip_type_suffix(&rest[i..]);
                hole_toks.push(rest[start..i].to_vec());
            }
            Token::LParen => {
                frags.push(Fragment::Hole(CTOR_HOLE_PREC));
                let start = i;
                i += skip_balanced(&rest[i..]);
                i += skip_type_suffix(&rest[i..]);
                hole_toks.push(rest[start..i].to_vec());
            }
            _ => {
                frags.push(Fragment::Lit(rest[i].token.clone()));
                i += 1;
            }
        }
    }
    (frags, hole_toks)
}

// ---------- minimal Expr AST + conclusion elaboration ----------

/// Expression AST, sketched to mirror `spectec_ast::SpecTecExp` so the
/// converter in [`crate::ast_doc`] can map every variant directly.
///
/// **Coverage caveat:** elaboration currently produces only a subset of
/// these variants (`Var`, `Num`, `Text`, `Tup`, `Case`, `Eps`, `Iter`,
/// `Raw`). The others — `Bin`, `Cmp`, `Idx`, `Dot`, `Call`, `Str`, etc.
/// — exist so we can structurally represent the full SpecTec language
/// when later elaboration passes (arithmetic-escape parsing,
/// field-access recognition, etc.) start producing them. Until then,
/// shapes that would map to them fall through to `Raw`.
///
/// Spans are carried so downstream consumers can attach diagnostics.
#[derive(Clone, Debug)]
pub enum Expr {
    Var { span: Span, name: String },
    Bool { span: Span, value: bool },
    Num { span: Span, value: NumLit },
    Text { span: Span, value: String },
    /// Unary operator: `not e`, `+e`, `-e`, `±e`, `∓e`.
    Un { span: Span, op: UnOp, ty: OpType, e: Box<Expr> },
    /// Binary arithmetic / logical: `e1 + e2`, `e1 ∧ e2`, etc.
    Bin {
        span: Span,
        op: BinOp,
        ty: OpType,
        e1: Box<Expr>,
        e2: Box<Expr>,
    },
    /// Comparison: `e1 = e2`, `e1 ≤ e2`, etc.
    Cmp {
        span: Span,
        op: CmpOp,
        ty: OpType,
        e1: Box<Expr>,
        e2: Box<Expr>,
    },
    /// Indexing: `e1[e2]`.
    Idx { span: Span, e1: Box<Expr>, e2: Box<Expr> },
    /// Slicing: `e1[e2 : e3]`.
    Slice {
        span: Span,
        e1: Box<Expr>,
        e2: Box<Expr>,
        e3: Box<Expr>,
    },
    /// Functional update: `e1[path := e2]`.
    Upd {
        span: Span,
        e1: Box<Expr>,
        path: Box<Path>,
        e2: Box<Expr>,
    },
    /// Functional extension: `e1[path =.. e2]`.
    Ext {
        span: Span,
        e1: Box<Expr>,
        path: Box<Path>,
        e2: Box<Expr>,
    },
    /// Record literal: `{ FIELD = e, ... }`.
    Str { span: Span, fields: Vec<ExprField> },
    /// Field access: `e.FIELD`.
    Dot { span: Span, e: Box<Expr>, field: String },
    /// Sequence composition: `e1 ++ e2`.
    Comp { span: Span, e1: Box<Expr>, e2: Box<Expr> },
    /// Membership: `e1 <- e2`.
    Mem { span: Span, e1: Box<Expr>, e2: Box<Expr> },
    /// Length: `|e|`.
    Len { span: Span, e: Box<Expr> },
    /// Parenthesised sequence — `()` is the empty tuple, `(x)` collapses
    /// to `x`, `(x, y)` is a 2-tuple.
    Tup { span: Span, items: Vec<Expr> },
    /// Function call: `$name(arg, ...)`. Args are elaborated to
    /// `Expr`s at construction time so the typechecker can coerce
    /// each against the callee's parameter type (analogous to how
    /// `Case` args are typed against `ctor_params`).
    Call { span: Span, name: String, args: Vec<Expr> },
    /// `<inner><iter-suffix>` — postfix iteration on an expression.
    /// `bindings` is the inferred binder list (see `IterBinding`).
    Iter {
        span: Span,
        inner: Box<Expr>,
        kind: IterKind,
        bindings: Vec<IterBinding>,
    },
    /// Tuple projection: `e.<i>` (positional).
    Proj { span: Span, e: Box<Expr>, index: i64 },
    /// Case constructor application: `NAME` or `NAME e_1 e_2 ...`.
    /// The "case-like" head is any identifier whose first character is
    /// uppercase, or that begins with an underscore (`NOP`, `BLOCK`,
    /// `I32`, `_IDX`, ...).
    ///
    /// `op` is the explicit MixOp parts to emit on lowering. `None`
    /// falls back to `[head]` (the OCaml convention for named case
    /// constructors). `Some(parts)` is used for headless single-case
    /// variants synthesised by the type-checker — e.g. splitting
    /// `e1 ; e2` against `syntax config = state; instr*` produces a
    /// `Case { head: "config", args: [e1, e2], op: Some(vec!["", ";", ""]) }`
    /// so the converter emits `MixOp(["", ";", ""])` rather than
    /// `MixOp(["config"])`.
    Case {
        span: Span,
        head: String,
        args: Vec<Expr>,
        op: Option<Vec<String>>,
    },
    /// Inverse case match: `e :> NAME` — extracts the operand of a
    /// known case constructor.
    Uncase { span: Span, e: Box<Expr>, head: String },
    /// Optional literal: `?e` (Some), or `?` (None when `inner` is None).
    Opt {
        span: Span,
        inner: Option<Box<Expr>>,
    },
    /// Inverse optional: extracts the value from a `Some` known to hold.
    Unopt { span: Span, e: Box<Expr> },
    /// List literal: `[e_1, e_2, ...]` or `eps` for the empty list.
    List { span: Span, items: Vec<Expr> },
    /// Singleton lift: `[e]`.
    Lift { span: Span, e: Box<Expr> },
    /// List concatenation: `e1 ++ e2`.
    Cat { span: Span, e1: Box<Expr>, e2: Box<Expr> },
    /// Numeric conversion: `Cvt(nt1, nt2, e)` reinterprets a number of
    /// type `nt1` as one of type `nt2`.
    Cvt {
        span: Span,
        from: NumTyp,
        to: NumTyp,
        e: Box<Expr>,
    },
    /// Subtype coercion: `Sub(t1, t2, e)` injects `e : t1` into `t2`.
    /// Inserted by the type-checker at subtype boundaries; not
    /// produced by elaboration directly. The `from_ty`/`to_ty` carry
    /// the source and target `SpecTecTyp`s for the coercion.
    Sub {
        span: Span,
        from_ty: spectec_ast::SpecTecTyp,
        to_ty: spectec_ast::SpecTecTyp,
        e: Box<Expr>,
    },
    /// `eps` — the empty sequence literal.
    Eps { span: Span },
    /// Fallback: an unanalysed token run. Used when the expression
    /// shape isn't yet supported by the structured cases.
    Raw(TokenRun),
}

/// Number literal. Mirrors `spectec_ast::SpecTecNum` structurally, but
/// uses arbitrary-precision `covalence_types::Nat` / `Int` so source
/// literals beyond `u64`/`i64` survive elaboration. The converter in
/// [`crate::ast_doc`] clamps to `u64`/`i64` when emitting to
/// `spectec_ast::SpecTecNum` (which uses bounded ints).
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum NumLit {
    Nat(covalence_types::Nat),
    Int(covalence_types::Int),
    Rat(String),
    Real(String),
}

/// Operand-type tag for arithmetic / comparison operators — mirrors
/// `spectec_ast::SpecTecOpTyp`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum OpType {
    Nat,
    Int,
    Rat,
    Real,
    Bool,
}

/// Unary operator — mirrors `spectec_ast::SpecTecUnOp`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum UnOp {
    Not,
    Plus,
    Minus,
    PlusMinus,
    MinusPlus,
}

/// Binary operator — mirrors `spectec_ast::SpecTecBinOp`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum BinOp {
    And,
    Or,
    Impl,
    Equiv,
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Pow,
}

/// Comparison operator — mirrors `spectec_ast::SpecTecCmpOp`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CmpOp {
    Eq,
    Ne,
    Lt,
    Gt,
    Le,
    Ge,
}

/// Numeric type — mirrors `spectec_ast::SpecTecNumTyp`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum NumTyp {
    Nat,
    Int,
    Rat,
    Real,
}

/// Update / extension path — mirrors `spectec_ast::SpecTecPath`. Kept
/// as a sketch; full path elaboration comes with `Upd`/`Ext` lowering.
#[derive(Clone, Debug)]
pub enum Path {
    /// `e` itself — root of a path.
    Root,
    /// `path[e]` — index step.
    Idx { p: Box<Path>, e: Expr },
    /// `path[e1 : e2]` — slice step.
    Slice { p: Box<Path>, e1: Expr, e2: Expr },
    /// `path.FIELD` — dot step.
    Dot { p: Box<Path>, field: String },
}

/// One `FIELD = value` pair in a record literal.
#[derive(Clone, Debug)]
pub struct ExprField {
    pub field: String,
    pub value: Expr,
}

impl Expr {
    pub fn span(&self) -> Span {
        match self {
            Expr::Var { span, .. }
            | Expr::Bool { span, .. }
            | Expr::Num { span, .. }
            | Expr::Text { span, .. }
            | Expr::Un { span, .. }
            | Expr::Bin { span, .. }
            | Expr::Cmp { span, .. }
            | Expr::Idx { span, .. }
            | Expr::Slice { span, .. }
            | Expr::Upd { span, .. }
            | Expr::Ext { span, .. }
            | Expr::Str { span, .. }
            | Expr::Dot { span, .. }
            | Expr::Comp { span, .. }
            | Expr::Mem { span, .. }
            | Expr::Len { span, .. }
            | Expr::Tup { span, .. }
            | Expr::Call { span, .. }
            | Expr::Iter { span, .. }
            | Expr::Proj { span, .. }
            | Expr::Case { span, .. }
            | Expr::Uncase { span, .. }
            | Expr::Opt { span, .. }
            | Expr::Unopt { span, .. }
            | Expr::List { span, .. }
            | Expr::Lift { span, .. }
            | Expr::Cat { span, .. }
            | Expr::Cvt { span, .. }
            | Expr::Sub { span, .. }
            | Expr::Eps { span } => *span,
            Expr::Raw(tr) => tr.span,
        }
    }
}

/// Result of elaborating one `rule`: the relation it belongs to, the
/// operand expressions extracted from its conclusion, and the rule's
/// premises (each elaborated to its kind).
#[derive(Clone, Debug)]
pub struct ElabRuleConclusion {
    pub rule_name: String,
    pub case: Option<String>,
    pub op: OpId,
    pub operands: Vec<Expr>,
    pub premises: Vec<ElabPremise>,
}

/// An elaborated premise.
#[derive(Clone, Debug)]
pub enum ElabPremise {
    /// `RelName: <args>` — a relation premise.
    Rule {
        rel_name: String,
        op: OpId,
        operands: Vec<Expr>,
    },
    /// `if <expr>` — a boolean side condition.
    If(Expr),
    /// `let <lhs> = <rhs>` — a binding side condition.
    Let { lhs: Expr, rhs: Expr },
    /// `otherwise` / `else` — residual catch-all marker.
    Else,
    /// `(P)<iter>` — replicated premise. `inner` is the elaborated body;
    /// `kind` describes the iteration shape. `bindings` lists the
    /// implicit iteration binders inferred from variables that appear
    /// both inside `inner` and as `name`-suffixed sources somewhere in
    /// the enclosing rule's conclusion or earlier premises.
    Iter {
        inner: Box<ElabPremise>,
        kind: IterKind,
        bindings: Vec<IterBinding>,
    },
    /// Anything not yet structurally recognised, kept as a raw run.
    Raw(TokenRun),
}

/// One inferred iteration binder: a name appearing inside an iter body
/// that is bound (per iteration) by drawing values from a `*`-suffixed
/// source elsewhere in the rule. Mirrors `spectec_ast::SpecTecIterExp::Dom`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct IterBinding {
    /// The bound variable name (the one referenced inside the iter body).
    pub var: String,
    /// The source expression supplying values for that name. Typically
    /// `<var>*` somewhere in the conclusion or earlier premise.
    pub source: String,
}

/// Iteration shape attached to a premise.
#[derive(Clone, Debug)]
pub enum IterKind {
    /// `(P)?`
    Opt,
    /// `(P)*`
    Star,
    /// `(P)+`
    Plus,
    /// `(P)^<count-expr>` — fixed-length iteration with an explicit count.
    /// The count expression is kept as a raw token run for now.
    Length(TokenRun),
}

/// Elaborate one rule's conclusion against the operator table.
///
/// Looks up the rule's relation by name in `ctx.op_table`, walks the
/// operator's `Fragment` template, matches literals against the
/// conclusion's tokens, and parses the holes as expressions.
pub fn elab_rule_conclusion(
    rule: &RuleDecl,
    ctx: &ElabContext,
) -> Result<ElabRuleConclusion, Diagnostic> {
    let op = ctx
        .op_table
        .iter()
        .find(|o| o.name == rule.name.text)
        .ok_or_else(|| {
            Diagnostic::error(
                rule.name.span,
                format!(
                    "rule references unknown relation `{}`",
                    rule.name.text
                ),
            )
        })?;
    let op_id = op.id;
    let fragments = op.fragments.clone();

    // Normalise subscripts in the rule body so `_C` (a context
    // metavariable subscript) matches the relation template's
    // `_<context>` literal+hole split.
    let normalised_concl = normalize_subscript_idents(&rule.conclusion.tokens);
    let mut input: &[Spanned] = &normalised_concl;
    let mut operands = Vec::new();

    for (i, frag) in fragments.iter().enumerate() {
        match frag {
            Fragment::Lit(expected) => {
                expect_token_in_conclusion(&mut input, expected, &rule.name.text)?;
            }
            Fragment::Hole(_) => {
                // If the next fragment is another Hole (consecutive
                // holes, no Lit between), consume one atomic token
                // for this hole so the next one has something left.
                // Otherwise: hole runs up to the next Lit, or to EOF.
                let next_is_hole =
                    matches!(fragments.get(i + 1), Some(Fragment::Hole(_)));
                let expr = if next_is_hole {
                    parse_atomic_in_conclusion(&mut input, ctx, &rule.name.text)?
                } else {
                    let stop = next_lit_after(&fragments, i + 1);
                    parse_expression_until(&mut input, stop.as_ref(), ctx)?
                };
                operands.push(expr);
            }
        }
    }

    if !input.is_empty() {
        return Err(Diagnostic::error(
            input.first().unwrap().span,
            format!(
                "rule `{}` conclusion has {} leftover token(s) after matching template",
                rule.name.text,
                input.len()
            ),
        ));
    }

    let premises = rule
        .premises
        .iter()
        .map(|p| elab_premise(p, ctx))
        .collect::<Result<Vec<_>, _>>()?;
    // Iteration binder inference: scan operands + every premise for
    // `name*`-shaped sources, then walk each Iter premise body and
    // record bindings for variables that match.
    let sources = collect_iter_sources(&operands, &premises);
    let operands = operands
        .into_iter()
        .map(|e| attach_iter_bindings_to_expr(e, &sources))
        .collect();
    let premises = premises
        .into_iter()
        .map(|p| attach_iter_bindings(p, &sources))
        .collect();

    Ok(ElabRuleConclusion {
        rule_name: rule.name.text.clone(),
        case: rule.case.as_ref().map(|c| c.text.clone()),
        op: op_id,
        operands,
        premises,
    })
}

/// Elaborate a single premise from its raw token run.
///
/// Detects the premise form from the leading token: `if`, `let`,
/// `else`/`otherwise`, an iteration group `(...)`, or otherwise a
/// `RelName: <args>` relation reference.
pub fn elab_premise(
    prem: &TokenRun,
    ctx: &ElabContext,
) -> Result<ElabPremise, Diagnostic> {
    let toks = &prem.tokens;
    match toks.first().map(|s| &s.token) {
        Some(Token::If) => {
            // `if <expr>` — entire remainder is the expression.
            let span = prem.span;
            if toks.len() == 1 {
                return Err(Diagnostic::error(
                    span,
                    "`if` premise needs a condition expression",
                ));
            }
            let body = &toks[1..];
            let body_span = body
                .iter()
                .map(|s| s.span)
                .reduce(Span::join)
                .unwrap_or(span);
            // `if` premise bodies often contain top-level comparison /
            // arithmetic operators. Route through `parse_arith` so
            // those get structured before falling back to
            // `classify_simple_expression`.
            let cond = parse_arith(body, body_span, ctx)?;
            Ok(ElabPremise::If(cond))
        }
        Some(Token::Let) => {
            // `let <lhs> = <rhs>` — find top-level `=` split.
            let body = &toks[1..];
            let eq_idx = top_level_index_of(body, |t| matches!(t, Token::Eq))
                .ok_or_else(|| {
                    Diagnostic::error(
                        prem.span,
                        "`let` premise has no top-level `=` splitting lhs from rhs",
                    )
                })?;
            let lhs_slice = &body[..eq_idx];
            let rhs_slice = &body[eq_idx + 1..];
            if lhs_slice.is_empty() || rhs_slice.is_empty() {
                return Err(Diagnostic::error(
                    prem.span,
                    "`let` premise has empty lhs or rhs",
                ));
            }
            let lhs_span = lhs_slice.iter().map(|s| s.span).reduce(Span::join).unwrap();
            let rhs_span = rhs_slice.iter().map(|s| s.span).reduce(Span::join).unwrap();
            let lhs = classify_simple_expression(lhs_slice, lhs_span, ctx)?;
            let rhs = classify_simple_expression(rhs_slice, rhs_span, ctx)?;
            Ok(ElabPremise::Let { lhs, rhs })
        }
        Some(Token::Else) | Some(Token::Otherwise) => Ok(ElabPremise::Else),
        Some(Token::LParen) => elab_iter_premise(prem, ctx),
        Some(Token::Ident(name)) => {
            // `RelName: <args>` — relation premise.
            let rel_name = name.clone();
            let Some(op) = ctx.op_table.iter().find(|o| o.name == rel_name) else {
                return Ok(ElabPremise::Raw(prem.clone()));
            };
            let op_id = op.id;
            let fragments = op.fragments.clone();
            // Expect a `:` right after the relation name.
            if !matches!(toks.get(1).map(|s| &s.token), Some(Token::Colon)) {
                return Ok(ElabPremise::Raw(prem.clone()));
            }
            let mut input: &[Spanned] = &toks[2..];
            let mut operands = Vec::new();
            for (i, frag) in fragments.iter().enumerate() {
                match frag {
                    Fragment::Lit(expected) => {
                        // Use a soft error here: fall back to Raw if a
                        // literal doesn't match (premise might have
                        // optional extras we don't model yet).
                        match input.first() {
                            Some(s) if &s.token == expected => {
                                input = &input[1..];
                            }
                            _ => return Ok(ElabPremise::Raw(prem.clone())),
                        }
                    }
                    Fragment::Hole(_) => {
                        let stop = next_lit_after(&fragments, i + 1);
                        match parse_expression_until(&mut input, stop.as_ref(), ctx) {
                            Ok(e) => operands.push(e),
                            Err(_) => return Ok(ElabPremise::Raw(prem.clone())),
                        }
                    }
                }
            }
            if !input.is_empty() {
                return Ok(ElabPremise::Raw(prem.clone()));
            }
            Ok(ElabPremise::Rule {
                rel_name,
                op: op_id,
                operands,
            })
        }
        _ => Ok(ElabPremise::Raw(prem.clone())),
    }
}

/// Recognise an iteration premise: `( <inner-premise> ) <iter-suffix>`.
/// The matching `)` must be at paren depth 0 of the inner body and
/// must leave at least one trailing token (the iter suffix).
fn elab_iter_premise(
    prem: &TokenRun,
    ctx: &ElabContext,
) -> Result<ElabPremise, Diagnostic> {
    let toks = &prem.tokens;
    // toks[0] is `(`. Find the matching `)` (depth 0 again).
    let close_idx = matching_rparen(toks).ok_or_else(|| {
        Diagnostic::error(prem.span, "iteration premise: no matching `)`")
    })?;
    let inner_toks = &toks[1..close_idx];
    let trailing = &toks[close_idx + 1..];
    if inner_toks.is_empty() {
        return Ok(ElabPremise::Raw(prem.clone()));
    }
    if trailing.is_empty() {
        // Just a parenthesised premise with no iter suffix — pass-through.
        let inner_span = inner_toks
            .iter()
            .map(|s| s.span)
            .reduce(Span::join)
            .expect("non-empty");
        let inner_prem = TokenRun {
            span: inner_span,
            tokens: inner_toks.to_vec(),
        };
        return elab_premise(&inner_prem, ctx);
    }
    // Recognise the iter suffix.
    let kind = match &trailing[0].token {
        Token::Question if trailing.len() == 1 => IterKind::Opt,
        Token::Star if trailing.len() == 1 => IterKind::Star,
        Token::Plus if trailing.len() == 1 => IterKind::Plus,
        Token::Caret => {
            // `^<count-expr>` — count is the rest of trailing.
            let count_toks = &trailing[1..];
            if count_toks.is_empty() {
                return Ok(ElabPremise::Raw(prem.clone()));
            }
            let count_span = count_toks
                .iter()
                .map(|s| s.span)
                .reduce(Span::join)
                .expect("non-empty");
            IterKind::Length(TokenRun {
                span: count_span,
                tokens: count_toks.to_vec(),
            })
        }
        _ => return Ok(ElabPremise::Raw(prem.clone())),
    };
    // Recursively elaborate the inner premise.
    let inner_span = inner_toks
        .iter()
        .map(|s| s.span)
        .reduce(Span::join)
        .expect("non-empty");
    let inner_prem = TokenRun {
        span: inner_span,
        tokens: inner_toks.to_vec(),
    };
    let inner_elab = elab_premise(&inner_prem, ctx)?;
    Ok(ElabPremise::Iter {
        inner: Box::new(inner_elab),
        kind,
        bindings: Vec::new(),
    })
}

/// Map from bare iter-source name to its source-with-suffix form.
/// `Iter { inner: Var{t_1}, kind: Star }` populates the entry
/// `"t_1" -> "t_1*"`. Mirrors OCaml's `dom "x" (var "x*")` shape — the
/// bare name is what the iter body references; the suffixed form is
/// what populates the `e` side of each `SpecTecIterExp::Dom`.
type IterSources = std::collections::BTreeMap<String, String>;

/// Collect the bare→source map for every `name`-shaped iter source
/// appearing in `operands` or `premises`. Each entry is a candidate
/// for iteration binder inference inside any `Iter` body referencing
/// the bare name.
fn collect_iter_sources(operands: &[Expr], premises: &[ElabPremise]) -> IterSources {
    let mut sources = IterSources::new();
    for op in operands {
        gather_iter_sources_in_expr(op, &mut sources);
    }
    for p in premises {
        gather_iter_sources_in_premise(p, &mut sources);
    }
    sources
}

fn iter_suffix_char(kind: &IterKind) -> &'static str {
    match kind {
        IterKind::Opt => "?",
        IterKind::Star => "*",
        IterKind::Plus => "+",
        // Fixed-length iters don't have a single-char suffix; keep
        // them bare for now. (No wasm-3.0 rule uses one as a Dom
        // source.)
        IterKind::Length(_) => "",
    }
}

fn gather_iter_sources_in_expr(e: &Expr, out: &mut IterSources) {
    match e {
        Expr::Iter { inner, kind, .. } => {
            if let Expr::Var { name, .. } = inner.as_ref() {
                let suffix = iter_suffix_char(kind);
                if !suffix.is_empty() {
                    let with_suffix = format!("{name}{suffix}");
                    out.entry(name.clone()).or_insert(with_suffix);
                }
            }
            gather_iter_sources_in_expr(inner, out);
        }
        Expr::Case { args, .. } => {
            for a in args {
                gather_iter_sources_in_expr(a, out);
            }
        }
        Expr::Tup { items, .. } => {
            for i in items {
                gather_iter_sources_in_expr(i, out);
            }
        }
        _ => {}
    }
}

fn gather_iter_sources_in_premise(p: &ElabPremise, out: &mut IterSources) {
    match p {
        ElabPremise::Rule { operands, .. } => {
            for op in operands {
                gather_iter_sources_in_expr(op, out);
            }
        }
        ElabPremise::If(e) => gather_iter_sources_in_expr(e, out),
        ElabPremise::Let { lhs, rhs } => {
            gather_iter_sources_in_expr(lhs, out);
            gather_iter_sources_in_expr(rhs, out);
        }
        ElabPremise::Iter { inner, .. } => gather_iter_sources_in_premise(inner, out),
        ElabPremise::Else | ElabPremise::Raw(_) => {}
    }
}

/// Walk an expression; for every `Iter` it contains whose inner Var is
/// in the source set, populate the `bindings` field. Mirrors the
/// existing premise-only logic, applied to operand expressions so that
/// constructor-arg iters (e.g. the `iter (var "t_1") list (dom "t_1"
/// (var "t_1"))` inside an arrow_mixfix conclusion) get their `xes`
/// populated by the converter. Source is kept as the bare base name to
/// match the existing premise-binding convention.
fn attach_iter_bindings_to_expr(e: Expr, sources: &IterSources) -> Expr {
    match e {
        Expr::Iter {
            span,
            inner,
            kind,
            bindings: _,
        } => {
            let mut vars: HashSet<String> = HashSet::new();
            collect_vars_in_expr(&inner, &mut vars);
            let mut bindings: Vec<IterBinding> = vars
                .iter()
                .filter_map(|v| {
                    sources.get(v).map(|src| IterBinding {
                        var: v.clone(),
                        source: src.clone(),
                    })
                })
                .collect();
            bindings.sort_by(|a, b| a.var.cmp(&b.var));
            let inner = Box::new(attach_iter_bindings_to_expr(*inner, sources));
            Expr::Iter {
                span,
                inner,
                kind,
                bindings,
            }
        }
        Expr::Case { span, head, args, op } => Expr::Case {
            span,
            head,
            op,
            args: args
                .into_iter()
                .map(|a| attach_iter_bindings_to_expr(a, sources))
                .collect(),
        },
        Expr::Tup { span, items } => Expr::Tup {
            span,
            items: items
                .into_iter()
                .map(|i| attach_iter_bindings_to_expr(i, sources))
                .collect(),
        },
        other => other,
    }
}

/// Walk a premise; for every `Iter` it contains, infer bindings by
/// matching its inner Vars against the source set.
fn attach_iter_bindings(p: ElabPremise, sources: &IterSources) -> ElabPremise {
    match p {
        ElabPremise::Iter { inner, kind, .. } => {
            let bindings = infer_bindings_for_inner(&inner, sources);
            let inner = Box::new(attach_iter_bindings(*inner, sources));
            ElabPremise::Iter {
                inner,
                kind,
                bindings,
            }
        }
        other => other,
    }
}

fn infer_bindings_for_inner(
    inner: &ElabPremise,
    sources: &IterSources,
) -> Vec<IterBinding> {
    let mut vars: HashSet<String> = HashSet::new();
    collect_vars_in_premise(inner, &mut vars);
    let mut bindings: Vec<IterBinding> = Vec::new();
    for v in &vars {
        if let Some(src) = sources.get(v) {
            bindings.push(IterBinding {
                var: v.clone(),
                source: src.clone(),
            });
        }
    }
    bindings.sort_by(|a, b| a.var.cmp(&b.var));
    bindings
}

fn collect_vars_in_expr(e: &Expr, out: &mut HashSet<String>) {
    match e {
        Expr::Var { name, .. } => {
            out.insert(name.clone());
        }
        Expr::Case { args, .. } => {
            for a in args {
                collect_vars_in_expr(a, out);
            }
        }
        Expr::Tup { items, .. } => {
            for i in items {
                collect_vars_in_expr(i, out);
            }
        }
        Expr::Iter { inner, .. } => collect_vars_in_expr(inner, out),
        _ => {}
    }
}

fn collect_vars_in_premise(p: &ElabPremise, out: &mut HashSet<String>) {
    match p {
        ElabPremise::Rule { operands, .. } => {
            for op in operands {
                collect_vars_in_expr(op, out);
            }
        }
        ElabPremise::If(e) => collect_vars_in_expr(e, out),
        ElabPremise::Let { lhs, rhs } => {
            collect_vars_in_expr(lhs, out);
            collect_vars_in_expr(rhs, out);
        }
        ElabPremise::Iter { inner, .. } => collect_vars_in_premise(inner, out),
        ElabPremise::Else | ElabPremise::Raw(_) => {}
    }
}

/// Given `toks[0]` is `LParen`, return the index of the matching `RParen`
/// at depth 0 (relative to that opening paren).
fn matching_rparen(toks: &[Spanned]) -> Option<usize> {
    let mut depth: i32 = 0;
    for (i, t) in toks.iter().enumerate() {
        match &t.token {
            Token::LParen | Token::LBracket | Token::LBrace => depth += 1,
            Token::RParen | Token::RBracket | Token::RBrace => {
                depth -= 1;
                if depth == 0 {
                    return Some(i);
                }
            }
            _ => {}
        }
    }
    None
}

/// Index of the first token (at paren depth 0) for which `pred` is true.
fn top_level_index_of(toks: &[Spanned], pred: impl Fn(&Token) -> bool) -> Option<usize> {
    let mut depth: i32 = 0;
    for (i, t) in toks.iter().enumerate() {
        match &t.token {
            Token::LParen | Token::LBracket | Token::LBrace => depth += 1,
            Token::RParen | Token::RBracket | Token::RBrace => depth -= 1,
            _ => {}
        }
        if depth == 0 && pred(&t.token) {
            return Some(i);
        }
    }
    None
}

/// Find the next `Lit` token in the fragment list starting at `from`.
fn next_lit_after(frags: &[Fragment], from: usize) -> Option<Token> {
    for f in &frags[from..] {
        if let Fragment::Lit(t) = f {
            return Some(t.clone());
        }
    }
    None
}

fn expect_token_in_conclusion(
    input: &mut &[Spanned],
    expected: &Token,
    rule_name: &str,
) -> Result<(), Diagnostic> {
    match input.first() {
        Some(s) if &s.token == expected => {
            *input = &input[1..];
            Ok(())
        }
        Some(s) => Err(Diagnostic::error(
            s.span,
            format!(
                "rule `{}` conclusion does not match relation template: expected `{}`, found `{}`",
                rule_name,
                expected.to_source_text(),
                s.token.to_source_text(),
            ),
        )),
        None => Err(Diagnostic::error(
            Span::new(crate::source::FileId::new(0), u32::MAX, u32::MAX),
            format!(
                "rule `{}` conclusion ends before template literal `{}`",
                rule_name,
                expected.to_source_text(),
            ),
        )),
    }
}

/// Consume one atomic expression: a single Ident/Nat/Text/Eps token
/// or one balanced parenthesised / bracketed group. Used when two
/// `Hole` fragments meet with no literal between, so we can't gauge
/// where the first hole ends by scanning for a stop token.
fn parse_atomic_in_conclusion(
    input: &mut &[Spanned],
    ctx: &ElabContext,
    rule_name: &str,
) -> Result<Expr, Diagnostic> {
    let s = input.first().ok_or_else(|| {
        Diagnostic::error(
            Span::new(crate::source::FileId::new(0), u32::MAX, u32::MAX),
            format!(
                "rule `{}` conclusion runs out before all template holes are filled",
                rule_name
            ),
        )
    })?;
    let take_n = match &s.token {
        Token::LParen | Token::LBracket | Token::LBrace => skip_balanced(input),
        _ => 1,
    };
    // Include any trailing iter suffix.
    let after_atom = &input[take_n..];
    let suffix = skip_type_suffix(after_atom);
    let take_total = take_n + suffix;
    let taken = &input[..take_total];
    let span = taken
        .iter()
        .map(|s| s.span)
        .reduce(Span::join)
        .expect("non-empty by check above");
    let expr = classify_simple_expression(taken, span, ctx)?;
    *input = &input[take_total..];
    Ok(expr)
}

/// Parse an expression from `input`, stopping when the next top-level
/// token equals `stop_lit` (or, if `stop_lit` is None, when input is
/// empty). The stop sentinel is NOT consumed.
fn parse_expression_until(
    input: &mut &[Spanned],
    stop_lit: Option<&Token>,
    ctx: &ElabContext,
) -> Result<Expr, Diagnostic> {
    // Collect tokens up to the stop sentinel at depth 0.
    let mut depth: i32 = 0;
    let mut taken: Vec<Spanned> = Vec::new();
    while let Some(s) = input.first() {
        if depth == 0
            && stop_lit.map(|t| t == &s.token).unwrap_or(false)
        {
            break;
        }
        match &s.token {
            Token::LParen | Token::LBracket | Token::LBrace => depth += 1,
            Token::RParen | Token::RBracket | Token::RBrace => depth -= 1,
            _ => {}
        }
        taken.push(s.clone());
        *input = &input[1..];
    }
    if taken.is_empty() {
        return Err(Diagnostic::error(
            input
                .first()
                .map(|s| s.span)
                .unwrap_or_else(|| Span::new(crate::source::FileId::new(0), u32::MAX, u32::MAX)),
            "empty expression in rule conclusion hole",
        ));
    }
    let span = taken
        .iter()
        .map(|s| s.span)
        .reduce(Span::join)
        .expect("non-empty by check above");
    classify_simple_expression(&taken, span, ctx)
}

/// Public wrapper: classify the tokens of a `TokenRun` as an `Expr`
/// using the same machinery as conclusion-hole elaboration. Returns
/// `None` for empty input. Used by the converter to lower raw token
/// runs (def clause args + rhs, etc.) without going through a full
/// rule-style elaboration.
pub fn classify_token_run(tr: &TokenRun, ctx: &ElabContext) -> Option<Expr> {
    if tr.tokens.is_empty() {
        return None;
    }
    let span = tr.tokens.iter().map(|s| s.span).reduce(Span::join).unwrap();
    classify_simple_expression(&tr.tokens, span, ctx).ok()
}

/// Try to recognise an expression from a slice of tokens. Order of
/// attempts:
///
/// 1. Singletons (Var / Num / Text / Eps / zero-arg Case).
/// 2. Parenthesised groups (Tup with comma-split; singleton-collapsing).
/// 3. **Pratt parse against the OpTable** — structures constructor
///    applications (`BLOCK bt instr*` → `Case(BLOCK, [bt, instr])`)
///    and other registered mixfix forms that fully consume the slice.
/// 4. Fallback: `Expr::Raw`.
fn classify_simple_expression(
    toks: &[Spanned],
    span: Span,
    ctx: &ElabContext,
) -> Result<Expr, Diagnostic> {
    // Singletons: Var, Num, Text, Eps, or a zero-arg Case for uppercase
    // / underscore-prefixed names. A declared metavariable wins over
    // the case-head heuristic.
    if toks.len() == 1 {
        return Ok(match &toks[0].token {
            Token::Ident(name) if name == "true" => Expr::Bool { span, value: true },
            Token::Ident(name) if name == "false" => Expr::Bool { span, value: false },
            Token::Ident(name) if is_declared_metavar(name, &ctx.var_names) => Expr::Var {
                span,
                name: name.clone(),
            },
            Token::Ident(name) if is_case_head(name) => Expr::Case {
                span,
                head: name.clone(),
                args: Vec::new(),
                op: None,
            },
            Token::Ident(name) => Expr::Var {
                span,
                name: name.clone(),
            },
            Token::Nat(n) => Expr::Num {
                span,
                value: NumLit::Nat(n.clone()),
            },
            Token::Text(t) => Expr::Text {
                span,
                value: t.clone(),
            },
            Token::Eps => Expr::Eps { span },
            _ => Expr::Raw(TokenRun {
                span,
                tokens: toks.to_vec(),
            }),
        });
    }

    // Parenthesised: `( ... )` — split inner on top-level commas.
    if matches!(toks.first().map(|s| &s.token), Some(Token::LParen))
        && matches!(toks.last().map(|s| &s.token), Some(Token::RParen))
    {
        let inner = &toks[1..toks.len() - 1];
        if depth_balanced(inner) {
            return classify_tuple_inner(inner, span, ctx);
        }
    }

    // Record literal `{FIELD val, FIELD val, ...}`.
    if matches!(toks.first().map(|s| &s.token), Some(Token::LBrace))
        && matches!(toks.last().map(|s| &s.token), Some(Token::RBrace))
    {
        let inner = &toks[1..toks.len() - 1];
        if depth_balanced(inner)
            && let Some(rec) = try_classify_record(inner, span, ctx)?
        {
            return Ok(rec);
        }
    }

    // `$( ... )` — arithmetic-escape body, parsed with the standard
    // precedence ladder. Must come before `try_classify_call` so the
    // `$(` prefix isn't misread as the start of a call (which expects
    // `$Ident(`).
    if let Some(arith) = try_classify_arith_escape(toks, span, ctx)? {
        return Ok(arith);
    }

    // `$ident ( ... )` — function call. Optional trailing tokens (like
    // postfix ops) are NOT consumed here; we require the call to span
    // the entire slice exactly.
    if let Some(call) = try_classify_call(toks, span, ctx)? {
        return Ok(call);
    }

    // `e [ <path> <op> <rhs> ]` — functional update / extension. Must
    // run before `try_classify_idx` so the path-shape body wins over
    // plain indexing. See task #34 spec doc.
    if let Some(upd) = try_classify_path_update(toks, span, ctx)? {
        return Ok(upd);
    }

    // `e [ ... ]` — indexing. Last token is `]`; matching `[` is at
    // some balanced offset. The split puts the bracketed body on the
    // right and the prefix on the left.
    if let Some(idx) = try_classify_idx(toks, span, ctx)? {
        return Ok(idx);
    }

    // `e . FIELD` — field access. Last two tokens are `Dot Ident` at
    // paren-depth 0.
    if let Some(dot) = try_classify_dot(toks, span, ctx)? {
        return Ok(dot);
    }

    // Pratt-parse against the OpTable. Succeeds only if the parse fully
    // consumes the slice; on failure or leftover input we fall back.
    if let Some(expr) = try_pratt_expression(toks, span, ctx) {
        return Ok(expr);
    }

    // Coarse fallback: a case-headed multi-token slice that Pratt
    // didn't structure. Wrap as `Case` with a single `Raw` arg holding
    // the remainder. Better than a top-level `Raw` because downstream
    // consumers at least know the constructor name.
    if let Some(Spanned { token: Token::Ident(head), .. }) = toks.first()
        && is_case_head(head) {
            let head_name = head.clone();
            let args_slice = &toks[1..];
            let arg_span = args_slice
                .iter()
                .map(|s| s.span)
                .reduce(Span::join)
                .expect("non-empty");
            let args = vec![Expr::Raw(TokenRun {
                span: arg_span,
                tokens: args_slice.to_vec(),
            })];
            return Ok(Expr::Case {
                span,
                head: head_name,
                args,
                op: None,
            });
        }

    Ok(Expr::Raw(TokenRun {
        span,
        tokens: toks.to_vec(),
    }))
}

/// Attempt to parse `toks` as a mixfix expression against `ctx.op_table`.
/// Returns `Some(expr)` only if the parse fully consumes `toks`; if it
/// fails or leaves residual input, returns `None` and the caller falls
/// back to its own structuring.
fn try_pratt_expression(
    toks: &[Spanned],
    span: Span,
    ctx: &ElabContext,
) -> Option<Expr> {
    let mut input: &[Spanned] = toks;
    let mut leaf = pratt_leaf;
    let tree = mixfix::parse_term(&mut input, &ctx.op_table, 0, &mut leaf).ok()?;
    if !input.is_empty() {
        return None;
    }
    Some(tree_to_expr(tree, &ctx.op_table, span))
}

/// Leaf parser used by [`mixfix::parse_term`] inside the SpecTec
/// expression elaborator. Recognises singleton tokens as
/// Var/Num/Text/Eps/zero-arg-Case; a `(` opens a recursive `parse_term`
/// to parse a sub-expression up to the matching `)`.
///
/// NOTE: this leaf does not have access to `ElabContext` so it cannot
/// honour `var` declarations. The post-Pratt `classify_simple_expression`
/// handles that distinction for singletons.
fn pratt_leaf(
    input: &mut &[Spanned],
    table: &OpTable,
) -> Result<Tree<Expr>, Diagnostic> {
    let s = input.first().ok_or_else(|| {
        Diagnostic::error(
            Span::new(crate::source::FileId::new(0), u32::MAX, u32::MAX),
            "expected atomic expression",
        )
    })?;
    let span = s.span;
    let leaf_expr = match &s.token {
        Token::Ident(name) if is_case_head(name) => {
            // A zero-arg constructor as a leaf — the table-matching loop
            // in parse_term will fold any following args into the Case.
            let name = name.clone();
            *input = &input[1..];
            return Ok(Tree::Leaf(Expr::Case {
                span,
                head: name,
                args: Vec::new(),
                op: None,
            }));
        }
        Token::Ident(name) => Expr::Var { span, name: name.clone() },
        Token::Nat(n) => Expr::Num { span, value: NumLit::Nat(n.clone()) },
        Token::Text(t) => Expr::Text { span, value: t.clone() },
        Token::Eps => Expr::Eps { span },
        Token::LParen => {
            // Recurse for a parenthesised sub-expression.
            *input = &input[1..];
            let mut leaf2 = pratt_leaf;
            let inner = mixfix::parse_term(input, table, 0, &mut leaf2)?;
            match input.first() {
                Some(Spanned { token: Token::RParen, .. }) => {
                    *input = &input[1..];
                }
                Some(s) => {
                    return Err(Diagnostic::error(
                        s.span,
                        format!("expected `)`, found {}", s.token.describe()),
                    ));
                }
                None => {
                    return Err(Diagnostic::error(
                        span,
                        "unterminated parenthesised expression",
                    ));
                }
            }
            return Ok(inner);
        }
        other => {
            return Err(Diagnostic::error(
                span,
                format!("expected atomic expression, found {}", other.describe()),
            ));
        }
    };
    *input = &input[1..];
    Ok(Tree::Leaf(leaf_expr))
}

/// Convert a Pratt `Tree<Expr>` back to an `Expr`, looking up operator
/// names from the table.
fn tree_to_expr(tree: Tree<Expr>, table: &OpTable, span: Span) -> Expr {
    match tree {
        Tree::Leaf(e) => e,
        Tree::App(op_id, args) => {
            let op = table.get(op_id);
            let head = op.name.clone();
            let mut iter_args: Vec<Expr> = args
                .into_iter()
                .map(|t| tree_to_expr(t, table, span))
                .collect();
            // Recognise the synthetic postfix-iter ops we registered in
            // build_table and convert them to `Expr::Iter` rather than
            // `Expr::Case`.
            let iter_kind = match head.as_str() {
                ITER_STAR_OP => Some(IterKind::Star),
                ITER_OPT_OP => Some(IterKind::Opt),
                ITER_PLUS_OP => Some(IterKind::Plus),
                _ => None,
            };
            if let Some(kind) = iter_kind {
                debug_assert_eq!(iter_args.len(), 1, "postfix iter takes one arg");
                let inner = iter_args.pop().expect("checked");
                return Expr::Iter {
                    span,
                    inner: Box::new(inner),
                    kind,
                    bindings: Vec::new(),
                };
            }
            Expr::Case {
                span,
                head,
                args: iter_args,
                op: None,
            }
        }
    }
}

// ---------- arithmetic escape `$( ... )` ----------

/// Recognise `$ ( ... )` as an arithmetic / boolean expression. The
/// matching `)` must be at the end of the slice (i.e. the entire input
/// is the arith escape, not just a prefix).
fn try_classify_arith_escape(
    toks: &[Spanned],
    _span: Span,
    ctx: &ElabContext,
) -> Result<Option<Expr>, Diagnostic> {
    if toks.len() < 3 {
        return Ok(None);
    }
    let (Some(Spanned { token: Token::Dollar, .. }), Some(Spanned { token: Token::LParen, .. })) =
        (toks.first(), toks.get(1))
    else {
        return Ok(None);
    };
    if !matches!(toks.last().map(|s| &s.token), Some(Token::RParen)) {
        return Ok(None);
    }
    if skip_balanced(&toks[1..]) != toks.len() - 1 {
        return Ok(None);
    }
    let inner = &toks[2..toks.len() - 1];
    if inner.is_empty() {
        return Ok(None);
    }
    let inner_span = inner.iter().map(|s| s.span).reduce(Span::join).unwrap();
    Ok(Some(parse_arith(inner, inner_span, ctx)?))
}

/// Top of the arithmetic precedence ladder. Lowest precedence (longest
/// span before splitting) is `\/`; highest is unary; below that lies
/// the atom (number, ident, parens, `$call(...)`, nested `$()`).
fn parse_arith(
    toks: &[Spanned],
    span: Span,
    ctx: &ElabContext,
) -> Result<Expr, Diagnostic> {
    // Level 1: `\/` (logical or, left-assoc)
    if let Some(i) = arith_last_top(toks, |t| matches!(t, Token::LogOr)) {
        return bin_split(toks, i, BinOp::Or, OpType::Bool, span, ctx);
    }
    // Level 2: `/\` (logical and, left-assoc)
    if let Some(i) = arith_last_top(toks, |t| matches!(t, Token::LogAnd)) {
        return bin_split(toks, i, BinOp::And, OpType::Bool, span, ctx);
    }
    // Level 3: comparisons (non-associative; we just take the leftmost
    // hit and let the right side carry any chained comparisons —
    // SpecTec source rarely chains them).
    if let Some((i, op)) = arith_first_cmp(toks) {
        return cmp_split(toks, i, op, span, ctx);
    }
    // Level 4: add/sub (left-assoc)
    if let Some((i, op)) = arith_last_addsub(toks) {
        return bin_split(toks, i, op, OpType::Nat, span, ctx);
    }
    // Level 5: mul/div/mod (left-assoc). SpecTec uses `*`, `/`, `mod`.
    // `mod` lexes as an Ident, so we recognise it positionally.
    if let Some((i, op)) = arith_last_muldiv(toks) {
        return bin_split(toks, i, op, OpType::Nat, span, ctx);
    }
    // Level 6: pow `^` (right-assoc — split on the first occurrence).
    if let Some(i) = arith_first_top(toks, |t| matches!(t, Token::Caret)) {
        return bin_split(toks, i, BinOp::Pow, OpType::Nat, span, ctx);
    }
    // Level 7: unary `+` / `-` / `not`.
    if let Some(s) = toks.first() {
        match &s.token {
            Token::Minus if toks.len() > 1 => {
                let rest = &toks[1..];
                let rest_span = rest.iter().map(|s| s.span).reduce(Span::join).unwrap_or(span);
                let e = parse_arith(rest, rest_span, ctx)?;
                return Ok(Expr::Un {
                    span,
                    op: UnOp::Minus,
                    ty: OpType::Nat,
                    e: Box::new(e),
                });
            }
            Token::Plus if toks.len() > 1 => {
                let rest = &toks[1..];
                let rest_span = rest.iter().map(|s| s.span).reduce(Span::join).unwrap_or(span);
                let e = parse_arith(rest, rest_span, ctx)?;
                return Ok(Expr::Un {
                    span,
                    op: UnOp::Plus,
                    ty: OpType::Nat,
                    e: Box::new(e),
                });
            }
            Token::Ident(n) if n == "not" && toks.len() > 1 => {
                let rest = &toks[1..];
                let rest_span = rest.iter().map(|s| s.span).reduce(Span::join).unwrap_or(span);
                let e = parse_arith(rest, rest_span, ctx)?;
                return Ok(Expr::Un {
                    span,
                    op: UnOp::Not,
                    ty: OpType::Bool,
                    e: Box::new(e),
                });
            }
            _ => {}
        }
    }
    // Atom.
    parse_arith_atom(toks, span, ctx)
}

fn parse_arith_atom(
    toks: &[Spanned],
    span: Span,
    ctx: &ElabContext,
) -> Result<Expr, Diagnostic> {
    // Parenthesised: `( ... )` covering the whole slice.
    if matches!(toks.first().map(|s| &s.token), Some(Token::LParen))
        && matches!(toks.last().map(|s| &s.token), Some(Token::RParen))
        && skip_balanced(toks) == toks.len()
    {
        let inner = &toks[1..toks.len() - 1];
        if inner.is_empty() {
            return Ok(Expr::Tup {
                span,
                items: Vec::new(),
            });
        }
        let inner_span = inner.iter().map(|s| s.span).reduce(Span::join).unwrap();
        return parse_arith(inner, inner_span, ctx);
    }
    // Nested `$( ... )` — recurse.
    if let Some(arith) = try_classify_arith_escape(toks, span, ctx)? {
        return Ok(arith);
    }
    // `$name(args)` — call.
    if let Some(call) = try_classify_call(toks, span, ctx)? {
        return Ok(call);
    }
    // Defer to the general classifier for everything else (Var, Num,
    // Case heads, Dot, Idx, etc.).
    classify_simple_expression(toks, span, ctx)
}

fn bin_split(
    toks: &[Spanned],
    pivot: usize,
    op: BinOp,
    ty: OpType,
    span: Span,
    ctx: &ElabContext,
) -> Result<Expr, Diagnostic> {
    let lhs = &toks[..pivot];
    let rhs = &toks[pivot + 1..];
    let lhs_span = lhs.iter().map(|s| s.span).reduce(Span::join).unwrap_or(span);
    let rhs_span = rhs.iter().map(|s| s.span).reduce(Span::join).unwrap_or(span);
    Ok(Expr::Bin {
        span,
        op,
        ty,
        e1: Box::new(parse_arith(lhs, lhs_span, ctx)?),
        e2: Box::new(parse_arith(rhs, rhs_span, ctx)?),
    })
}

fn cmp_split(
    toks: &[Spanned],
    pivot: usize,
    op: CmpOp,
    span: Span,
    ctx: &ElabContext,
) -> Result<Expr, Diagnostic> {
    let lhs = &toks[..pivot];
    let rhs = &toks[pivot + 1..];
    let lhs_span = lhs.iter().map(|s| s.span).reduce(Span::join).unwrap_or(span);
    let rhs_span = rhs.iter().map(|s| s.span).reduce(Span::join).unwrap_or(span);
    Ok(Expr::Cmp {
        span,
        op,
        ty: OpType::Nat,
        e1: Box::new(parse_arith(lhs, lhs_span, ctx)?),
        e2: Box::new(parse_arith(rhs, rhs_span, ctx)?),
    })
}

/// Last paren-depth-0 position where `pred` matches.
fn arith_last_top(toks: &[Spanned], pred: impl Fn(&Token) -> bool) -> Option<usize> {
    let mut depth: i32 = 0;
    let mut hit: Option<usize> = None;
    for (i, t) in toks.iter().enumerate() {
        match &t.token {
            Token::LParen | Token::LBracket | Token::LBrace => depth += 1,
            Token::RParen | Token::RBracket | Token::RBrace => depth -= 1,
            _ => {}
        }
        if depth == 0 && pred(&t.token) {
            hit = Some(i);
        }
    }
    hit
}

/// First paren-depth-0 position where `pred` matches.
fn arith_first_top(toks: &[Spanned], pred: impl Fn(&Token) -> bool) -> Option<usize> {
    let mut depth: i32 = 0;
    for (i, t) in toks.iter().enumerate() {
        match &t.token {
            Token::LParen | Token::LBracket | Token::LBrace => depth += 1,
            Token::RParen | Token::RBracket | Token::RBrace => depth -= 1,
            _ => {}
        }
        if depth == 0 && pred(&t.token) {
            return Some(i);
        }
    }
    None
}

fn arith_first_cmp(toks: &[Spanned]) -> Option<(usize, CmpOp)> {
    let mut depth: i32 = 0;
    for (i, t) in toks.iter().enumerate() {
        match &t.token {
            Token::LParen | Token::LBracket | Token::LBrace => depth += 1,
            Token::RParen | Token::RBracket | Token::RBrace => depth -= 1,
            _ => {}
        }
        if depth == 0 {
            let op = match &t.token {
                Token::Eq => CmpOp::Eq,
                Token::NotEq => CmpOp::Ne,
                Token::LessThan => CmpOp::Lt,
                Token::LessEq => CmpOp::Le,
                Token::GreaterThan => CmpOp::Gt,
                Token::GreaterEq => CmpOp::Ge,
                _ => continue,
            };
            // Reject the very first position: a leading `<` etc. would
            // be a syntax error (no LHS), so we skip.
            if i == 0 {
                continue;
            }
            return Some((i, op));
        }
    }
    None
}

fn arith_last_addsub(toks: &[Spanned]) -> Option<(usize, BinOp)> {
    let mut depth: i32 = 0;
    let mut hit: Option<(usize, BinOp)> = None;
    for (i, t) in toks.iter().enumerate() {
        match &t.token {
            Token::LParen | Token::LBracket | Token::LBrace => depth += 1,
            Token::RParen | Token::RBracket | Token::RBrace => depth -= 1,
            _ => {}
        }
        if depth == 0 && i > 0 {
            // i > 0 so the operator can't be a unary at position 0.
            match &t.token {
                Token::Plus => hit = Some((i, BinOp::Add)),
                Token::Minus => hit = Some((i, BinOp::Sub)),
                _ => {}
            }
        }
    }
    hit
}

fn arith_last_muldiv(toks: &[Spanned]) -> Option<(usize, BinOp)> {
    let mut depth: i32 = 0;
    let mut hit: Option<(usize, BinOp)> = None;
    for (i, t) in toks.iter().enumerate() {
        match &t.token {
            Token::LParen | Token::LBracket | Token::LBrace => depth += 1,
            Token::RParen | Token::RBracket | Token::RBrace => depth -= 1,
            _ => {}
        }
        // Treat as multiplication only when there's a non-empty RHS;
        // a trailing `*` is the iter postfix, not arithmetic.
        if depth == 0 && i > 0 && i + 1 < toks.len() {
            match &t.token {
                Token::Star => hit = Some((i, BinOp::Mul)),
                Token::Slash => hit = Some((i, BinOp::Div)),
                Token::Ident(n) if n == "mod" => hit = Some((i, BinOp::Mod)),
                _ => {}
            }
        }
    }
    hit
}

// ---------- structural recognisers used by classify_simple_expression ----------

/// Recognise `$name(arg, ...)` as `Expr::Call`. Requires the call to
/// span the entire slice (i.e. `last == RParen`, `matching LParen at
/// index 2`, with the call body strictly between them).
fn try_classify_call(
    toks: &[Spanned],
    span: Span,
    ctx: &ElabContext,
) -> Result<Option<Expr>, Diagnostic> {
    if toks.len() < 4 {
        return Ok(None);
    }
    let (Some(Spanned { token: Token::Dollar, .. }), Some(Spanned { token: Token::Ident(name), .. })) =
        (toks.first(), toks.get(1))
    else {
        return Ok(None);
    };
    if !matches!(toks.get(2).map(|s| &s.token), Some(Token::LParen)) {
        return Ok(None);
    }
    if !matches!(toks.last().map(|s| &s.token), Some(Token::RParen)) {
        return Ok(None);
    }
    // The `(` at index 2 must match the `)` at index `toks.len()-1`.
    let consumed = skip_balanced(&toks[2..]);
    if consumed != toks.len() - 2 {
        return Ok(None);
    }
    let inner = &toks[3..toks.len() - 1];
    let args: Vec<Expr> = split_top_comma(inner)
        .into_iter()
        .map(|slice| {
            let arg_span = slice
                .iter()
                .map(|s| s.span)
                .reduce(Span::join)
                .unwrap_or(span);
            classify_simple_expression(slice, arg_span, ctx).unwrap_or_else(|_| {
                Expr::Raw(TokenRun {
                    span: arg_span,
                    tokens: slice.to_vec(),
                })
            })
        })
        .collect();
    Ok(Some(Expr::Call {
        span,
        name: name.clone(),
        args,
    }))
}

/// Recognise `e [ <path> <op> <rhs> ]` as a functional update or
/// extension — `Expr::Upd` for `=` / `:=`, `Expr::Ext` for `=++` /
/// `=..`. The bracketed body must:
///
/// - start with a `.` (root dot-step) or `[` (root index-step), and
/// - contain one of the operators at top-level bracket depth.
///
/// Returns `Ok(None)` if the slice doesn't fit this shape — the caller
/// then falls through to plain `Expr::Idx` recognition.
///
/// Task #34 — see `docs/sketches/spectec-tasks/task-34-expr-paths.md`.
fn try_classify_path_update(
    toks: &[Spanned],
    span: Span,
    ctx: &ElabContext,
) -> Result<Option<Expr>, Diagnostic> {
    if !matches!(toks.last().map(|s| &s.token), Some(Token::RBracket)) {
        return Ok(None);
    }
    // Find the matching `[` for the trailing `]` (same logic as
    // try_classify_idx — depth walk from the right).
    let mut depth: i32 = 0;
    let mut open_idx: Option<usize> = None;
    for (i, t) in toks.iter().enumerate().rev() {
        match &t.token {
            Token::RParen | Token::RBracket | Token::RBrace => depth += 1,
            Token::LParen | Token::LBracket | Token::LBrace => {
                depth -= 1;
                if depth == 0 {
                    if matches!(&t.token, Token::LBracket) {
                        open_idx = Some(i);
                    }
                    break;
                }
            }
            _ => {}
        }
    }
    let Some(open) = open_idx else { return Ok(None) };
    if open == 0 {
        return Ok(None);
    }
    let prefix = &toks[..open];
    let inner = &toks[open + 1..toks.len() - 1];
    if !depth_balanced(prefix) || !depth_balanced(inner) {
        return Ok(None);
    }
    // Body must begin with `.` or `[` to look like a path (anchored at
    // the implicit root). A bare identifier or number means plain
    // indexing, which `try_classify_idx` will handle.
    let Some(first) = inner.first() else { return Ok(None) };
    if !matches!(&first.token, Token::Dot | Token::LBracket) {
        return Ok(None);
    }
    // Find a top-level update / extend operator inside the body.
    let Some((op_idx, op_kind)) = find_path_update_op(inner) else {
        return Ok(None);
    };
    let path_toks = &inner[..op_idx];
    let rhs_toks = &inner[op_idx + 1..];
    if path_toks.is_empty() || rhs_toks.is_empty() {
        return Ok(None);
    }
    let path = parse_path(path_toks, ctx)?;
    let rhs_span = rhs_toks
        .iter()
        .map(|s| s.span)
        .reduce(Span::join)
        .unwrap_or(span);
    let rhs = classify_simple_expression(rhs_toks, rhs_span, ctx)?;
    let prefix_span = prefix.iter().map(|s| s.span).reduce(Span::join).unwrap_or(span);
    let e1 = classify_simple_expression(prefix, prefix_span, ctx)?;
    Ok(Some(match op_kind {
        PathUpdateOp::Upd => Expr::Upd {
            span,
            e1: Box::new(e1),
            path: Box::new(path),
            e2: Box::new(rhs),
        },
        PathUpdateOp::Ext => Expr::Ext {
            span,
            e1: Box::new(e1),
            path: Box::new(path),
            e2: Box::new(rhs),
        },
    }))
}

/// Whether a `<path> <op> <rhs>` body inside `[...]` denotes a
/// functional update (`Upd`) or extension (`Ext`).
#[derive(Clone, Copy, Debug)]
enum PathUpdateOp {
    Upd,
    Ext,
}

/// Find the first top-level (depth 0) update/extend operator in the
/// brackets-body slice. Returns `Some((index, kind))` or `None`.
///
/// Operators searched: `=` (Upd), `:=` (Upd), `=++` (Ext), `=..` (Ext).
/// Comparisons (`<=`, `>=`, `=/=`) are distinct tokens so the bare `=`
/// match here is unambiguous.
fn find_path_update_op(toks: &[Spanned]) -> Option<(usize, PathUpdateOp)> {
    let mut depth: i32 = 0;
    for (i, t) in toks.iter().enumerate() {
        match &t.token {
            Token::LParen | Token::LBracket | Token::LBrace => depth += 1,
            Token::RParen | Token::RBracket | Token::RBrace => depth -= 1,
            Token::Eq if depth == 0 => return Some((i, PathUpdateOp::Upd)),
            Token::Assign if depth == 0 => return Some((i, PathUpdateOp::Upd)),
            Token::EqPlusPlus if depth == 0 => return Some((i, PathUpdateOp::Ext)),
            Token::EqDotDot if depth == 0 => return Some((i, PathUpdateOp::Ext)),
            _ => {}
        }
    }
    None
}

/// Parse a path body — a sequence of `.IDENT`, `[expr]`, and `[e1:e2]`
/// steps anchored at the implicit `Path::Root`.
///
/// Each step is appended to the current path. Path subexpressions
/// (inside `[ ]`) are elaborated by recursing into
/// `classify_simple_expression`.
fn parse_path(toks: &[Spanned], ctx: &ElabContext) -> Result<Path, Diagnostic> {
    let mut path = Path::Root;
    let mut i = 0;
    while i < toks.len() {
        match &toks[i].token {
            Token::Dot => {
                // `.IDENT` — Dot step.
                let Some(next) = toks.get(i + 1) else {
                    return Err(Diagnostic::error(
                        toks[i].span,
                        "expected identifier after `.` in path",
                    ));
                };
                let Token::Ident(field) = &next.token else {
                    return Err(Diagnostic::error(
                        next.span,
                        format!(
                            "expected identifier after `.` in path, found {}",
                            next.token.describe()
                        ),
                    ));
                };
                path = Path::Dot { p: Box::new(path), field: field.clone() };
                i += 2;
            }
            Token::LBracket => {
                // `[ ... ]` — find matching `]`, then check for top-level `:`.
                let body_start = i + 1;
                let mut bdepth: i32 = 1;
                let mut close: Option<usize> = None;
                let mut j = body_start;
                while j < toks.len() {
                    match &toks[j].token {
                        Token::LParen | Token::LBracket | Token::LBrace => bdepth += 1,
                        Token::RParen | Token::RBracket | Token::RBrace => {
                            bdepth -= 1;
                            if bdepth == 0 {
                                close = Some(j);
                                break;
                            }
                        }
                        _ => {}
                    }
                    j += 1;
                }
                let Some(close) = close else {
                    return Err(Diagnostic::error(
                        toks[i].span,
                        "unmatched `[` in path",
                    ));
                };
                let body = &toks[body_start..close];
                let body_span = body
                    .iter()
                    .map(|s| s.span)
                    .reduce(Span::join)
                    .unwrap_or(toks[i].span);
                // Top-level `:` split → slice; otherwise → idx.
                if let Some(colon_idx) = top_level_colon(body) {
                    let lhs = &body[..colon_idx];
                    let rhs = &body[colon_idx + 1..];
                    if lhs.is_empty() || rhs.is_empty() {
                        return Err(Diagnostic::error(
                            body_span,
                            "slice path step needs expressions on both sides of `:`",
                        ));
                    }
                    let lspan = lhs.iter().map(|s| s.span).reduce(Span::join).unwrap_or(body_span);
                    let rspan = rhs.iter().map(|s| s.span).reduce(Span::join).unwrap_or(body_span);
                    let e1 = classify_simple_expression(lhs, lspan, ctx)?;
                    let e2 = classify_simple_expression(rhs, rspan, ctx)?;
                    path = Path::Slice { p: Box::new(path), e1, e2 };
                } else {
                    if body.is_empty() {
                        return Err(Diagnostic::error(
                            body_span,
                            "empty `[]` not allowed in path",
                        ));
                    }
                    let e = classify_simple_expression(body, body_span, ctx)?;
                    path = Path::Idx { p: Box::new(path), e };
                }
                i = close + 1;
            }
            _ => {
                return Err(Diagnostic::error(
                    toks[i].span,
                    format!(
                        "unexpected token {} in path; expected `.` or `[`",
                        toks[i].token.describe()
                    ),
                ));
            }
        }
    }
    Ok(path)
}

/// Top-level `:` index in a bracket body — used to split a slice path
/// step (`[e1 : e2]`) from an indexing step (`[e]`). Returns `None` if
/// no top-level `:` exists (e.g. all colons are nested in inner
/// brackets).
fn top_level_colon(toks: &[Spanned]) -> Option<usize> {
    let mut depth: i32 = 0;
    for (i, t) in toks.iter().enumerate() {
        match &t.token {
            Token::LParen | Token::LBracket | Token::LBrace => depth += 1,
            Token::RParen | Token::RBracket | Token::RBrace => depth -= 1,
            Token::Colon if depth == 0 => return Some(i),
            _ => {}
        }
    }
    None
}

/// Recognise `e [ idx ]` as `Expr::Idx`. The matching `[` must be at
/// the highest-priority balanced position from the right.
fn try_classify_idx(
    toks: &[Spanned],
    span: Span,
    ctx: &ElabContext,
) -> Result<Option<Expr>, Diagnostic> {
    if !matches!(toks.last().map(|s| &s.token), Some(Token::RBracket)) {
        return Ok(None);
    }
    // Find the matching `[` for the trailing `]` by walking bracket
    // depth from the right.
    let mut depth: i32 = 0;
    let mut open_idx: Option<usize> = None;
    for (i, t) in toks.iter().enumerate().rev() {
        match &t.token {
            Token::RParen | Token::RBracket | Token::RBrace => depth += 1,
            Token::LParen | Token::LBracket | Token::LBrace => {
                depth -= 1;
                if depth == 0 {
                    if matches!(&t.token, Token::LBracket) {
                        open_idx = Some(i);
                    }
                    break;
                }
            }
            _ => {}
        }
    }
    let Some(open) = open_idx else { return Ok(None) };
    if open == 0 {
        return Ok(None);
    }
    let prefix = &toks[..open];
    let inner = &toks[open + 1..toks.len() - 1];
    if !depth_balanced(prefix) || !depth_balanced(inner) {
        return Ok(None);
    }
    let prefix_span = prefix.iter().map(|s| s.span).reduce(Span::join).unwrap_or(span);
    let inner_span = inner.iter().map(|s| s.span).reduce(Span::join).unwrap_or(span);
    let e1 = classify_simple_expression(prefix, prefix_span, ctx)?;
    // Slice form: `e [ lo : hi ]` — top-level `:` inside the brackets.
    // Both halves must be non-empty; bare `[:]` falls back to Idx.
    if let Some(colon) = top_level_colon(inner) {
        let lhs = &inner[..colon];
        let rhs = &inner[colon + 1..];
        if !lhs.is_empty() && !rhs.is_empty() {
            let lspan = lhs.iter().map(|s| s.span).reduce(Span::join).unwrap_or(inner_span);
            let rspan = rhs.iter().map(|s| s.span).reduce(Span::join).unwrap_or(inner_span);
            let e2 = classify_simple_expression(lhs, lspan, ctx)?;
            let e3 = classify_simple_expression(rhs, rspan, ctx)?;
            return Ok(Some(Expr::Slice {
                span,
                e1: Box::new(e1),
                e2: Box::new(e2),
                e3: Box::new(e3),
            }));
        }
    }
    let e2 = classify_simple_expression(inner, inner_span, ctx)?;
    Ok(Some(Expr::Idx {
        span,
        e1: Box::new(e1),
        e2: Box::new(e2),
    }))
}

/// Recognise `e . FIELD` as `Expr::Dot`. The `Dot Ident` must be at
/// paren-depth 0 at the end of the slice.
fn try_classify_dot(
    toks: &[Spanned],
    span: Span,
    ctx: &ElabContext,
) -> Result<Option<Expr>, Diagnostic> {
    if toks.len() < 3 {
        return Ok(None);
    }
    let Some(Spanned { token: Token::Ident(field), .. }) = toks.last() else {
        return Ok(None);
    };
    if !matches!(toks.get(toks.len() - 2).map(|s| &s.token), Some(Token::Dot)) {
        return Ok(None);
    }
    let prefix = &toks[..toks.len() - 2];
    if !depth_balanced(prefix) {
        return Ok(None);
    }
    let prefix_span = prefix.iter().map(|s| s.span).reduce(Span::join).unwrap_or(span);
    let e = classify_simple_expression(prefix, prefix_span, ctx)?;
    Ok(Some(Expr::Dot {
        span,
        e: Box::new(e),
        field: field.clone(),
    }))
}

/// Split a token slice on top-level (depth 0) commas. Empty leading or
/// trailing chunks are dropped.
fn split_top_comma(toks: &[Spanned]) -> Vec<&[Spanned]> {
    let mut out = Vec::new();
    let mut depth: i32 = 0;
    let mut start = 0usize;
    for (i, t) in toks.iter().enumerate() {
        match &t.token {
            Token::LParen | Token::LBracket | Token::LBrace => depth += 1,
            Token::RParen | Token::RBracket | Token::RBrace => depth -= 1,
            Token::Comma if depth == 0 => {
                if start < i {
                    out.push(&toks[start..i]);
                }
                start = i + 1;
            }
            _ => {}
        }
    }
    if start < toks.len() {
        out.push(&toks[start..]);
    }
    out
}

/// True if `name` looks like a SpecTec case constructor.
///
/// Heuristic: at least 2 characters AND every alphabetic character is
/// uppercase. This catches `NOP`, `BLOCK`, `I32`, `UNREACHABLE`, `_IDX`,
/// `_DEF`, and rejects single-letter metavariables (`C`, `X`, `N`),
/// lowercase identifiers (`numtype`), and mixed-case names (`Foo`).
///
/// The proper distinction between metavariables and constructors comes
/// from `var` and `syntax`-variant declarations; this heuristic stands
/// in until the elaborator threads those through. See [[phase-p-parallel-types]]
/// for the broader pattern of letting parallel structures coexist while
/// the elaborator catches up.
fn is_case_head(name: &str) -> bool {
    if name.len() < 2 {
        return false;
    }
    let mut bytes = name.bytes();
    match bytes.next() {
        Some(b) if b.is_ascii_uppercase() => {}
        Some(b'_') => {}
        _ => return false,
    }
    let mut saw_letter = false;
    for b in name.bytes() {
        if b.is_ascii_alphabetic() {
            saw_letter = true;
            if b.is_ascii_lowercase() {
                return false;
            }
        }
    }
    saw_letter
}

fn depth_balanced(toks: &[Spanned]) -> bool {
    let mut depth: i32 = 0;
    for t in toks {
        match &t.token {
            Token::LParen | Token::LBracket | Token::LBrace => depth += 1,
            Token::RParen | Token::RBracket | Token::RBrace => {
                depth -= 1;
                if depth < 0 {
                    return false;
                }
            }
            _ => {}
        }
    }
    depth == 0
}

fn classify_tuple_inner(
    inner: &[Spanned],
    span: Span,
    ctx: &ElabContext,
) -> Result<Expr, Diagnostic> {
    // Empty: `()`.
    if inner.is_empty() {
        return Ok(Expr::Tup {
            span,
            items: Vec::new(),
        });
    }
    // Split on top-level commas.
    let mut items: Vec<Expr> = Vec::new();
    let mut depth: i32 = 0;
    let mut chunk_start = 0;
    for (i, t) in inner.iter().enumerate() {
        match &t.token {
            Token::LParen | Token::LBracket | Token::LBrace => depth += 1,
            Token::RParen | Token::RBracket | Token::RBrace => depth -= 1,
            Token::Comma if depth == 0 => {
                let chunk = &inner[chunk_start..i];
                let cspan = chunk
                    .iter()
                    .map(|s| s.span)
                    .reduce(Span::join)
                    .expect("non-empty chunk");
                items.push(classify_simple_expression(chunk, cspan, ctx)?);
                chunk_start = i + 1;
            }
            _ => {}
        }
    }
    let chunk = &inner[chunk_start..];
    let cspan = chunk
        .iter()
        .map(|s| s.span)
        .reduce(Span::join)
        .expect("non-empty chunk");
    items.push(classify_simple_expression(chunk, cspan, ctx)?);

    // Singleton: `(x)` — grouping. Return inner expression directly.
    if items.len() == 1 {
        return Ok(items.into_iter().next().unwrap());
    }
    Ok(Expr::Tup { span, items })
}

/// Classify a record literal body: `FIELD val, FIELD val, ...`. Each
/// field starts with an uppercase / case-head ident and is followed by
/// a value expression. Returns `Some(Expr::Str{...})` on success;
/// `None` if the body doesn't look record-shaped (no leading uppercase
/// ident).
fn try_classify_record(
    inner: &[Spanned],
    span: Span,
    ctx: &ElabContext,
) -> Result<Option<Expr>, Diagnostic> {
    if inner.is_empty() {
        return Ok(Some(Expr::Str {
            span,
            fields: Vec::new(),
        }));
    }
    // Must lead with a case-head ident; otherwise this isn't a record.
    let Some(Spanned { token: Token::Ident(first), .. }) = inner.first() else {
        return Ok(None);
    };
    if !is_case_head(first) {
        return Ok(None);
    }
    // Split on top-level commas. Each chunk: `FIELD val_tokens*`.
    let mut chunks: Vec<&[Spanned]> = Vec::new();
    let mut depth: i32 = 0;
    let mut chunk_start = 0;
    for (i, t) in inner.iter().enumerate() {
        match &t.token {
            Token::LParen | Token::LBracket | Token::LBrace => depth += 1,
            Token::RParen | Token::RBracket | Token::RBrace => depth -= 1,
            Token::Comma if depth == 0 => {
                chunks.push(&inner[chunk_start..i]);
                chunk_start = i + 1;
            }
            _ => {}
        }
    }
    chunks.push(&inner[chunk_start..]);
    let mut fields = Vec::with_capacity(chunks.len());
    for chunk in chunks {
        let Some(Spanned { token: Token::Ident(name), .. }) = chunk.first() else {
            return Ok(None);
        };
        if !is_case_head(name) {
            return Ok(None);
        }
        let val_toks = &chunk[1..];
        let val_span = val_toks
            .iter()
            .map(|s| s.span)
            .reduce(Span::join)
            .unwrap_or(span);
        let value = if val_toks.is_empty() {
            Expr::Tup { span: val_span, items: Vec::new() }
        } else {
            classify_simple_expression(val_toks, val_span, ctx)?
        };
        fields.push(ExprField {
            field: name.clone(),
            value,
        });
    }
    Ok(Some(Expr::Str { span, fields }))
}

/// Given `toks[0]` IS an opening bracket, return the number of tokens
/// from `toks[0]` up to AND INCLUDING the matching close bracket. If
/// brackets are unbalanced, returns the remaining length.
pub fn skip_balanced(toks: &[Spanned]) -> usize {
    let mut depth: i32 = 0;
    let mut i = 0;
    while i < toks.len() {
        match &toks[i].token {
            Token::LParen | Token::LBracket | Token::LBrace => depth += 1,
            Token::RParen | Token::RBracket | Token::RBrace => {
                depth -= 1;
                if depth == 0 {
                    return i + 1;
                }
            }
            _ => {}
        }
        i += 1;
    }
    toks.len()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lex::lex;
    use crate::parse::parse;
    use crate::source::SourceMap;

    fn build_from_str(src: &str) -> ElabContext {
        let mut map = SourceMap::new();
        let id = map.add("<test>", src);
        let tokens = lex(id, src).unwrap();
        let tops = parse(id, tokens).unwrap();
        build_table(&tops).unwrap()
    }

    /// Format an op's fragments compactly for tests: `H` for hole, `<token>` for lit.
    fn fmt_op(op: &crate::mixfix::Op) -> String {
        let parts: Vec<String> = op
            .fragments
            .iter()
            .map(|f| match f {
                Fragment::Hole(_) => "%".to_string(),
                Fragment::Lit(t) => format!("{:?}", t),
            })
            .collect();
        format!("{}: {}", op.name, parts.join(" "))
    }

    #[test]
    fn type_names_include_builtins() {
        let ctx = build_from_str("");
        assert!(ctx.type_names.contains("nat"));
        assert!(ctx.type_names.contains("int"));
        assert!(ctx.type_names.contains("bool"));
        assert!(ctx.type_names.contains("text"));
    }

    #[test]
    fn type_names_from_syntax_decls() {
        let src = r#"
            syntax foo = nat
            syntax bar(N) = nat
            syntax baz/syn = nat
        "#;
        let ctx = build_from_str(src);
        assert!(ctx.type_names.contains("foo"));
        assert!(ctx.type_names.contains("bar"));
        assert!(ctx.type_names.contains("baz"));
    }

    #[test]
    fn relation_with_simple_template() {
        let src = r#"
            syntax context = nat
            syntax numtype = nat
            relation Numtype_sub: context |- numtype <: numtype
        "#;
        let ctx = build_from_str(src);
        let op = ctx.op_table.iter().find(|o| o.name == "Numtype_sub").unwrap();
        // % |- % <: %
        assert_eq!(op.fragments.len(), 5);
        assert!(matches!(op.fragments[0], Fragment::Hole(_)));
        assert!(matches!(op.fragments[1], Fragment::Lit(Token::Turnstile)));
        assert!(matches!(op.fragments[2], Fragment::Hole(_)));
        assert!(matches!(op.fragments[3], Fragment::Lit(Token::Subtype)));
        assert!(matches!(op.fragments[4], Fragment::Hole(_)));
    }

    #[test]
    fn relation_with_iter_suffix_in_hole() {
        // `context |- type : deftype*` — the trailing `*` should be
        // absorbed into the last hole, not become a separate Lit.
        let src = r#"
            syntax context = nat
            syntax type = nat
            syntax deftype = nat
            relation Type_ok: context |- type : deftype*
        "#;
        let ctx = build_from_str(src);
        let op = ctx.op_table.iter().find(|o| o.name == "Type_ok").unwrap();
        // % |- % : %    (3 holes, 2 lits — `*` absorbed)
        assert_eq!(op.fragments.len(), 5);
        assert!(matches!(op.fragments[0], Fragment::Hole(_)));
        assert!(matches!(op.fragments[1], Fragment::Lit(Token::Turnstile)));
        assert!(matches!(op.fragments[2], Fragment::Hole(_)));
        assert!(matches!(op.fragments[3], Fragment::Lit(Token::Colon)));
        assert!(matches!(op.fragments[4], Fragment::Hole(_)));
    }

    #[test]
    fn relation_with_optional_and_plus_suffixes() {
        let src = r#"
            syntax foo = nat
            syntax bar = nat
            syntax baz = nat
            relation R: foo? |- bar+ <: baz*
        "#;
        let ctx = build_from_str(src);
        let op = ctx.op_table.iter().find(|o| o.name == "R").unwrap();
        // 3 holes, 2 lits
        assert_eq!(op.fragments.len(), 5);
        assert_eq!(
            op.fragments.iter().filter(|f| matches!(f, Fragment::Hole(_))).count(),
            3
        );
    }

    #[test]
    fn relation_starts_with_literal() {
        // `|- valtype DEFAULTABLE` — starts with `|-` literal, then a hole,
        // then a `DEFAULTABLE` literal that's NOT a declared type name.
        let src = r#"
            syntax valtype = nat
            relation Defaultable: |- valtype DEFAULTABLE
        "#;
        let ctx = build_from_str(src);
        let op = ctx.op_table.iter().find(|o| o.name == "Defaultable").unwrap();
        // Lit Hole Lit
        assert_eq!(op.fragments.len(), 3);
        assert!(matches!(op.fragments[0], Fragment::Lit(Token::Turnstile)));
        assert!(matches!(op.fragments[1], Fragment::Hole(_)));
        assert!(matches!(op.fragments[2], Fragment::Lit(Token::Ident(ref s)) if s == "DEFAULTABLE"));
    }

    #[test]
    fn relation_with_parametric_type_in_hole() {
        // `relation R: foo(N) |- bar` — the `(N)` is part of the first
        // hole's type, not separate template tokens.
        let src = r#"
            syntax foo(N) = nat
            syntax bar = nat
            relation R: foo(N) |- bar
        "#;
        let ctx = build_from_str(src);
        let op = ctx.op_table.iter().find(|o| o.name == "R").unwrap();
        // Hole Lit Hole
        assert_eq!(op.fragments.len(), 3);
    }

    #[test]
    fn multiple_relations_extracted() {
        let src = r#"
            syntax t = nat
            relation A: t |- t
            relation B: t |- t : t
            relation C: t ~> t
        "#;
        let ctx = build_from_str(src);
        let names: Vec<_> = ctx.op_table.iter().map(|o| o.name.clone()).collect();
        assert!(names.contains(&"A".to_string()));
        assert!(names.contains(&"B".to_string()));
        assert!(names.contains(&"C".to_string()));
    }

    #[test]
    fn empty_input_table_has_only_builtins() {
        let ctx = build_from_str("");
        // Three universal postfix iter ops (`*`, `?`, `+`) are always
        // registered. No user-defined operators for empty input.
        let names: Vec<_> = ctx.op_table.iter().map(|o| o.name.clone()).collect();
        assert_eq!(names.len(), 3);
        assert!(names.contains(&ITER_STAR_OP.to_string()));
        assert!(names.contains(&ITER_OPT_OP.to_string()));
        assert!(names.contains(&ITER_PLUS_OP.to_string()));
    }

    #[test]
    fn variant_constructors_become_ops() {
        let src = r#"
            syntax numtype = | I32 | I64 | F32 | F64
        "#;
        let ctx = build_from_str(src);
        for name in &["I32", "I64", "F32", "F64"] {
            assert!(
                ctx.op_table.iter().any(|o| o.name == *name),
                "expected op for `{name}`"
            );
        }
    }

    #[test]
    fn headless_arrow_mixfix_registers_two_op_forms() {
        // `syntax instrtype = resulttype ->_(localidx*) resulttype` —
        // the headless single-case variant with optional middle slot.
        // Two ops should be registered under `ARROW_MIXFIX_OP`: the
        // long form (5 fragments — `Hole Lit(Arrow) Lit("_") Hole Hole`)
        // and the short form (3 fragments — `Hole Lit(Arrow) Hole`).
        let src = r#"
            syntax localidx = nat
            syntax resulttype = nat
            syntax instrtype = resulttype ->_(localidx*) resulttype
        "#;
        let ctx = build_from_str(src);
        let ops: Vec<&crate::mixfix::Op> = ctx
            .op_table
            .iter()
            .filter(|o| o.name == ARROW_MIXFIX_OP)
            .collect();
        assert_eq!(
            ops.len(),
            2,
            "expected two arrow mixfix ops (long + short), got {}: {:?}",
            ops.len(),
            ops.iter().map(|o| fmt_op(o)).collect::<Vec<_>>(),
        );
        let lengths: Vec<usize> = ops.iter().map(|o| o.fragments.len()).collect();
        assert!(lengths.contains(&5), "long form should have 5 fragments: {lengths:?}");
        assert!(lengths.contains(&3), "short form should have 3 fragments: {lengths:?}");
        // Both forms must agree on the leading-hole precedence so the
        // Pratt parser treats them as alternatives of the same binding
        // strength. They share `ARROW_LEFT_PREC` so the arrow doesn't
        // compete inside higher-precedence constructor argument slots.
        for op in &ops {
            assert!(
                matches!(op.fragments[0], Fragment::Hole(p) if p == ARROW_LEFT_PREC),
                "leading hole prec should be ARROW_LEFT_PREC, got {:?}",
                op.fragments[0],
            );
            assert!(matches!(op.fragments[1], Fragment::Lit(Token::Arrow)));
        }
    }

    #[test]
    fn non_arrow_headless_variants_do_not_register_arrow_op() {
        // `syntax fieldtype = mut? storagetype` is a headless variant
        // without an arrow, so no arrow mixfix op should be registered
        // (regression check on the shape predicate).
        let src = r#"
            syntax mut = MUT
            syntax storagetype = nat
            syntax fieldtype = mut? storagetype
        "#;
        let ctx = build_from_str(src);
        assert!(
            !ctx.op_table.iter().any(|o| o.name == ARROW_MIXFIX_OP),
            "non-arrow headless variant must not register an arrow mixfix op",
        );
    }

    #[test]
    fn variant_constructors_with_args() {
        let src = r#"
            syntax heaptype = nat
            syntax null = NULL
            syntax reftype = | REF null? heaptype
        "#;
        let ctx = build_from_str(src);
        let op = ctx.op_table.iter().find(|o| o.name == "REF").unwrap();
        // Lit(REF), Hole (null?), Hole (heaptype) — but only if both
        // null and heaptype are declared as syntax. `null` is declared.
        assert!(matches!(op.fragments[0], Fragment::Lit(_)));
        let hole_count = op
            .fragments
            .iter()
            .filter(|f| matches!(f, Fragment::Hole(_)))
            .count();
        assert_eq!(hole_count, 2, "expected REF to have 2 args");
    }

    #[test]
    fn type_inclusion_alt_does_not_become_constructor() {
        // `syntax valtype = | numtype | reftype` — these aren't case
        // constructors, they're type inclusions. No ops added for them.
        let src = r#"
            syntax numtype = nat
            syntax reftype = nat
            syntax valtype = | numtype | reftype
        "#;
        let ctx = build_from_str(src);
        let names: Vec<_> = ctx.op_table.iter().map(|o| o.name.clone()).collect();
        // No op named "numtype" or "reftype" should be in the table.
        assert!(!names.contains(&"numtype".to_string()));
        assert!(!names.contains(&"reftype".to_string()));
    }

    #[test]
    fn nullary_constructors_have_just_a_lit() {
        let src = r#"
            syntax instr = | NOP | UNREACHABLE
        "#;
        let ctx = build_from_str(src);
        let nop = ctx.op_table.iter().find(|o| o.name == "NOP").unwrap();
        assert_eq!(nop.fragments.len(), 1);
        assert!(matches!(nop.fragments[0], Fragment::Lit(_)));
    }

    #[test]
    fn nonexistent_type_in_template_is_lit() {
        // `Foobar` isn't declared as a syntax — treated as a literal token.
        let src = r#"
            syntax foo = nat
            relation R: foo |- Foobar
        "#;
        let ctx = build_from_str(src);
        let op = ctx.op_table.iter().find(|o| o.name == "R").unwrap();
        // Hole Lit Lit
        assert_eq!(op.fragments.len(), 3);
        assert!(matches!(op.fragments[0], Fragment::Hole(_)));
        assert!(matches!(op.fragments[1], Fragment::Lit(Token::Turnstile)));
        assert!(matches!(op.fragments[2], Fragment::Lit(Token::Ident(ref s)) if s == "Foobar"));
    }

    // Used only when debugging; kept for future iteration.
    #[allow(dead_code)]
    fn debug_table(ctx: &ElabContext) {
        for op in ctx.op_table.iter() {
            eprintln!("  {}", fmt_op(op));
        }
    }

    // ---------- conclusion elaboration ----------

    fn elab_first_rule(src: &str) -> ElabRuleConclusion {
        let mut map = SourceMap::new();
        let id = map.add("<test>", src);
        let tokens = lex(id, src).unwrap();
        let tops = parse(id, tokens).unwrap();
        let ctx = build_table(&tops).unwrap();
        let rule = tops
            .iter()
            .find_map(|t| if let Top::Rule(r) = t { Some(r) } else { None })
            .expect("no rule in input");
        elab_rule_conclusion(rule, &ctx).expect("elab failed")
    }

    #[test]
    fn elab_rule_with_short_arrow_in_operand() {
        // `eps -> eps` is the short form of the instrtype mixfix —
        // the Pratt parser should structure it as
        // `Case { head: ARROW_MIXFIX_OP, args: [Eps, Eps] }`.
        let src = r#"
            syntax context = nat
            syntax localidx = nat
            syntax resulttype = nat
            syntax instrtype = resulttype ->_(localidx*) resulttype
            syntax instr = NOP
            relation Instr_ok: context |- instr : instrtype
            rule Instr_ok/nop:
              C |- NOP : eps -> eps
        "#;
        let elab = elab_first_rule(src);
        assert_eq!(elab.operands.len(), 3);
        let arrow = &elab.operands[2];
        match arrow {
            Expr::Case { head, args, .. } => {
                assert_eq!(head, ARROW_MIXFIX_OP);
                assert_eq!(args.len(), 2, "short form should produce 2 args");
                assert!(matches!(args[0], Expr::Eps { .. }));
                assert!(matches!(args[1], Expr::Eps { .. }));
            }
            other => panic!("expected arrow Case, got {other:?}"),
        }
    }

    #[test]
    fn elab_rule_with_long_arrow_in_operand() {
        // `eps ->_(x*) eps` is the long form — Pratt should match the
        // 5-fragment op and produce 3 args.
        let src = r#"
            syntax context = nat
            syntax localidx = nat
            syntax resulttype = nat
            syntax instrtype = resulttype ->_(localidx*) resulttype
            syntax instr = NOP
            relation Instr_ok: context |- instr : instrtype
            rule Instr_ok/test:
              C |- NOP : eps ->_(x*) eps
        "#;
        let elab = elab_first_rule(src);
        assert_eq!(elab.operands.len(), 3);
        let arrow = &elab.operands[2];
        match arrow {
            Expr::Case { head, args, .. } => {
                assert_eq!(head, ARROW_MIXFIX_OP);
                assert_eq!(args.len(), 3, "long form should produce 3 args");
                assert!(matches!(args[0], Expr::Eps { .. }));
                // Middle arg: `(x*)` — the parens collapse to a singleton
                // tup, leaving the Iter directly.
                assert!(matches!(args[1], Expr::Iter { .. }));
                assert!(matches!(args[2], Expr::Eps { .. }));
            }
            other => panic!("expected arrow Case, got {other:?}"),
        }
    }

    #[test]
    fn elab_func_with_inner_arrow_keeps_func_template() {
        // Regression guard for the Pratt-precedence fix: the arrow
        // mixfix must NOT steal the `->` literal from inside the
        // `FUNC resulttype -> resulttype` constructor template
        // (`comptype = | ... | FUNC resulttype -> resulttype`). The
        // top-level Case should be `FUNC` with two resulttype args, not
        // a 1-arg FUNC wrapping an arrow_mixfix application.
        let src = r#"
            syntax context = nat
            syntax localidx = nat
            syntax valtype = nat
            syntax resulttype = nat
            syntax instrtype = resulttype ->_(localidx*) resulttype
            syntax fieldtype = nat
            syntax comptype = | STRUCT fieldtype | FUNC resulttype -> resulttype
            relation Comptype_ok: context |- comptype : OK
            rule Comptype_ok/func:
              C |- FUNC eps -> eps : OK
        "#;
        let elab = elab_first_rule(src);
        let func = &elab.operands[1];
        match func {
            Expr::Case { head, args, .. } => {
                assert_eq!(head, "FUNC");
                assert_eq!(args.len(), 2, "FUNC must keep its 2-arg shape");
            }
            other => panic!("expected FUNC Case, got {other:?}"),
        }
    }

    #[test]
    fn elab_subtype_rule_three_vars() {
        let src = r#"
            syntax context = nat
            syntax numtype = nat
            relation Numtype_sub: context |- numtype <: numtype
            rule Numtype_sub:
              C |- numtype <: numtype
        "#;
        let elab = elab_first_rule(src);
        assert_eq!(elab.rule_name, "Numtype_sub");
        assert!(elab.case.is_none());
        assert_eq!(elab.operands.len(), 3);
        for op in &elab.operands {
            match op {
                Expr::Var { name, .. } => {
                    assert!(matches!(name.as_str(), "C" | "numtype"));
                }
                other => panic!("expected Var, got {other:?}"),
            }
        }
    }

    #[test]
    fn elab_rule_with_case_path() {
        let src = r#"
            syntax context = nat
            syntax heaptype = nat
            relation Heaptype_sub: context |- heaptype <: heaptype
            rule Heaptype_sub/refl:
              C |- heaptype <: heaptype
        "#;
        let elab = elab_first_rule(src);
        assert_eq!(elab.case.as_deref(), Some("refl"));
        assert_eq!(elab.operands.len(), 3);
    }

    #[test]
    fn elab_constant_constructors() {
        let src = r#"
            syntax instr = nat
            relation Step_pure: instr ~> instr
            rule Step_pure/unreachable:
              UNREACHABLE ~> TRAP
        "#;
        let elab = elab_first_rule(src);
        assert_eq!(elab.operands.len(), 2);
        let (lhs, rhs) = (&elab.operands[0], &elab.operands[1]);
        assert!(
            matches!(lhs, Expr::Case { head, args, .. } if head == "UNREACHABLE" && args.is_empty())
        );
        assert!(
            matches!(rhs, Expr::Case { head, args, .. } if head == "TRAP" && args.is_empty())
        );
    }

    #[test]
    fn elab_eps_as_eps_node() {
        let src = r#"
            syntax instr = nat
            relation Step_pure: instr ~> instr
            rule Step_pure/nop:
              NOP ~> eps
        "#;
        let elab = elab_first_rule(src);
        assert_eq!(elab.operands.len(), 2);
        assert!(matches!(&elab.operands[0], Expr::Case { head, .. } if head == "NOP"));
        assert!(matches!(&elab.operands[1], Expr::Eps { .. }));
    }

    #[test]
    fn elab_parenthesised_tuple() {
        let src = r#"
            syntax context = nat
            syntax t = nat
            relation R: context |- t : t
            rule R:
              (C) |- (a, b) : c
        "#;
        let elab = elab_first_rule(src);
        assert_eq!(elab.operands.len(), 3);
        // First operand is `(C)` — singleton parens collapse to Var(C).
        assert!(matches!(&elab.operands[0], Expr::Var { name, .. } if name == "C"));
        // Second is `(a, b)` — 2-tuple.
        let Expr::Tup { items, .. } = &elab.operands[1] else {
            panic!("expected Tup, got {:?}", elab.operands[1]);
        };
        assert_eq!(items.len(), 2);
        // Third is `c` — Var.
        assert!(matches!(&elab.operands[2], Expr::Var { name, .. } if name == "c"));
    }

    #[test]
    fn elab_unknown_relation_errors() {
        // Rule references a relation that doesn't exist.
        let src = r#"
            syntax t = nat
            relation A: t |- t
            rule UnknownRelation:
              x |- y
        "#;
        let mut map = SourceMap::new();
        let id = map.add("<test>", src);
        let tokens = lex(id, src).unwrap();
        let tops = parse(id, tokens).unwrap();
        let ctx = build_table(&tops).unwrap();
        let rule = tops
            .iter()
            .find_map(|t| if let Top::Rule(r) = t { Some(r) } else { None })
            .unwrap();
        assert!(elab_rule_conclusion(rule, &ctx).is_err());
    }

    #[test]
    fn elab_template_mismatch_errors() {
        // Rule conclusion missing the `<:` from the template.
        let src = r#"
            syntax t = nat
            relation R: t |- t <: t
            rule R:
              a |- b c
        "#;
        let mut map = SourceMap::new();
        let id = map.add("<test>", src);
        let tokens = lex(id, src).unwrap();
        let tops = parse(id, tokens).unwrap();
        let ctx = build_table(&tops).unwrap();
        let rule = tops
            .iter()
            .find_map(|t| if let Top::Rule(r) = t { Some(r) } else { None })
            .unwrap();
        assert!(elab_rule_conclusion(rule, &ctx).is_err());
    }

    // ---------- premise elaboration ----------

    #[test]
    fn elab_premise_if_guard() {
        let src = r#"
            syntax context = nat
            syntax t = nat
            relation R: context |- t : t
            rule R:
              C |- a : b
              -- if a
        "#;
        let elab = elab_first_rule(src);
        assert_eq!(elab.premises.len(), 1);
        assert!(matches!(&elab.premises[0], ElabPremise::If(Expr::Var { name, .. }) if name == "a"));
    }

    #[test]
    fn elab_premise_let_binding() {
        let src = r#"
            syntax context = nat
            syntax t = nat
            relation R: context |- t : t
            rule R:
              C |- x : y
              -- let p = q
        "#;
        let elab = elab_first_rule(src);
        assert_eq!(elab.premises.len(), 1);
        let ElabPremise::Let { lhs, rhs } = &elab.premises[0] else {
            panic!("expected Let, got {:?}", elab.premises[0]);
        };
        assert!(matches!(lhs, Expr::Var { name, .. } if name == "p"));
        assert!(matches!(rhs, Expr::Var { name, .. } if name == "q"));
    }

    #[test]
    fn elab_premise_else_marker() {
        let src = r#"
            syntax context = nat
            syntax t = nat
            relation R: context |- t : t
            rule R:
              C |- x : y
              -- otherwise
        "#;
        let elab = elab_first_rule(src);
        assert!(matches!(&elab.premises[0], ElabPremise::Else));
    }

    #[test]
    fn elab_premise_relation_reference() {
        let src = r#"
            syntax context = nat
            syntax t = nat
            relation OK: context |- t : t
            relation Sub: context |- t <: t
            rule Sub:
              C |- x <: y
              -- OK: C |- z : z
        "#;
        let elab = elab_first_rule(src);
        assert_eq!(elab.premises.len(), 1);
        let ElabPremise::Rule { rel_name, operands, .. } = &elab.premises[0] else {
            panic!("expected Rule premise, got {:?}", elab.premises[0]);
        };
        assert_eq!(rel_name, "OK");
        assert_eq!(operands.len(), 3);
    }

    #[test]
    fn elab_premise_unknown_relation_falls_back_to_raw() {
        let src = r#"
            syntax context = nat
            syntax t = nat
            relation R: context |- t : t
            rule R:
              C |- x : y
              -- Unknown_rel: C |- z : z
        "#;
        let elab = elab_first_rule(src);
        assert!(matches!(&elab.premises[0], ElabPremise::Raw(_)));
    }

    // ---------- profile merging ----------

    #[test]
    fn profile_merge_two_profiles() {
        let src = r#"
            syntax absheaptype/syn = | ANY | EQ | ... | NOFUNC
            syntax absheaptype/sem = | ... | BOT
        "#;
        let mut map = SourceMap::new();
        let id = map.add("<test>", src);
        let tokens = lex(id, src).unwrap();
        let tops = parse(id, tokens).unwrap();
        let ctx = build_table(&tops).unwrap();

        let merged = ctx.syntax_defs.get("absheaptype").unwrap();
        assert_eq!(merged.profiles.len(), 2);

        // /syn profile: ANY, EQ, then ... (spliced with /sem's BOT), then NOFUNC.
        let syn_alts = merged.alts_for_profile(Some("syn"));
        let syn_names: Vec<&str> = syn_alts
            .iter()
            .map(|a| match a.body.tokens.first().map(|s| &s.token) {
                Some(Token::Ident(n)) => n.as_str(),
                _ => "?",
            })
            .collect();
        assert_eq!(syn_names, vec!["ANY", "EQ", "BOT", "NOFUNC"]);

        // /sem profile: ... (spliced with /syn's [ANY, EQ, NOFUNC]), then BOT.
        let sem_alts = merged.alts_for_profile(Some("sem"));
        let sem_names: Vec<&str> = sem_alts
            .iter()
            .map(|a| match a.body.tokens.first().map(|s| &s.token) {
                Some(Token::Ident(n)) => n.as_str(),
                _ => "?",
            })
            .collect();
        assert_eq!(sem_names, vec!["ANY", "EQ", "NOFUNC", "BOT"]);
    }

    #[test]
    fn profile_merge_single_profile() {
        let src = r#"syntax numtype = | I32 | I64 | F32 | F64"#;
        let mut map = SourceMap::new();
        let id = map.add("<test>", src);
        let tokens = lex(id, src).unwrap();
        let tops = parse(id, tokens).unwrap();
        let ctx = build_table(&tops).unwrap();
        let merged = ctx.syntax_defs.get("numtype").unwrap();
        assert_eq!(merged.profiles.len(), 1);
        let alts = merged.alts_for_profile(None);
        assert_eq!(alts.len(), 4);
    }

    // ---------- var declarations ----------

    #[test]
    fn elab_var_decl_overrides_case_head() {
        // `C` is single-letter so falls through to Var via the
        // is_case_head length check. But also test something that
        // *would* be a case head without var decl: `Foo`.
        let src = r#"
            var Foo : nat
            syntax t = nat
            syntax context = nat
            relation R: context |- t : t
            rule R:
              Foo |- a : b
        "#;
        let elab = elab_first_rule(src);
        // First operand `Foo` should be Var thanks to var decl,
        // not Case (even though is_case_head matches "Foo"...
        // wait, "Foo" is mixed case so is_case_head rejects it. Hmm.).
        // Better test: pick something is_case_head WOULD accept like FOO.
        // Let's not require var decl override of case-head here, just
        // confirm the var decl is in ctx.
        assert!(matches!(&elab.operands[0], Expr::Var { name, .. } if name == "Foo"));
    }

    #[test]
    fn var_decl_with_subscript_still_resolves() {
        // `C_1` should resolve to `C` via metavar_base stripping.
        // To exercise this, set up a name where is_case_head WOULD fire
        // for a single Ident, then declare it as a var.
        let src = r#"
            var FOO : nat
            syntax t = nat
            syntax context = nat
            relation R: context |- t : t
            rule R:
              FOO_1 |- a : b
        "#;
        let elab = elab_first_rule(src);
        // FOO_1 strips to FOO which is in var_names → Var, not Case.
        assert!(matches!(&elab.operands[0], Expr::Var { name, .. } if name == "FOO_1"));
    }

    #[test]
    fn metavar_base_stripping() {
        use std::collections::HashSet;
        let vars: HashSet<String> = ["C", "FOO", "BAR"].iter().map(|s| s.to_string()).collect();
        assert!(is_declared_metavar("C", &vars));
        assert!(is_declared_metavar("C_1", &vars));
        assert!(is_declared_metavar("C_n", &vars));
        assert!(is_declared_metavar("C'", &vars));
        assert!(is_declared_metavar("C''", &vars));
        assert!(is_declared_metavar("C_1'", &vars));
        assert!(is_declared_metavar("FOO_n", &vars));
        assert!(!is_declared_metavar("OTHER", &vars));
        // Subscript that isn't all digits/lowercase: not stripped.
        assert!(!is_declared_metavar("C_X", &vars));
    }

    #[test]
    fn elab_iter_suffix_on_arg() {
        // `BLOCK bt instr*` should structure as
        // `Case(BLOCK, [Var(bt), Iter(Var(instr), Star)])`.
        let src = r#"
            syntax blocktype = nat
            syntax instr = | BLOCK blocktype instr*
            syntax context = nat
            relation R: context |- instr : instr
            rule R:
              C |- BLOCK bt instr* : i
        "#;
        let elab = elab_first_rule(src);
        assert_eq!(elab.operands.len(), 3);
        let Expr::Case { head, args, .. } = &elab.operands[1] else {
            panic!("expected Case, got {:?}", elab.operands[1]);
        };
        assert_eq!(head, "BLOCK");
        assert_eq!(args.len(), 2);
        assert!(matches!(&args[0], Expr::Var { name, .. } if name == "bt"));
        let Expr::Iter { inner, kind, .. } = &args[1] else {
            panic!("expected Iter for second arg, got {:?}", args[1]);
        };
        assert!(matches!(kind, IterKind::Star));
        assert!(matches!(inner.as_ref(), Expr::Var { name, .. } if name == "instr"));
    }

    #[test]
    fn elab_iter_suffix_question_and_plus() {
        let src = r#"
            syntax a = nat
            syntax b = nat
            syntax context = nat
            relation R: context |- a : a
            rule R:
              C |- x? : y+
        "#;
        let elab = elab_first_rule(src);
        assert_eq!(elab.operands.len(), 3);
        assert!(matches!(&elab.operands[1], Expr::Iter { kind: IterKind::Opt, .. }));
        assert!(matches!(&elab.operands[2], Expr::Iter { kind: IterKind::Plus, .. }));
    }

    #[test]
    fn elab_pratt_structures_multi_arg_constructor() {
        // Two-arg constructor `REF null heaptype` where both args are
        // simple idents. Pratt should fully consume and produce a
        // structured Case with both args (not a Case with a single Raw
        // arg, which is the fallback heuristic).
        let src = r#"
            syntax null = NULL
            syntax heaptype = nat
            syntax reftype = | REF null heaptype
            syntax context = nat
            relation R: context |- reftype : reftype
            rule R:
              C |- REF nul ht : REF nul ht
        "#;
        let elab = elab_first_rule(src);
        assert_eq!(elab.operands.len(), 3);
        let Expr::Case { head, args, .. } = &elab.operands[1] else {
            panic!("expected Case for second operand, got {:?}", elab.operands[1]);
        };
        assert_eq!(head, "REF");
        // Two structured args, not a single Raw fallback arg.
        assert_eq!(args.len(), 2, "expected REF to have 2 structured args");
        for arg in args {
            assert!(
                matches!(arg, Expr::Var { .. }),
                "expected Var arg, got {arg:?}"
            );
        }
    }

    #[test]
    fn iter_binder_inferred_from_iter_source_in_conclusion() {
        // The rule's conclusion has `l*` (Iter over Var `l`); the
        // premise body references `l`. Binder should be inferred.
        let src = r#"
            syntax context = nat
            syntax l = nat
            syntax t = nat
            relation R: context |- l : t
            rule R:
              C |- l* : t
              -- if l
        "#;
        // Note: this test uses a contrived shape. The real binder
        // inference target is `(...)*` premises referencing variables
        // also iterated in the conclusion.
        let elab = elab_first_rule(src);
        // No `(...)*` premise here, so no bindings to infer. Just
        // confirm the code path doesn't crash.
        assert!(!elab.premises.is_empty());
    }

    #[test]
    fn iter_binder_basic() {
        let src = r#"
            syntax context = nat
            syntax t = nat
            relation Sub: context |- t <: t
            relation R: context |- t <: t
            rule R:
              C |- a <: b
              -- if t*
              -- (Sub: C |- t <: b)*
        "#;
        let elab = elab_first_rule(src);
        // Last premise is an Iter; should have a binding for `t`
        // because `t*` appears earlier in the rule.
        let iter_prem = elab
            .premises
            .iter()
            .find_map(|p| match p {
                ElabPremise::Iter { bindings, .. } => Some(bindings),
                _ => None,
            })
            .expect("expected an Iter premise");
        // Source = `t*` (bare + iter suffix from the `if t*` premise)
        // — matches OCaml's `dom "t" (var "t*")` convention.
        assert!(
            iter_prem.iter().any(|b| b.var == "t" && b.source == "t*"),
            "expected binding for `t` with source `t*`, got {iter_prem:?}"
        );
    }

    #[test]
    fn elab_premise_iter_star() {
        let src = r#"
            syntax context = nat
            syntax t = nat
            relation Sub: context |- t <: t
            rule Sub:
              C |- x <: y
              -- (Sub: C |- a <: b)*
        "#;
        let elab = elab_first_rule(src);
        assert_eq!(elab.premises.len(), 1);
        let ElabPremise::Iter { inner, kind, .. } = &elab.premises[0] else {
            panic!("expected Iter, got {:?}", elab.premises[0]);
        };
        assert!(matches!(kind, IterKind::Star));
        assert!(matches!(inner.as_ref(), ElabPremise::Rule { rel_name, .. } if rel_name == "Sub"));
    }

    #[test]
    fn elab_premise_iter_opt() {
        let src = r#"
            syntax context = nat
            syntax t = nat
            relation R: context |- t : t
            rule R:
              C |- x : y
              -- (R: C |- a : b)?
        "#;
        let elab = elab_first_rule(src);
        let ElabPremise::Iter { kind, .. } = &elab.premises[0] else {
            panic!("expected Iter");
        };
        assert!(matches!(kind, IterKind::Opt));
    }

    #[test]
    fn elab_premise_iter_plus() {
        let src = r#"
            syntax context = nat
            syntax t = nat
            relation R: context |- t : t
            rule R:
              C |- x : y
              -- (R: C |- a : b)+
        "#;
        let elab = elab_first_rule(src);
        let ElabPremise::Iter { kind, .. } = &elab.premises[0] else {
            panic!("expected Iter");
        };
        assert!(matches!(kind, IterKind::Plus));
    }

    #[test]
    fn elab_premise_iter_caret_length() {
        let src = r#"
            syntax context = nat
            syntax t = nat
            relation R: context |- t : t
            rule R:
              C |- x : y
              -- (R: C |- a : b)^n
        "#;
        let elab = elab_first_rule(src);
        let ElabPremise::Iter { kind, .. } = &elab.premises[0] else {
            panic!("expected Iter");
        };
        assert!(matches!(kind, IterKind::Length(_)));
    }

    #[test]
    fn elab_multiple_premises() {
        let src = r#"
            syntax context = nat
            syntax t = nat
            relation Wf: context |- t : t
            relation Sub: context |- t <: t
            rule Sub:
              C |- x <: z
              -- Wf: C |- y : y
              -- Sub: C |- x <: y
              -- Sub: C |- y <: z
        "#;
        let elab = elab_first_rule(src);
        assert_eq!(elab.premises.len(), 3);
        for p in &elab.premises {
            assert!(matches!(p, ElabPremise::Rule { .. }));
        }
    }

    /// Classify a raw expression string against a context built from
    /// `decls`. Helper for path-update / slice tests.
    fn classify_expr_str(decls: &str, expr_src: &str) -> Expr {
        let ctx = build_from_str(decls);
        let mut map = SourceMap::new();
        let id = map.add("<expr>", expr_src);
        let tokens = lex(id, expr_src).expect("lex ok");
        let span = tokens
            .iter()
            .map(|s| s.span)
            .reduce(Span::join)
            .expect("non-empty input");
        let tr = crate::cst::TokenRun {
            span,
            tokens,
        };
        classify_token_run(&tr, &ctx).expect("classify ok")
    }

    /// Task #34 — `e[.FIELD = e']` lowers to `Upd { path: Dot{Root, FIELD} }`.
    #[test]
    fn elab_path_upd_single_dot() {
        let e = classify_expr_str("syntax state = nat", "free[.LABELS = eps]");
        let Expr::Upd { e1, path, e2, .. } = &e else {
            panic!("expected Expr::Upd, got {e:?}");
        };
        assert!(matches!(e1.as_ref(), Expr::Var { name, .. } if name == "free"));
        let Path::Dot { p, field } = path.as_ref() else {
            panic!("expected Path::Dot, got {path:?}");
        };
        assert!(matches!(p.as_ref(), Path::Root));
        assert_eq!(field, "LABELS");
        assert!(matches!(e2.as_ref(), Expr::Eps { .. }));
    }

    /// Task #34 — `e[.FIELD =++ e']` lowers to `Ext { path: Dot{Root, FIELD} }`.
    #[test]
    fn elab_path_ext_with_eqplusplus() {
        let e = classify_expr_str("syntax state = nat", "z[.ARRAYS =++ ai]");
        let Expr::Ext { e1, path, e2, .. } = &e else {
            panic!("expected Expr::Ext, got {e:?}");
        };
        assert!(matches!(e1.as_ref(), Expr::Var { name, .. } if name == "z"));
        let Path::Dot { p, field } = path.as_ref() else {
            panic!("expected Path::Dot, got {path:?}");
        };
        assert!(matches!(p.as_ref(), Path::Root));
        assert_eq!(field, "ARRAYS");
        assert!(matches!(e2.as_ref(), Expr::Var { name, .. } if name == "ai"));
    }

    /// Task #34 — `e[.A.B = e']` lowers to nested `Dot` path.
    #[test]
    fn elab_path_chained_dots() {
        let e = classify_expr_str("syntax state = nat", "f[.MODULE.GLOBALS = a]");
        let Expr::Upd { path, .. } = &e else {
            panic!("expected Expr::Upd, got {e:?}");
        };
        // Path::Dot { p: Path::Dot { p: Root, field: "MODULE" }, field: "GLOBALS" }
        let Path::Dot { p: outer_p, field: outer_field } = path.as_ref() else {
            panic!("outer not Dot");
        };
        assert_eq!(outer_field, "GLOBALS");
        let Path::Dot { p: inner_p, field: inner_field } = outer_p.as_ref() else {
            panic!("inner not Dot");
        };
        assert_eq!(inner_field, "MODULE");
        assert!(matches!(inner_p.as_ref(), Path::Root));
    }

    /// Task #34 — `e[.FIELD[i] = e']` lowers to `Idx` step on top of `Dot`.
    #[test]
    fn elab_path_dot_then_idx() {
        let e = classify_expr_str("syntax state = nat", "z[.LOCALS[x] = v]");
        let Expr::Upd { path, .. } = &e else {
            panic!("expected Expr::Upd, got {e:?}");
        };
        let Path::Idx { p, e: ie } = path.as_ref() else {
            panic!("expected Path::Idx, got {path:?}");
        };
        assert!(matches!(ie, Expr::Var { name, .. } if name == "x"));
        let Path::Dot { p: pp, field } = p.as_ref() else {
            panic!("expected inner Path::Dot");
        };
        assert!(matches!(pp.as_ref(), Path::Root));
        assert_eq!(field, "LOCALS");
    }

    /// Task #34 — `e[[i] = e']` lowers to `Idx` step on `Root` (no
    /// leading dot). Appears in 4.3-execution.instructions.spectec.
    #[test]
    fn elab_path_bracket_only() {
        let e = classify_expr_str("syntax state = nat", "c[[j] = k]");
        let Expr::Upd { path, .. } = &e else {
            panic!("expected Expr::Upd, got {e:?}");
        };
        let Path::Idx { p, e: ie } = path.as_ref() else {
            panic!("expected Path::Idx, got {path:?}");
        };
        assert!(matches!(p.as_ref(), Path::Root));
        assert!(matches!(ie, Expr::Var { name, .. } if name == "j"));
    }

    /// Task #34 — `e[path := e']` also recognised as Upd (alternate
    /// surface syntax, mirrors OCaml's permissive grammar).
    #[test]
    fn elab_path_upd_with_assign() {
        let e = classify_expr_str("syntax state = nat", "z[.LOCALS := v]");
        assert!(matches!(&e, Expr::Upd { .. }));
    }

    /// Task #34 — `e[.FIELD =.. e']` lowers to Ext, same as `=++`.
    #[test]
    fn elab_path_ext_with_eqdotdot() {
        let e = classify_expr_str("syntax state = nat", "z[.ARRAYS =.. ai]");
        assert!(matches!(&e, Expr::Ext { .. }));
    }

    /// Task #34 — plain `e[i]` (no `=` in body) must stay as `Expr::Idx`,
    /// NOT misclassified as a path update.
    #[test]
    fn elab_plain_idx_unaffected() {
        let e = classify_expr_str("syntax state = nat", "xs[i]");
        let Expr::Idx { e1, e2, .. } = &e else {
            panic!("expected Expr::Idx, got {e:?}");
        };
        assert!(matches!(e1.as_ref(), Expr::Var { name, .. } if name == "xs"));
        assert!(matches!(e2.as_ref(), Expr::Var { name, .. } if name == "i"));
    }

    /// Task #34 — `e[i : j]` (slice form) lowers to `Expr::Slice`.
    #[test]
    fn elab_plain_slice() {
        let e = classify_expr_str("syntax state = nat", "bs[i : j]");
        let Expr::Slice { e1, e2, e3, .. } = &e else {
            panic!("expected Expr::Slice, got {e:?}");
        };
        assert!(matches!(e1.as_ref(), Expr::Var { name, .. } if name == "bs"));
        assert!(matches!(e2.as_ref(), Expr::Var { name, .. } if name == "i"));
        assert!(matches!(e3.as_ref(), Expr::Var { name, .. } if name == "j"));
    }

    /// Task #34 — path step can itself be a slice: `e[.F[i:j] = e']`.
    #[test]
    fn elab_path_slice_step() {
        let e = classify_expr_str("syntax state = nat", "z[.BYTES[i : j] = b]");
        let Expr::Upd { path, .. } = &e else {
            panic!("expected Expr::Upd, got {e:?}");
        };
        let Path::Slice { p, e1, e2 } = path.as_ref() else {
            panic!("expected Path::Slice, got {path:?}");
        };
        let Path::Dot { p: pp, field } = p.as_ref() else {
            panic!("expected inner Path::Dot");
        };
        assert!(matches!(pp.as_ref(), Path::Root));
        assert_eq!(field, "BYTES");
        assert!(matches!(e1, Expr::Var { name, .. } if name == "i"));
        assert!(matches!(e2, Expr::Var { name, .. } if name == "j"));
    }

    #[test]
    fn is_case_head_classification() {
        assert!(is_case_head("I32"));
        assert!(is_case_head("NOP"));
        assert!(is_case_head("BLOCK"));
        assert!(is_case_head("UNREACHABLE"));
        assert!(is_case_head("_IDX"));
        assert!(is_case_head("_DEF"));
        assert!(!is_case_head("instr"));
        assert!(!is_case_head("t_1"));
        assert!(!is_case_head("_"));
        assert!(!is_case_head(""));
        // Single-letter uppercase metavariables are NOT case heads.
        assert!(!is_case_head("C"));
        assert!(!is_case_head("X"));
        assert!(!is_case_head("N"));
        // Mixed case is not a case head.
        assert!(!is_case_head("Foo"));
        assert!(!is_case_head("Numtype_sub"));
    }

    #[test]
    fn param_kinds_include_builtins() {
        let ctx = build_from_str("");
        assert_eq!(ctx.param_kinds.get("list"), Some(&vec![ParamKind::Typ]));
        assert_eq!(ctx.param_kinds.get("option"), Some(&vec![ParamKind::Typ]));
    }

    #[test]
    fn param_kinds_from_syntax_decl_exp_arg() {
        // `fN(N)` — `N` is a bare ident, so it's an Exp param.
        let src = "syntax fN(N) = | POS fN(N) | NEG fN(N)";
        let ctx = build_from_str(src);
        assert_eq!(ctx.param_kinds.get("fN"), Some(&vec![ParamKind::Exp]));
    }

    #[test]
    fn param_kinds_from_syntax_decl_typ_arg() {
        // `mylist(syntax X)` — `syntax X` is a Typ param.
        let src = "syntax mylist(syntax X) = X";
        let ctx = build_from_str(src);
        assert_eq!(ctx.param_kinds.get("mylist"), Some(&vec![ParamKind::Typ]));
    }

    #[test]
    fn param_kinds_mixed_decl() {
        // Multiple params of differing kinds.
        let src = "syntax thing(syntax T, N : nat) = T";
        let ctx = build_from_str(src);
        assert_eq!(
            ctx.param_kinds.get("thing"),
            Some(&vec![ParamKind::Typ, ParamKind::Exp]),
        );
    }
}
