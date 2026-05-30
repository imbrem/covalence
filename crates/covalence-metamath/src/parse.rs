use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};

use crate::database::{Database, Proof, Statement, SymbolId};
use crate::error::MmError;

// ---------------------------------------------------------------------------
// Source resolver trait and implementations
// ---------------------------------------------------------------------------

/// Resolve and read Metamath source files for `$[ filename $]` inclusion.
pub trait SourceResolver {
    /// Resolve and read a source file.
    /// `filename` — the token between `$[` and `$]`.
    /// `referrer` — canonical path of the file containing the directive (None for root).
    /// Returns `(canonical_key, contents)`. The key is used for deduplication.
    fn resolve(
        &self,
        filename: &str,
        referrer: Option<&str>,
    ) -> Result<(String, String), std::io::Error>;
}

/// Resolves files from the filesystem, relative to the referrer's directory.
pub struct FileResolver {
    base_dir: PathBuf,
}

impl FileResolver {
    pub fn new(base_dir: impl Into<PathBuf>) -> Self {
        Self {
            base_dir: base_dir.into(),
        }
    }
}

impl SourceResolver for FileResolver {
    fn resolve(
        &self,
        filename: &str,
        referrer: Option<&str>,
    ) -> Result<(String, String), std::io::Error> {
        let dir = match referrer {
            Some(r) => Path::new(r)
                .parent()
                .unwrap_or(self.base_dir.as_path())
                .to_path_buf(),
            None => self.base_dir.clone(),
        };
        let path = dir.join(filename);
        let canonical = path
            .canonicalize()
            .map_err(|e| std::io::Error::new(e.kind(), format!("{}: {e}", path.display())))?;
        let key = canonical.to_string_lossy().into_owned();
        let contents = std::fs::read_to_string(&canonical)?;
        Ok((key, contents))
    }
}

/// In-memory resolver for testing. Looks up filenames in a map.
pub struct MemoryResolver {
    files: HashMap<String, String>,
}

impl MemoryResolver {
    pub fn new(files: HashMap<String, String>) -> Self {
        Self { files }
    }
}

impl SourceResolver for MemoryResolver {
    fn resolve(
        &self,
        filename: &str,
        _referrer: Option<&str>,
    ) -> Result<(String, String), std::io::Error> {
        let contents = self.files.get(filename).ok_or_else(|| {
            std::io::Error::new(
                std::io::ErrorKind::NotFound,
                format!("file not found: {filename}"),
            )
        })?;
        Ok((filename.to_owned(), contents.clone()))
    }
}

// ---------------------------------------------------------------------------
// Public parse API
// ---------------------------------------------------------------------------

/// Parse a Metamath `.mm` source string into a [`Database`].
pub fn parse(input: &str) -> Result<Database, MmError> {
    let tokens = tokenize(input);
    parse_tokens(tokens)
}

/// Parse a Metamath database starting from `filename`, resolving `$[ ... $]` includes.
pub fn parse_with_resolver(
    filename: &str,
    resolver: &dyn SourceResolver,
) -> Result<Database, MmError> {
    let (key, contents) = resolver
        .resolve(filename, None)
        .map_err(|e| MmError::FileError {
            path: filename.to_owned(),
            message: e.to_string(),
        })?;
    let mut seen = HashSet::new();
    seen.insert(key.clone());
    let tokens = tokenize_with_includes(&contents, resolver, Some(&key), &mut seen)?;
    parse_tokens(tokens)
}

// ---------------------------------------------------------------------------
// Internal: token-level include expansion
// ---------------------------------------------------------------------------

fn tokenize_with_includes(
    input: &str,
    resolver: &dyn SourceResolver,
    referrer: Option<&str>,
    seen: &mut HashSet<String>,
) -> Result<Vec<(String, usize)>, MmError> {
    let raw = tokenize(input);
    let mut out = Vec::with_capacity(raw.len());
    let mut it = raw.into_iter();

    while let Some((tok, span)) = it.next() {
        if tok == "$[" {
            let (filename, _) = it.next().ok_or_else(|| MmError::Parse {
                span,
                message: "expected filename after $[".into(),
            })?;
            let (close, close_span) = it.next().ok_or_else(|| MmError::Parse {
                span,
                message: "expected $] after filename".into(),
            })?;
            if close != "$]" {
                return Err(MmError::Parse {
                    span: close_span,
                    message: format!("expected $], got `{close}`"),
                });
            }

            let (key, contents) =
                resolver
                    .resolve(&filename, referrer)
                    .map_err(|e| MmError::FileError {
                        path: filename.clone(),
                        message: e.to_string(),
                    })?;

            if seen.insert(key.clone()) {
                let included = tokenize_with_includes(&contents, resolver, Some(&key), seen)?;
                out.extend(included);
            }
        } else {
            out.push((tok, span));
        }
    }

    Ok(out)
}

// ---------------------------------------------------------------------------
// Internal: parse a token stream into a Database
// ---------------------------------------------------------------------------

fn parse_tokens(tokens: Vec<(String, usize)>) -> Result<Database, MmError> {
    let mut db = Database::new();
    let mut it = tokens.into_iter().peekable();

    while let Some((tok, span)) = it.next() {
        match tok.as_str() {
            "$c" => parse_constants(&mut db, &mut it, span)?,
            "$v" => parse_variables(&mut db, &mut it, span)?,
            "$d" => parse_disjoint(&mut db, &mut it, span)?,
            "${" => db.push_scope(),
            "$}" => db.pop_scope(),
            _ => {
                // Must be a label — next token is the keyword.
                let label = tok;
                let (keyword, kw_span) = it.next().ok_or_else(|| MmError::Parse {
                    span,
                    message: format!("expected keyword after label `{label}`"),
                })?;
                match keyword.as_str() {
                    "$f" => parse_float(&mut db, &mut it, label, kw_span)?,
                    "$e" => parse_essential(&mut db, &mut it, label, kw_span)?,
                    "$a" => parse_axiom(&mut db, &mut it, label, kw_span)?,
                    "$p" => parse_provable(&mut db, &mut it, label, kw_span)?,
                    _ => {
                        return Err(MmError::Parse {
                            span: kw_span,
                            message: format!(
                                "unexpected keyword `{keyword}` after label `{label}`"
                            ),
                        });
                    }
                }
            }
        }
    }

    Ok(db)
}

// ---------------------------------------------------------------------------
// Tokenizer
// ---------------------------------------------------------------------------

/// Tokenize input, skipping `$( ... $)` comments. Returns (token, byte_offset) pairs.
fn tokenize(input: &str) -> Vec<(String, usize)> {
    let mut tokens = Vec::new();
    let mut chars = input.char_indices().peekable();

    loop {
        // Skip whitespace.
        while let Some(&(_, c)) = chars.peek() {
            if c.is_ascii_whitespace() {
                chars.next();
            } else {
                break;
            }
        }

        let Some(&(start, _)) = chars.peek() else {
            break;
        };

        // Collect non-whitespace.
        let mut end = start;
        while let Some(&(i, c)) = chars.peek() {
            if c.is_ascii_whitespace() {
                break;
            }
            end = i + c.len_utf8();
            chars.next();
        }

        let tok = &input[start..end];

        // Skip comments: $( ... $)
        if tok == "$(" {
            // Consume until $)
            loop {
                // Skip whitespace.
                while let Some(&(_, c)) = chars.peek() {
                    if c.is_ascii_whitespace() {
                        chars.next();
                    } else {
                        break;
                    }
                }
                let Some(&(cs, _)) = chars.peek() else {
                    break;
                };
                let mut ce = cs;
                while let Some(&(i, c)) = chars.peek() {
                    if c.is_ascii_whitespace() {
                        break;
                    }
                    ce = i + c.len_utf8();
                    chars.next();
                }
                if &input[cs..ce] == "$)" {
                    break;
                }
            }
            continue;
        }

        tokens.push((tok.to_owned(), start));
    }

    tokens
}

type TokenIter = std::iter::Peekable<std::vec::IntoIter<(String, usize)>>;

// ---------------------------------------------------------------------------
// Statement parsers
// ---------------------------------------------------------------------------

/// `$c sym1 sym2 ... $.`
fn parse_constants(db: &mut Database, it: &mut TokenIter, span: usize) -> Result<(), MmError> {
    let mut syms = Vec::new();
    loop {
        let (tok, _) = it.next().ok_or_else(|| MmError::Parse {
            span,
            message: "unterminated $c".into(),
        })?;
        if tok == "$." {
            break;
        }
        let id = db.intern_symbol(&tok, false);
        syms.push(id);
    }
    db.add_statement(Statement::Constant { symbols: syms });
    Ok(())
}

/// `$v var1 var2 ... $.`
fn parse_variables(db: &mut Database, it: &mut TokenIter, span: usize) -> Result<(), MmError> {
    let mut syms = Vec::new();
    loop {
        let (tok, _) = it.next().ok_or_else(|| MmError::Parse {
            span,
            message: "unterminated $v".into(),
        })?;
        if tok == "$." {
            break;
        }
        let id = db.intern_symbol(&tok, true);
        syms.push(id);
        db.current_scope_mut().variables.push(id);
    }
    db.add_statement(Statement::Variable { symbols: syms });
    Ok(())
}

/// `$d var1 var2 ... $.`
fn parse_disjoint(db: &mut Database, it: &mut TokenIter, span: usize) -> Result<(), MmError> {
    let mut vars = Vec::new();
    loop {
        let (tok, _) = it.next().ok_or_else(|| MmError::Parse {
            span,
            message: "unterminated $d".into(),
        })?;
        if tok == "$." {
            break;
        }
        let id = db.lookup_symbol(&tok).ok_or_else(|| MmError::Parse {
            span,
            message: format!("unknown symbol `{tok}` in $d"),
        })?;
        vars.push(id);
    }
    // Register all pairwise disjoint restrictions.
    for i in 0..vars.len() {
        for j in (i + 1)..vars.len() {
            db.current_scope_mut().disjoints.push((vars[i], vars[j]));
        }
    }
    db.add_statement(Statement::Disjoint { vars });
    Ok(())
}

/// `label $f typecode var $.`
fn parse_float(
    db: &mut Database,
    it: &mut TokenIter,
    label: String,
    span: usize,
) -> Result<(), MmError> {
    let (tc_tok, _) = it.next().ok_or_else(|| MmError::Parse {
        span,
        message: "unterminated $f".into(),
    })?;
    let (var_tok, _) = it.next().ok_or_else(|| MmError::Parse {
        span,
        message: "unterminated $f".into(),
    })?;
    let (dot, _) = it.next().ok_or_else(|| MmError::Parse {
        span,
        message: "unterminated $f".into(),
    })?;
    if dot != "$." {
        return Err(MmError::Parse {
            span,
            message: format!("expected $. in $f, got `{dot}`"),
        });
    }

    let typecode = db.lookup_symbol(&tc_tok).ok_or_else(|| MmError::Parse {
        span,
        message: format!("unknown typecode `{tc_tok}` in $f"),
    })?;
    let var = db.lookup_symbol(&var_tok).ok_or_else(|| MmError::Parse {
        span,
        message: format!("unknown variable `{var_tok}` in $f"),
    })?;

    let stmt = Statement::Float {
        label: label.clone(),
        typecode,
        var,
    };
    let id = db.add_statement(stmt);
    db.register_label(label.clone(), id)
        .map_err(|l| MmError::DuplicateLabel { label: l })?;
    db.current_scope_mut().floats.push((label, id));
    Ok(())
}

/// `label $e sym1 sym2 ... $.`
fn parse_essential(
    db: &mut Database,
    it: &mut TokenIter,
    label: String,
    span: usize,
) -> Result<(), MmError> {
    let symbols = read_symbol_string(db, it, span, "$e")?;
    let stmt = Statement::Essential {
        label: label.clone(),
        symbols,
    };
    let id = db.add_statement(stmt);
    db.register_label(label.clone(), id)
        .map_err(|l| MmError::DuplicateLabel { label: l })?;
    db.current_scope_mut().essentials.push((label, id));
    Ok(())
}

/// `label $a sym1 sym2 ... $.`
fn parse_axiom(
    db: &mut Database,
    it: &mut TokenIter,
    label: String,
    span: usize,
) -> Result<(), MmError> {
    let symbols = read_symbol_string(db, it, span, "$a")?;
    let frame = db.build_frame(&symbols);
    let stmt = Statement::Axiom {
        label: label.clone(),
        symbols,
        frame,
    };
    let id = db.add_statement(stmt);
    db.register_label(label, id)
        .map_err(|l| MmError::DuplicateLabel { label: l })?;
    Ok(())
}

/// `label $p sym1 sym2 ... $= label1 label2 ... $.`
fn parse_provable(
    db: &mut Database,
    it: &mut TokenIter,
    label: String,
    span: usize,
) -> Result<(), MmError> {
    // Read symbols until $=.
    let mut symbols = Vec::new();
    loop {
        let (tok, _) = it.next().ok_or_else(|| MmError::Parse {
            span,
            message: "unterminated $p".into(),
        })?;
        if tok == "$=" {
            break;
        }
        let id = db.lookup_symbol(&tok).ok_or_else(|| MmError::Parse {
            span,
            message: format!("unknown symbol `{tok}` in $p"),
        })?;
        symbols.push(id);
    }

    // Check for compressed proof: starts with `(`
    let proof = if it.peek().is_some_and(|(tok, _)| tok == "(") {
        it.next(); // consume `(`
        // Read label block until `)`
        let mut labels = Vec::new();
        loop {
            let (tok, _) = it.next().ok_or_else(|| MmError::Parse {
                span,
                message: "unterminated compressed proof label block".into(),
            })?;
            if tok == ")" {
                break;
            }
            labels.push(tok);
        }
        // Read letter block: concatenate all tokens until `$.`
        let mut letters = Vec::new();
        loop {
            let (tok, _) = it.next().ok_or_else(|| MmError::Parse {
                span,
                message: "unterminated compressed proof letter block".into(),
            })?;
            if tok == "$." {
                break;
            }
            letters.extend_from_slice(tok.as_bytes());
        }
        Proof::Compressed { labels, letters }
    } else {
        // Normal proof: read labels until `$.`
        let mut labels = Vec::new();
        loop {
            let (tok, _) = it.next().ok_or_else(|| MmError::Parse {
                span,
                message: "unterminated proof in $p".into(),
            })?;
            if tok == "$." {
                break;
            }
            labels.push(tok);
        }
        Proof::Normal(labels)
    };

    let frame = db.build_frame(&symbols);
    let stmt = Statement::Provable {
        label: label.clone(),
        symbols,
        frame,
        proof,
    };
    let id = db.add_statement(stmt);
    db.register_label(label, id)
        .map_err(|l| MmError::DuplicateLabel { label: l })?;
    Ok(())
}

/// Read symbols until `$.`, resolving each to a SymbolId.
fn read_symbol_string(
    db: &Database,
    it: &mut TokenIter,
    span: usize,
    ctx: &str,
) -> Result<Vec<SymbolId>, MmError> {
    let mut syms = Vec::new();
    loop {
        let (tok, _) = it.next().ok_or_else(|| MmError::Parse {
            span,
            message: format!("unterminated {ctx}"),
        })?;
        if tok == "$." {
            break;
        }
        let id = db.lookup_symbol(&tok).ok_or_else(|| MmError::Parse {
            span,
            message: format!("unknown symbol `{tok}` in {ctx}"),
        })?;
        syms.push(id);
    }
    Ok(syms)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tokenize_skips_comments() {
        let tokens = tokenize("a $( comment $) b");
        let words: Vec<&str> = tokens.iter().map(|(t, _)| t.as_str()).collect();
        assert_eq!(words, vec!["a", "b"]);
    }

    #[test]
    fn tokenize_handles_multiline() {
        let tokens = tokenize("  a\n  b\r\n  c  ");
        let words: Vec<&str> = tokens.iter().map(|(t, _)| t.as_str()).collect();
        assert_eq!(words, vec!["a", "b", "c"]);
    }

    #[test]
    fn parse_constants() {
        let db = parse("$c wff |- $.").unwrap();
        assert!(db.lookup_symbol("wff").is_some());
        assert!(db.lookup_symbol("|-").is_some());
        assert!(!db.is_variable(db.lookup_symbol("wff").unwrap()));
    }

    #[test]
    fn parse_variables() {
        let db = parse("$c wff $. $v ph ps $.").unwrap();
        let ph = db.lookup_symbol("ph").unwrap();
        assert!(db.is_variable(ph));
    }

    #[test]
    fn parse_float() {
        let db = parse("$c wff $. $v ph $. wph $f wff ph $.").unwrap();
        assert!(db.lookup_label("wph").is_some());
    }

    #[test]
    fn parse_duplicate_label_error() {
        let result = parse("$c wff $. $v ph $. wph $f wff ph $. wph $f wff ph $.");
        assert!(result.is_err());
    }

    #[test]
    fn parse_scopes() {
        // Variables in inner scope should still be usable for frame building.
        let input = "\
            $c wff $.\n\
            ${ $v ph $. wph $f wff ph $. $}\n\
        ";
        let db = parse(input).unwrap();
        assert!(db.lookup_label("wph").is_some());
    }

    // -----------------------------------------------------------------------
    // Include tests
    // -----------------------------------------------------------------------

    fn mem(files: &[(&str, &str)]) -> MemoryResolver {
        MemoryResolver::new(
            files
                .iter()
                .map(|(k, v)| (k.to_string(), v.to_string()))
                .collect(),
        )
    }

    #[test]
    fn include_two_files() {
        let resolver = mem(&[
            ("root.mm", "$[ defs.mm $] wph $f wff ph $."),
            ("defs.mm", "$c wff $. $v ph $."),
        ]);
        let db = parse_with_resolver("root.mm", &resolver).unwrap();
        assert!(db.lookup_symbol("wff").is_some());
        assert!(db.lookup_label("wph").is_some());
    }

    #[test]
    fn include_duplicate_skipped() {
        let resolver = mem(&[("root.mm", "$[ a.mm $] $[ a.mm $]"), ("a.mm", "$c wff $.")]);
        // If a.mm were included twice, the second $c wff would re-declare —
        // but it still works because $c is additive. The key thing is no error.
        let db = parse_with_resolver("root.mm", &resolver).unwrap();
        assert!(db.lookup_symbol("wff").is_some());
    }

    #[test]
    fn include_nested() {
        let resolver = mem(&[
            ("root.mm", "$[ a.mm $] wph $f wff ph $."),
            ("a.mm", "$[ b.mm $] $v ph $."),
            ("b.mm", "$c wff $."),
        ]);
        let db = parse_with_resolver("root.mm", &resolver).unwrap();
        assert!(db.lookup_symbol("wff").is_some());
        assert!(db.lookup_label("wph").is_some());
    }

    #[test]
    fn include_unknown_file_error() {
        let resolver = mem(&[("root.mm", "$[ missing.mm $]")]);
        let result = parse_with_resolver("root.mm", &resolver);
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(
            matches!(err, MmError::FileError { ref path, .. } if path == "missing.mm"),
            "expected FileError for missing.mm, got: {err}"
        );
    }
}
