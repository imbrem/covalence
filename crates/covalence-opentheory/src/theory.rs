//! Parser for OpenTheory `.thy` theory files.
//!
//! A theory file declares a package's metadata (name, version, etc.),
//! its dependencies (`requires:`), and one or more named blocks.
//!
//! Two formats are supported:
//!
//! **Simple (leaf) packages** — a single `main` block with an `article:`:
//! ```text
//! name: bool-def
//! version: 1.11
//! main {
//!   article: "bool-def.art"
//! }
//! ```
//!
//! **Umbrella packages** — multiple named blocks referencing sub-packages:
//! ```text
//! name: bool
//! version: 1.37
//! def {
//!   package: bool-def-1.11
//! }
//! int {
//!   import: def
//!   package: bool-int-1.18
//! }
//! main {
//!   import: def
//!   import: int
//! }
//! ```

use crate::error::OtError;

/// A named block within a `.thy` file.
#[derive(Debug, Clone)]
pub struct TheoryBlock {
    /// Block name (e.g. `"def"`, `"int"`, `"main"`).
    pub name: String,
    /// External package reference (e.g. `"bool-def-1.11"`).
    pub package: Option<String>,
    /// Local article file (e.g. `"bool-def.art"`).
    pub article: Option<String>,
    /// Block names imported within this `.thy` file.
    pub imports: Vec<String>,
    /// Interpretation file for renaming types/constants (e.g. `"word.int"`).
    pub interpretation: Option<String>,
}

/// Parsed representation of an OpenTheory `.thy` file.
#[derive(Debug, Clone)]
pub struct TheoryFile {
    pub name: String,
    pub version: String,
    pub description: String,
    /// Top-level `requires:` — external package dependencies.
    pub requires: Vec<String>,
    /// `show` directives mapping display prefixes.
    pub show: Vec<String>,
    /// Named blocks (includes `main`).
    pub blocks: Vec<TheoryBlock>,
}

impl TheoryFile {
    /// Get the article path from the `main` block, if any.
    pub fn main_article(&self) -> Option<&str> {
        self.blocks
            .iter()
            .find(|b| b.name == "main")
            .and_then(|b| b.article.as_deref())
    }

    /// True if this is a simple leaf package (main block has an article).
    pub fn is_leaf(&self) -> bool {
        self.main_article().is_some()
    }
}

/// Parse a `.thy` file from its text content.
pub fn parse_theory_file(input: &str) -> Result<TheoryFile, OtError> {
    let mut name = String::new();
    let mut version = String::new();
    let mut description = String::new();
    let mut requires = Vec::new();
    let mut show = Vec::new();
    let mut blocks: Vec<TheoryBlock> = Vec::new();

    // Current block being parsed (None = top level).
    let mut current_block: Option<TheoryBlock> = None;

    for line in input.lines() {
        let line = line.trim();
        if line.is_empty() {
            continue;
        }

        if let Some(ref mut block) = current_block {
            if line == "}" {
                blocks.push(current_block.take().unwrap());
                continue;
            }
            if let Some(rest) = line.strip_prefix("article:") {
                block.article = Some(rest.trim().trim_matches('"').to_string());
            } else if let Some(rest) = line.strip_prefix("import:") {
                block.imports.push(rest.trim().to_string());
            } else if let Some(rest) = line.strip_prefix("package:") {
                block.package = Some(rest.trim().to_string());
            } else if let Some(rest) = line.strip_prefix("interpretation:") {
                block.interpretation = Some(rest.trim().trim_matches('"').to_string());
            }
            // Skip: checksum, etc.
            continue;
        }

        // Top-level: check for block start.
        if let Some(block_name) = line.strip_suffix('{') {
            let block_name = block_name.trim();
            if !block_name.is_empty() {
                current_block = Some(TheoryBlock {
                    name: block_name.to_string(),
                    package: None,
                    article: None,
                    imports: Vec::new(),
                    interpretation: None,
                });
                continue;
            }
        }

        // Top-level key-value pairs.
        if let Some(rest) = line.strip_prefix("name:") {
            name = rest.trim().to_string();
        } else if let Some(rest) = line.strip_prefix("version:") {
            version = rest.trim().to_string();
        } else if let Some(rest) = line.strip_prefix("description:") {
            description = rest.trim().to_string();
        } else if let Some(rest) = line.strip_prefix("requires:") {
            requires.push(rest.trim().to_string());
        } else if let Some(rest) = line.strip_prefix("show:") {
            show.push(rest.trim().trim_matches('"').to_string());
        }
        // Ignore: author, license, provenance, homepage, haskell-*, etc.
    }

    // Validate: must have at least a main block.
    if !blocks.iter().any(|b| b.name == "main") {
        return Err(OtError::ParseError("theory file has no main block".into()));
    }

    // Validate: main block must have either an article or imports.
    let main_block = blocks.iter().find(|b| b.name == "main").unwrap();
    if main_block.article.is_none() && main_block.imports.is_empty() && main_block.package.is_none()
    {
        return Err(OtError::ParseError(
            "main block has no article, imports, or package".into(),
        ));
    }

    Ok(TheoryFile {
        name,
        version,
        description,
        requires,
        show,
        blocks,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_simple_thy() {
        let input = "\
name: bool-def-true
version: 1.0
description: bool-def-true
author: Joe Hurd <joe@gilith.com>
license: HOLLight
provenance: HOL Light theory extracted on 2011-02-19
show: \"Data.Bool\"

main {
  article: \"bool-def-true.art\"
}
";
        let thy = parse_theory_file(input).unwrap();
        assert_eq!(thy.name, "bool-def-true");
        assert_eq!(thy.version, "1.0");
        assert!(thy.is_leaf());
        assert_eq!(thy.main_article().unwrap(), "bool-def-true.art");
        assert!(thy.requires.is_empty());
    }

    #[test]
    fn test_parse_thy_with_requires() {
        let input = "\
name: bool-def-and
version: 1.0
description: bool-def-and
requires: bool-def-true

main {
  article: \"bool-def-and.art\"
}
";
        let thy = parse_theory_file(input).unwrap();
        assert_eq!(thy.name, "bool-def-and");
        assert_eq!(thy.requires, vec!["bool-def-true"]);
        assert_eq!(thy.main_article().unwrap(), "bool-def-and.art");
    }

    #[test]
    fn test_parse_thy_multiple_requires() {
        let input = "\
name: unit-def
version: 1.0
requires: bool-def-true
requires: bool-def-and

main {
  article: \"unit-def.art\"
}
";
        let thy = parse_theory_file(input).unwrap();
        assert_eq!(thy.requires, vec!["bool-def-true", "bool-def-and"]);
    }

    #[test]
    fn test_parse_umbrella_thy() {
        let input = "\
name: bool
version: 1.37
description: Boolean operators and quantifiers
show: \"Data.Bool\"

def {
  package: bool-def-1.11
  checksum: 0a4ed62119c317adca068ae0550c03a7c636698c
}

int {
  import: def
  package: bool-int-1.18
}

main {
  import: def
  import: int
}
";
        let thy = parse_theory_file(input).unwrap();
        assert_eq!(thy.name, "bool");
        assert_eq!(thy.version, "1.37");
        assert!(!thy.is_leaf());
        assert!(thy.main_article().is_none());
        assert_eq!(thy.blocks.len(), 3);

        let def = &thy.blocks[0];
        assert_eq!(def.name, "def");
        assert_eq!(def.package.as_deref(), Some("bool-def-1.11"));
        assert!(def.imports.is_empty());

        let int = &thy.blocks[1];
        assert_eq!(int.name, "int");
        assert_eq!(int.package.as_deref(), Some("bool-int-1.18"));
        assert_eq!(int.imports, vec!["def"]);

        let main = &thy.blocks[2];
        assert_eq!(main.name, "main");
        assert!(main.package.is_none());
        assert_eq!(main.imports, vec!["def", "int"]);
    }

    #[test]
    fn test_parse_mixed_thy() {
        let input = "\
name: byte-def
version: 1.100
requires: base

def {
  article: \"byte-def.art\"
}

word {
  import: def
  interpretation: \"word.int\"
  package: word-1.121
}

main {
  import: def
  import: word
}
";
        let thy = parse_theory_file(input).unwrap();
        assert_eq!(thy.name, "byte-def");
        assert!(!thy.is_leaf());
        assert_eq!(thy.requires, vec!["base"]);

        let def = &thy.blocks[0];
        assert_eq!(def.article.as_deref(), Some("byte-def.art"));
        assert!(def.package.is_none());

        let word = &thy.blocks[1];
        assert_eq!(word.package.as_deref(), Some("word-1.121"));
        assert_eq!(word.interpretation.as_deref(), Some("word.int"));
        assert_eq!(word.imports, vec!["def"]);
    }
}
