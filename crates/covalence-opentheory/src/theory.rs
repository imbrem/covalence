//! Parser for OpenTheory `.thy` theory files.
//!
//! A theory file declares a package's metadata (name, version, etc.),
//! its dependencies (`requires:`), and a `main` block that references
//! an article file.

use crate::error::OtError;

/// Parsed representation of an OpenTheory `.thy` file.
#[derive(Debug, Clone)]
pub struct TheoryFile {
    pub name: String,
    pub version: String,
    pub description: String,
    pub requires: Vec<String>,
    /// `show` directives mapping display prefixes.
    pub show: Vec<String>,
    /// The article path from the `main` block.
    pub article: String,
}

/// Parse a `.thy` file from its text content.
pub fn parse_theory_file(input: &str) -> Result<TheoryFile, OtError> {
    let mut name = String::new();
    let mut version = String::new();
    let mut description = String::new();
    let mut requires = Vec::new();
    let mut show = Vec::new();
    let mut article = String::new();
    let mut in_main_block = false;

    for line in input.lines() {
        let line = line.trim();
        if line.is_empty() {
            continue;
        }

        if in_main_block {
            if line == "}" {
                in_main_block = false;
                continue;
            }
            if let Some(rest) = line.strip_prefix("article:") {
                let rest = rest.trim();
                // Strip surrounding quotes.
                article = rest.trim_matches('"').to_string();
            }
            // Skip other block directives (import, interpret, etc.) for now.
            continue;
        }

        if line == "main {" || line.starts_with("main {") {
            in_main_block = true;
            continue;
        }

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
        // Ignore: author, license, provenance, etc.
    }

    if article.is_empty() {
        return Err(OtError::ParseError(
            "theory file has no article in main block".into(),
        ));
    }

    Ok(TheoryFile {
        name,
        version,
        description,
        requires,
        show,
        article,
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
        assert_eq!(thy.article, "bool-def-true.art");
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
        assert_eq!(thy.article, "bool-def-and.art");
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
}
