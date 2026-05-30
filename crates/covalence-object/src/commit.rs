use crate::table::TableError;

// ---------------------------------------------------------------------------
// GitSignature
// ---------------------------------------------------------------------------

/// An author or committer identity line from a git commit.
///
/// Preserves the exact raw representation so that `parse → to_git_string`
/// round-trips without changing the commit hash.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GitSignature {
    /// Display name (e.g. `"Jane Doe"`).
    pub name: String,
    /// Email address (e.g. `"jane@example.com"`).
    pub email: String,
    /// Unix timestamp in seconds (signed to allow pre-epoch dates).
    pub seconds: i64,
    /// Timezone offset string (e.g. `"+0200"`, `"-0500"`).
    pub tz_offset: String,
}

impl GitSignature {
    /// Parse a git identity string of the form `Name <email> timestamp tz_offset`.
    pub fn parse(line: &str) -> Result<Self, TableError> {
        let lt = line
            .find('<')
            .ok_or_else(|| TableError::InvalidGitCommit("missing '<' in signature".into()))?;
        let gt = line
            .find('>')
            .ok_or_else(|| TableError::InvalidGitCommit("missing '>' in signature".into()))?;
        if gt <= lt {
            return Err(TableError::InvalidGitCommit(
                "malformed signature brackets".into(),
            ));
        }

        let name = line[..lt].trim_end().to_string();
        let email = line[lt + 1..gt].to_string();

        let after = line[gt + 1..].trim_start();
        let mut parts = after.splitn(2, ' ');
        let seconds: i64 = parts
            .next()
            .and_then(|s| s.parse().ok())
            .ok_or_else(|| TableError::InvalidGitCommit("invalid timestamp".into()))?;
        let tz_offset = parts
            .next()
            .ok_or_else(|| TableError::InvalidGitCommit("missing timezone offset".into()))?
            .to_string();

        Ok(Self {
            name,
            email,
            seconds,
            tz_offset,
        })
    }

    /// Serialize back to the git identity string format.
    pub fn to_git_string(&self) -> String {
        format!(
            "{} <{}> {} {}",
            self.name, self.email, self.seconds, self.tz_offset
        )
    }
}

// ---------------------------------------------------------------------------
// GitCommit
// ---------------------------------------------------------------------------

/// A parsed git commit object.
///
/// Unknown headers (gpgsig, mergetag, encoding, etc.) are preserved in
/// `extra_headers` with continuation lines intact, so that `parse → to_bytes`
/// reproduces identical bytes for hash fidelity.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GitCommit {
    /// Tree hash as a hex string (40 chars for SHA-1, 64 for SHA-256).
    pub tree: String,
    /// Parent commit hashes as hex strings (0 for root commits, 1+ for merges).
    pub parents: Vec<String>,
    /// Author identity.
    pub author: GitSignature,
    /// Committer identity.
    pub committer: GitSignature,
    /// Extra headers not explicitly parsed (gpgsig, mergetag, encoding, etc.).
    /// Values include unfolded continuation lines (leading space preserved).
    pub extra_headers: Vec<(String, String)>,
    /// Commit message (everything after the blank line separator).
    pub message: String,
}

impl GitCommit {
    /// Parse a raw git commit object.
    ///
    /// The commit format is:
    /// ```text
    /// tree <hex>\n
    /// parent <hex>\n      (0 or more)
    /// author <identity>\n
    /// committer <identity>\n
    /// [extra-header value\n]* (continuation lines start with a space)
    /// \n
    /// <message>
    /// ```
    pub fn parse(data: &[u8]) -> Result<Self, TableError> {
        let text = std::str::from_utf8(data)
            .map_err(|e| TableError::InvalidGitCommit(format!("invalid UTF-8: {e}")))?;

        // Split headers from message at the first blank line.
        let (header_section, message) = match text.find("\n\n") {
            Some(pos) => (&text[..pos], &text[pos + 2..]),
            None => (text, ""),
        };

        // Unfold continuation lines: a line starting with ' ' is appended to the
        // previous header's value (with the newline and leading space preserved).
        let mut header_lines: Vec<String> = Vec::new();
        for line in header_section.split('\n') {
            if line.starts_with(' ') {
                // Continuation line — append to previous.
                if let Some(prev) = header_lines.last_mut() {
                    prev.push('\n');
                    prev.push_str(line);
                } else {
                    return Err(TableError::InvalidGitCommit(
                        "continuation line without preceding header".into(),
                    ));
                }
            } else {
                header_lines.push(line.to_string());
            }
        }

        let mut tree = None;
        let mut parents = Vec::new();
        let mut author = None;
        let mut committer = None;
        let mut extra_headers = Vec::new();

        for line in &header_lines {
            let (key, value) = line.split_once(' ').ok_or_else(|| {
                TableError::InvalidGitCommit(format!("malformed header line: {line}"))
            })?;
            match key {
                "tree" => tree = Some(value.to_string()),
                "parent" => parents.push(value.to_string()),
                "author" => author = Some(GitSignature::parse(value)?),
                "committer" => committer = Some(GitSignature::parse(value)?),
                _ => extra_headers.push((key.to_string(), value.to_string())),
            }
        }

        let tree =
            tree.ok_or_else(|| TableError::InvalidGitCommit("missing tree header".into()))?;
        let author =
            author.ok_or_else(|| TableError::InvalidGitCommit("missing author header".into()))?;
        let committer = committer
            .ok_or_else(|| TableError::InvalidGitCommit("missing committer header".into()))?;

        Ok(Self {
            tree,
            parents,
            author,
            committer,
            extra_headers,
            message: message.to_string(),
        })
    }

    /// Serialize the commit back to the git commit object format.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut buf = String::new();
        buf.push_str(&format!("tree {}\n", self.tree));
        for parent in &self.parents {
            buf.push_str(&format!("parent {}\n", parent));
        }
        buf.push_str(&format!("author {}\n", self.author.to_git_string()));
        buf.push_str(&format!("committer {}\n", self.committer.to_git_string()));
        for (key, value) in &self.extra_headers {
            buf.push_str(&format!("{key} {value}\n"));
        }
        buf.push('\n');
        buf.push_str(&self.message);
        buf.into_bytes()
    }
}

// ---------------------------------------------------------------------------
// Hashing (behind git feature)
// ---------------------------------------------------------------------------

/// Hash a parsed `GitCommit` using SHA-1, returning an O256 (20 bytes + 12 zero bytes).
#[cfg(feature = "git")]
pub fn git_commit_sha1(commit: &GitCommit) -> covalence_hash::O256 {
    let data = commit.to_bytes();
    let oid = covalence_hash::git::commit_sha1(&data);
    let mut out = [0u8; 32];
    out[..oid.as_bytes().len()].copy_from_slice(oid.as_bytes());
    covalence_hash::O256::from_bytes(out)
}

/// Hash a parsed `GitCommit` using SHA-256, returning an O256.
#[cfg(feature = "git")]
pub fn git_commit_sha256(commit: &GitCommit) -> covalence_hash::O256 {
    let data = commit.to_bytes();
    let oid = covalence_hash::git::commit_sha256(&data);
    let mut out = [0u8; 32];
    out.copy_from_slice(oid.as_bytes());
    covalence_hash::O256::from_bytes(out)
}

// ---------------------------------------------------------------------------
// GitCommitBuilder
// ---------------------------------------------------------------------------

/// Builder for constructing a [`GitCommit`] with validation.
///
/// ```
/// use covalence_object::GitCommitBuilder;
///
/// let commit = GitCommitBuilder::new()
///     .tree("4b825dc642cb6eb9a060e54bf899d69f82597401")
///     .author("Test", "test@example.com", 1000000000, "+0000")
///     .committer("Test", "test@example.com", 1000000000, "+0000")
///     .message("initial commit\n")
///     .build()
///     .unwrap();
/// assert_eq!(commit.tree, "4b825dc642cb6eb9a060e54bf899d69f82597401");
/// ```
pub struct GitCommitBuilder {
    tree: Option<String>,
    parents: Vec<String>,
    author: Option<GitSignature>,
    committer: Option<GitSignature>,
    extra_headers: Vec<(String, String)>,
    message: String,
}

impl GitCommitBuilder {
    pub fn new() -> Self {
        Self {
            tree: None,
            parents: Vec::new(),
            author: None,
            committer: None,
            extra_headers: Vec::new(),
            message: String::new(),
        }
    }

    pub fn tree(mut self, hex: &str) -> Self {
        self.tree = Some(hex.to_string());
        self
    }

    pub fn parent(mut self, hex: &str) -> Self {
        self.parents.push(hex.to_string());
        self
    }

    pub fn author(mut self, name: &str, email: &str, seconds: i64, tz_offset: &str) -> Self {
        self.author = Some(GitSignature {
            name: name.to_string(),
            email: email.to_string(),
            seconds,
            tz_offset: tz_offset.to_string(),
        });
        self
    }

    pub fn committer(mut self, name: &str, email: &str, seconds: i64, tz_offset: &str) -> Self {
        self.committer = Some(GitSignature {
            name: name.to_string(),
            email: email.to_string(),
            seconds,
            tz_offset: tz_offset.to_string(),
        });
        self
    }

    pub fn extra_header(mut self, key: &str, value: &str) -> Self {
        self.extra_headers
            .push((key.to_string(), value.to_string()));
        self
    }

    pub fn message(mut self, msg: &str) -> Self {
        self.message = msg.to_string();
        self
    }

    /// Consume the builder and produce a `GitCommit`.
    ///
    /// Returns `Err` if `tree`, `author`, or `committer` was not set.
    pub fn build(self) -> Result<GitCommit, TableError> {
        let tree = self
            .tree
            .ok_or_else(|| TableError::InvalidGitCommit("builder: missing tree".into()))?;
        let author = self
            .author
            .ok_or_else(|| TableError::InvalidGitCommit("builder: missing author".into()))?;
        let committer = self
            .committer
            .ok_or_else(|| TableError::InvalidGitCommit("builder: missing committer".into()))?;

        Ok(GitCommit {
            tree,
            parents: self.parents,
            author,
            committer,
            extra_headers: self.extra_headers,
            message: self.message,
        })
    }
}

impl Default for GitCommitBuilder {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    const EMPTY_TREE: &str = "4b825dc642cb6eb9a060e54bf899d69f82597401";

    fn minimal_commit_bytes() -> Vec<u8> {
        format!(
            "tree {EMPTY_TREE}\n\
             author Test User <test@example.com> 1000000000 +0000\n\
             committer Test User <test@example.com> 1000000000 +0000\n\
             \n\
             test commit\n"
        )
        .into_bytes()
    }

    // --- Signature tests ---

    #[test]
    fn signature_parse_basic() {
        let sig = GitSignature::parse("Test User <test@example.com> 1000000000 +0000").unwrap();
        assert_eq!(sig.name, "Test User");
        assert_eq!(sig.email, "test@example.com");
        assert_eq!(sig.seconds, 1000000000);
        assert_eq!(sig.tz_offset, "+0000");
    }

    #[test]
    fn signature_roundtrip() {
        let input = "Jane Doe <jane@example.com> 1234567890 -0500";
        let sig = GitSignature::parse(input).unwrap();
        assert_eq!(sig.to_git_string(), input);
    }

    #[test]
    fn signature_with_spaces_in_name() {
        let sig = GitSignature::parse("First Middle Last <user@host.com> 0 +0000").unwrap();
        assert_eq!(sig.name, "First Middle Last");
    }

    #[test]
    fn signature_missing_bracket_errors() {
        assert!(GitSignature::parse("No Bracket 1000 +0000").is_err());
    }

    // --- Parse tests ---

    #[test]
    fn parse_minimal_commit() {
        let commit = GitCommit::parse(&minimal_commit_bytes()).unwrap();
        assert_eq!(commit.tree, EMPTY_TREE);
        assert!(commit.parents.is_empty());
        assert_eq!(commit.author.name, "Test User");
        assert_eq!(commit.committer.email, "test@example.com");
        assert_eq!(commit.message, "test commit\n");
        assert!(commit.extra_headers.is_empty());
    }

    #[test]
    fn parse_commit_with_parents() {
        let data = format!(
            "tree {EMPTY_TREE}\n\
             parent aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\n\
             parent bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb\n\
             author A <a@a.com> 100 +0000\n\
             committer C <c@c.com> 200 +0100\n\
             \n\
             merge commit\n"
        );
        let commit = GitCommit::parse(data.as_bytes()).unwrap();
        assert_eq!(commit.parents.len(), 2);
        assert_eq!(
            commit.parents[0],
            "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
        );
        assert_eq!(
            commit.parents[1],
            "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"
        );
    }

    #[test]
    fn parse_commit_with_gpgsig() {
        let data = format!(
            "tree {EMPTY_TREE}\n\
             author A <a@a.com> 100 +0000\n\
             committer C <c@c.com> 200 +0000\n\
             gpgsig -----BEGIN PGP SIGNATURE-----\n \n iQEzBAAB...\n -----END PGP SIGNATURE-----\n\
             \n\
             signed commit\n"
        );
        let commit = GitCommit::parse(data.as_bytes()).unwrap();
        assert_eq!(commit.extra_headers.len(), 1);
        assert_eq!(commit.extra_headers[0].0, "gpgsig");
        assert!(commit.extra_headers[0].1.contains("BEGIN PGP SIGNATURE"));
        assert!(commit.extra_headers[0].1.contains("END PGP SIGNATURE"));
        assert_eq!(commit.message, "signed commit\n");
    }

    #[test]
    fn parse_missing_tree_errors() {
        let data = b"author A <a@a.com> 100 +0000\ncommitter C <c@c.com> 200 +0000\n\nmsg\n";
        assert!(GitCommit::parse(data).is_err());
    }

    // --- Round-trip tests ---

    #[test]
    fn roundtrip_minimal() {
        let original = minimal_commit_bytes();
        let commit = GitCommit::parse(&original).unwrap();
        assert_eq!(commit.to_bytes(), original);
    }

    #[test]
    fn roundtrip_with_parents_and_extras() {
        let data = format!(
            "tree {EMPTY_TREE}\n\
             parent aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\n\
             author A <a@a.com> 100 +0000\n\
             committer C <c@c.com> 200 +0100\n\
             encoding UTF-8\n\
             \n\
             message body\n"
        );
        let bytes = data.into_bytes();
        let commit = GitCommit::parse(&bytes).unwrap();
        assert_eq!(commit.to_bytes(), bytes);
    }

    #[test]
    fn roundtrip_gpgsig_continuation_lines() {
        let data = format!(
            "tree {EMPTY_TREE}\n\
             author A <a@a.com> 100 +0000\n\
             committer C <c@c.com> 200 +0000\n\
             gpgsig -----BEGIN PGP SIGNATURE-----\n \n iQEzBAAB...\n -----END PGP SIGNATURE-----\n\
             \n\
             signed\n"
        );
        let bytes = data.into_bytes();
        let commit = GitCommit::parse(&bytes).unwrap();
        assert_eq!(commit.to_bytes(), bytes);
    }

    // --- Builder tests ---

    #[test]
    fn builder_basic() {
        let commit = GitCommitBuilder::new()
            .tree(EMPTY_TREE)
            .author("A", "a@a.com", 100, "+0000")
            .committer("C", "c@c.com", 200, "+0000")
            .message("msg\n")
            .build()
            .unwrap();
        assert_eq!(commit.tree, EMPTY_TREE);
        assert_eq!(commit.message, "msg\n");
    }

    #[test]
    fn builder_with_parents() {
        let commit = GitCommitBuilder::new()
            .tree(EMPTY_TREE)
            .parent("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")
            .parent("bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb")
            .author("A", "a@a.com", 100, "+0000")
            .committer("C", "c@c.com", 200, "+0000")
            .message("merge\n")
            .build()
            .unwrap();
        assert_eq!(commit.parents.len(), 2);
    }

    #[test]
    fn builder_missing_tree_errors() {
        let result = GitCommitBuilder::new()
            .author("A", "a@a.com", 100, "+0000")
            .committer("C", "c@c.com", 200, "+0000")
            .message("msg\n")
            .build();
        assert!(result.is_err());
    }

    #[test]
    fn builder_missing_author_errors() {
        let result = GitCommitBuilder::new()
            .tree(EMPTY_TREE)
            .committer("C", "c@c.com", 200, "+0000")
            .message("msg\n")
            .build();
        assert!(result.is_err());
    }

    #[test]
    fn builder_missing_committer_errors() {
        let result = GitCommitBuilder::new()
            .tree(EMPTY_TREE)
            .author("A", "a@a.com", 100, "+0000")
            .message("msg\n")
            .build();
        assert!(result.is_err());
    }

    // --- Integration: build → to_bytes → parse round-trip ---

    #[test]
    fn builder_roundtrip() {
        let commit = GitCommitBuilder::new()
            .tree(EMPTY_TREE)
            .parent("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")
            .author("Test User", "test@example.com", 1000000000, "+0000")
            .committer("Test User", "test@example.com", 1000000000, "+0000")
            .extra_header("encoding", "UTF-8")
            .message("round-trip test\n")
            .build()
            .unwrap();

        let bytes = commit.to_bytes();
        let parsed = GitCommit::parse(&bytes).unwrap();
        assert_eq!(parsed, commit);
        assert_eq!(parsed.to_bytes(), bytes);
    }

    // --- Hash tests (git feature) ---

    #[cfg(feature = "git")]
    mod git_tests {
        use super::*;

        #[test]
        fn commit_sha1_matches_git() {
            let bytes = minimal_commit_bytes();
            let commit = GitCommit::parse(&bytes).unwrap();
            let hash = git_commit_sha1(&commit);
            // Same reference value tested in covalence-hash
            assert_eq!(
                &hash.to_string()[..40],
                "e1db426cfe2e239b11128fb96eaeadba3d77af61",
            );
        }

        #[test]
        fn commit_sha1_deterministic() {
            let commit = GitCommitBuilder::new()
                .tree(EMPTY_TREE)
                .author("A", "a@a.com", 100, "+0000")
                .committer("C", "c@c.com", 200, "+0000")
                .message("msg\n")
                .build()
                .unwrap();
            assert_eq!(git_commit_sha1(&commit), git_commit_sha1(&commit));
        }

        #[test]
        fn commit_sha256_deterministic() {
            let commit = GitCommitBuilder::new()
                .tree(EMPTY_TREE)
                .author("A", "a@a.com", 100, "+0000")
                .committer("C", "c@c.com", 200, "+0000")
                .message("msg\n")
                .build()
                .unwrap();
            assert_eq!(git_commit_sha256(&commit), git_commit_sha256(&commit));
        }

        #[test]
        fn different_commits_different_hashes() {
            let c1 = GitCommitBuilder::new()
                .tree(EMPTY_TREE)
                .author("A", "a@a.com", 100, "+0000")
                .committer("C", "c@c.com", 200, "+0000")
                .message("first\n")
                .build()
                .unwrap();
            let c2 = GitCommitBuilder::new()
                .tree(EMPTY_TREE)
                .author("A", "a@a.com", 100, "+0000")
                .committer("C", "c@c.com", 200, "+0000")
                .message("second\n")
                .build()
                .unwrap();
            assert_ne!(git_commit_sha1(&c1), git_commit_sha1(&c2));
        }
    }
}
