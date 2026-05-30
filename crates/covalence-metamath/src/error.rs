#[derive(Debug, thiserror::Error)]
pub enum MmError {
    #[error("parse error at byte {span}: {message}")]
    Parse { span: usize, message: String },
    #[error("unknown label `{label}` in proof of `{theorem}`")]
    UnknownLabel { theorem: String, label: String },
    #[error("stack underflow in proof of `{theorem}`")]
    StackUnderflow { theorem: String },
    #[error("unification failed in proof of `{theorem}`: {message}")]
    UnificationFailed { theorem: String, message: String },
    #[error("proof of `{theorem}` left {count} entries on stack (expected 1)")]
    StackResidue { theorem: String, count: usize },
    #[error("proof result does not match assertion `{theorem}`")]
    ResultMismatch { theorem: String },
    #[error("duplicate label `{label}`")]
    DuplicateLabel { label: String },
    #[error("invalid compressed proof in `{theorem}`: {message}")]
    CompressedProofError { theorem: String, message: String },
    #[error("file error for `{path}`: {message}")]
    FileError { path: String, message: String },
}
