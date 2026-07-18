//! Mapping a verified neutral wire identity to a system's internal identity.
//!
//! The wire [`Cid`] uses *neutral* plain BLAKE3 so any peer can re-verify it.
//! Once verified, each system addresses the object in its **own** domain. For
//! covalence that domain is the `COV_ROOT`-keyed `Name256` — a `O256` derived
//! under covalence's BLAKE3 derive-key context, domain-separated from the
//! neutral wire digest (and from every other BLAKE3 use in the workspace).
//!
//! Coln's analogue (a Sedimentree address) is not modelled here — see this
//! crate's the generated open-work index.

use covalence_hash::{COV_ROOT, HashCtx, O256};

use crate::cid::Cid;

/// Re-key a verified neutral wire [`Cid`] to covalence's internal `Name256`.
///
/// This is **not** the wire digest: it is `COV_ROOT.tag(cid.encode())`, a
/// distinct value in covalence's keyed domain. Two different wire CIDs map to
/// two different names; the same wire CID always maps to the same name.
pub fn covalence_name(cid: &Cid) -> O256 {
    COV_ROOT.tag(cid.encode())
}

impl Cid {
    /// covalence's internal `Name256` for this wire identity. See
    /// [`covalence_name`].
    pub fn covalence_name(&self) -> O256 {
        covalence_name(self)
    }
}
