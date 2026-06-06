//! Re-derive the BLAKE3 + SHA-256 of every committed `.wasm` and assert
//! it matches the build-time generated constants in `hashes.rs`. Catches
//! a hand-edited `.wasm` that wasn't accompanied by a rerun of
//! `cargo run -p covalence-wasm-spec --bin rebuild`.

use covalence_hash::{HashCtx, Sha256};
use covalence_wasm_spec::ALL_SPECS;

#[test]
fn committed_hashes_match_bytes() {
    for spec in ALL_SPECS {
        let blake3 = ().tag(spec.wasm);
        let sha256 = *Sha256.tag(spec.wasm).as_bytes();
        assert_eq!(
            blake3, spec.blake3,
            "BLAKE3 mismatch for {}/{} — wasm bytes do not hash to the committed constant",
            spec.name, spec.variant
        );
        assert_eq!(
            sha256, spec.sha256,
            "SHA-256 mismatch for {}/{} — wasm bytes do not hash to the committed constant",
            spec.name, spec.variant
        );
    }
}
