//! Stretch ingestion: parse + verify a full `set.mm` from disk.
//!
//! `set.mm` (~48 MB) is NOT vendored. This test is `#[ignore]`d; to run it,
//! download set.mm to a scratch path and point `COV_SET_MM` at it:
//!
//! ```sh
//! curl -s -o /tmp/set.mm \
//!   https://raw.githubusercontent.com/metamath/set.mm/refs/heads/develop/set.mm
//! COV_SET_MM=/tmp/set.mm cargo test -p covalence-metamath --test set_mm \
//!   --release -- --ignored --nocapture
//! ```
//!
//! It exercises the compressed-proof decoder at scale and reports parse + verify
//! counts and wall-clock. set.mm has ~40k+ assertions; full verification is
//! slow on the un-interned reader, so `--release` is recommended.

use std::time::Instant;

use covalence_metamath::{parse, verify_all};

#[test]
#[ignore = "requires COV_SET_MM=/path/to/set.mm; ~48MB, slow"]
fn set_mm_parses_and_verifies() {
    let path = std::env::var("COV_SET_MM")
        .expect("set COV_SET_MM to the path of a downloaded set.mm");
    let src = std::fs::read_to_string(&path).expect("read set.mm");
    eprintln!("set.mm: {} bytes", src.len());

    let t0 = Instant::now();
    let db = parse(&src).expect("set.mm should parse");
    eprintln!("parsed in {:?}", t0.elapsed());

    let t1 = Instant::now();
    let n = verify_all(&db).expect("set.mm should verify");
    eprintln!("verified {n} theorems in {:?}", t1.elapsed());
    assert!(n > 0);
}
