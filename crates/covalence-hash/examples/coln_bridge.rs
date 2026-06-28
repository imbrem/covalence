//! Covalence ⇄ Coln interchange-format demo (alpha sketch).
//!
//! A *multiformat*, self-describing, content-addressed envelope for
//! "derivation facts" — the minimal artifact both covalence and Coln can
//! read. The hinge: covalence's thin waist reduces every logic to one
//! proof-irrelevant existential ("∃ a derivation `D` with axiom-set `Ax`
//! of `P`"), and Coln's thesis is "proof checking is database constraint
//! checking". That existential *is* the record below; checking it *is* a
//! store membership query over its content address.
//!
//! Why multiformat (multihash + multicodec + multibase)? covalence's
//! native `O256` is an *opaque* 32-byte hash — the hash function and the
//! payload type are both implicit, known only by convention. That is the
//! wrong property for interop between two systems. So the *wire* identifier
//! is made self-describing:
//!   * **multihash**  — the digest carries its hash-function code (blake3 =
//!     0x1e) and length, so a reader knows how to re-verify it.
//!   * **multicodec** — every payload and the envelope carry a codec code,
//!     so a reader knows *what* it is (a covalence HOL theorem, a Coln
//!     geometric sequent, a derivation witness) — and can skip payloads it
//!     cannot interpret while still verifying hashes and following links.
//!   * **multibase**  — text form is prefixed ('f' = base16-lower) so the
//!     encoding is self-describing too.
//!
//! The wire hash is *neutral* plain BLAKE3 (multihash 0x1e), which is
//! exactly covalence's `O256::blob` primitive. Each system maps a verified
//! envelope onto its own internal identity (covalence's COV_ROOT-keyed
//! Name256, Coln's Sedimentree address) after the bytes check out.
//!
//! Run:  `cargo run -p covalence-hash --example coln_bridge`

use covalence_hash::ContentHash;

// ---------------------------------------------------------------------------
// multiformats primitives (unsigned-LEB128 varints, as in the spec)
// ---------------------------------------------------------------------------

fn put_varint(out: &mut Vec<u8>, mut v: u64) {
    loop {
        let mut b = (v & 0x7f) as u8;
        v >>= 7;
        if v != 0 {
            b |= 0x80;
        }
        out.push(b);
        if v == 0 {
            break;
        }
    }
}

fn get_varint(buf: &[u8]) -> Option<(u64, &[u8])> {
    let mut r = 0u64;
    let mut shift = 0u32;
    for (i, &b) in buf.iter().enumerate() {
        r |= ((b & 0x7f) as u64) << shift;
        if b & 0x80 == 0 {
            return Some((r, &buf[i + 1..]));
        }
        shift += 7;
        if shift >= 64 {
            return None;
        }
    }
    None
}

/// length-delimited bytes: varint(len) ++ bytes
fn put_lenbytes(out: &mut Vec<u8>, b: &[u8]) {
    put_varint(out, b.len() as u64);
    out.extend_from_slice(b);
}

fn get_lenbytes(buf: &[u8]) -> Option<(&[u8], &[u8])> {
    let (n, rest) = get_varint(buf)?;
    let n = n as usize;
    if rest.len() < n {
        return None;
    }
    Some((&rest[..n], &rest[n..]))
}

fn hex(bytes: &[u8]) -> String {
    let mut s = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        s.push_str(&format!("{b:02x}"));
    }
    s
}

// ---------------------------------------------------------------------------
// multicodec content-type codes
//
// 0x55 is the registered 'raw' code. The covalence/Coln-specific codes live
// in the multicodec private-use range (≥ 0x300000) for the alpha; real
// registration comes later.
// ---------------------------------------------------------------------------

const MH_BLAKE3: u64 = 0x1e; // registered multihash code for BLAKE3

const C_AXIOM_SET: u64 = 0x30_0101; // an axiom-set / theory object
const C_COV_HOL_THM: u64 = 0x30_0110; // covalence: a classical HOL theorem payload
const C_COLN_GEOM_SEQ: u64 = 0x30_0120; // Coln: a geometric-logic sequent payload
const C_MM_DERIVATION: u64 = 0x30_0130; // neutral "waist" derivation witness
const C_DERIVATION_FACT: u64 = 0x30_01f0; // the interchange envelope itself

fn codec_name(c: u64) -> String {
    match c {
        0x55 => "raw".into(),
        C_AXIOM_SET => "axiom-set".into(),
        C_COV_HOL_THM => "covalence/hol-theorem".into(),
        C_COLN_GEOM_SEQ => "coln/geometric-sequent".into(),
        C_MM_DERIVATION => "metamath/derivation-witness".into(),
        C_DERIVATION_FACT => "derivation-fact".into(),
        other => format!("unknown(0x{other:x})"),
    }
}

// logic tags
const L_HOL: u64 = 1; // classical higher-order logic (covalence kernel)
const L_GEOMETRIC: u64 = 2; // geometric logic (Coln kernel)
const L_METAMATH: u64 = 3; // the neutral waist

fn logic_name(l: u64) -> &'static str {
    match l {
        L_HOL => "HOL (classical)",
        L_GEOMETRIC => "geometric",
        L_METAMATH => "metamath-waist",
        _ => "unknown",
    }
}

// ---------------------------------------------------------------------------
// CID: multicodec(content-type) ++ multihash(blake3, 32, digest)
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, PartialEq, Eq)]
struct Cid {
    codec: u64,
    digest: [u8; 32],
}

impl Cid {
    /// Content-address `content` under `codec`, using neutral plain BLAKE3 —
    /// i.e. covalence's `O256::blob` primitive (`().tag(..)`).
    fn of(codec: u64, content: &[u8]) -> Cid {
        let digest: [u8; 32] = *content.to_id().as_bytes();
        Cid { codec, digest }
    }

    fn encode(&self) -> Vec<u8> {
        let mut o = Vec::new();
        put_varint(&mut o, self.codec); // multicodec content-type
        put_varint(&mut o, MH_BLAKE3); // multihash fn
        put_varint(&mut o, 32); // multihash length
        o.extend_from_slice(&self.digest);
        o
    }

    fn parse(buf: &[u8]) -> Option<(Cid, &[u8])> {
        let (codec, r) = get_varint(buf)?;
        let (mh, r) = get_varint(r)?;
        if mh != MH_BLAKE3 {
            return None; // self-describing: a reader rejects hashes it can't verify
        }
        let (len, r) = get_varint(r)?;
        if len != 32 || r.len() < 32 {
            return None;
        }
        let mut digest = [0u8; 32];
        digest.copy_from_slice(&r[..32]);
        Some((Cid { codec, digest }, &r[32..]))
    }

    /// Multibase 'f' (base16, lower) text form.
    fn to_text(&self) -> String {
        format!("f{}", hex(&self.encode()))
    }
}

impl std::fmt::Display for Cid {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // abbreviate the digest for readable output
        let h = hex(&self.digest);
        write!(
            f,
            "{}#{}…{}",
            codec_name(self.codec),
            &h[..8],
            &h[h.len() - 4..]
        )
    }
}

// ---------------------------------------------------------------------------
// DerivationFact — the interchange envelope.
//
// This is the reification of the waist existential:
//     "∃ a derivation `D` with axiom-set `Ax` of `P`, modulo assumptions Γ"
// ---------------------------------------------------------------------------

struct DerivationFact {
    logic: u64,            // which logic the statement lives in
    axioms: Cid,           // CID of the axiom-set / theory object
    prop_codec: u64,       // codec of the statement payload
    prop: Vec<u8>,         // the statement P, in `prop_codec`
    assumptions: Vec<Cid>, // scoped hypotheses Γ (e.g. imported foreign Thms, Con(ZFC))
    derivation: Cid,       // CID of the proof witness D (proof-irrelevant: existence only)
}

impl DerivationFact {
    /// Canonical, deterministic body encoding (what the fact's CID hashes).
    fn encode(&self) -> Vec<u8> {
        let mut o = Vec::new();
        put_varint(&mut o, 1); // format version
        put_varint(&mut o, self.logic);
        put_lenbytes(&mut o, &self.axioms.encode());
        put_varint(&mut o, self.prop_codec);
        put_lenbytes(&mut o, &self.prop);
        put_varint(&mut o, self.assumptions.len() as u64);
        for a in &self.assumptions {
            put_lenbytes(&mut o, &a.encode());
        }
        put_lenbytes(&mut o, &self.derivation.encode());
        o
    }

    fn cid(&self) -> Cid {
        Cid::of(C_DERIVATION_FACT, &self.encode())
    }
}

/// The structurally-parsed view of an envelope body — recoverable from the
/// self-describing bytes alone, with no payload-semantics knowledge.
struct ParsedFact<'a> {
    logic: u64,
    axioms: Cid,
    prop_codec: u64,
    prop: &'a [u8],
    assumptions: Vec<Cid>,
    derivation: Cid,
}

fn parse_fact(body: &[u8]) -> Option<ParsedFact<'_>> {
    let (_ver, r) = get_varint(body)?;
    let (logic, r) = get_varint(r)?;
    let (ax_bytes, r) = get_lenbytes(r)?;
    let (axioms, _) = Cid::parse(ax_bytes)?;
    let (prop_codec, r) = get_varint(r)?;
    let (prop, r) = get_lenbytes(r)?;
    let (n_assume, mut r) = get_varint(r)?;
    let mut assumptions = Vec::new();
    for _ in 0..n_assume {
        let (ab, rest) = get_lenbytes(r)?;
        let (cid, _) = Cid::parse(ab)?;
        assumptions.push(cid);
        r = rest;
    }
    let (db, _) = get_lenbytes(r)?;
    let (derivation, _) = Cid::parse(db)?;
    Some(ParsedFact {
        logic,
        axioms,
        prop_codec,
        prop,
        assumptions,
        derivation,
    })
}

/// A reader that knows ONLY the multiformat structure — not the payload
/// semantics. It verifies the content hash and follows links regardless of
/// whether it understands the logic or the payload codec. This is the whole
/// point of multiformat: partial, safe interop.
fn inspect(role: &str, body: &[u8], advertised: Cid) {
    println!(
        "  [{role}] reads envelope advertised as {}",
        advertised.to_text()
    );

    // 1. content-address verification (self-describing hash → re-checkable)
    let recomputed = Cid::of(C_DERIVATION_FACT, body);
    let ok = recomputed == advertised;
    println!(
        "      hash check: {} (recomputed {})",
        if ok { "VALID ✓" } else { "TAMPERED ✗" },
        recomputed
    );
    if !ok {
        return;
    }

    // 2. parse the self-describing body
    let f = parse_fact(body).expect("valid body");
    println!("      logic       : {}", logic_name(f.logic));
    println!("      axiom-set   : {}", f.axioms);
    // The reader may not understand the payload — but the codec tells it so.
    let understandable = matches!(f.prop_codec, C_COV_HOL_THM | C_COLN_GEOM_SEQ);
    if understandable {
        println!(
            "      statement   : [{}] {:?}",
            codec_name(f.prop_codec),
            String::from_utf8_lossy(f.prop)
        );
    } else {
        println!(
            "      statement   : [{}] <{} bytes, codec opaque to me — skipping, hash still verified>",
            codec_name(f.prop_codec),
            f.prop.len()
        );
    }
    println!(
        "      derivation  : {}  (proof-irrelevant: only existence matters)",
        f.derivation
    );
    if f.assumptions.is_empty() {
        println!("      assumptions : none (proved outright)");
    } else {
        println!(
            "      assumptions : {} scoped hypotheses —",
            f.assumptions.len()
        );
        for a in &f.assumptions {
            println!("                    ↳ {}   {}", a, a.to_text());
        }
    }
}

/// A content-addressed fact store: CID → envelope body. This is the database
/// in "proof checking is database constraint checking".
#[derive(Default)]
struct FactStore {
    facts: std::collections::HashMap<String, Vec<u8>>,
}

impl FactStore {
    /// Insert a fact; returns its content address.
    fn put(&mut self, fact: &DerivationFact) -> Cid {
        let cid = fact.cid();
        self.facts.insert(cid.to_text(), fact.encode());
        cid
    }

    /// Proof-checking *as* a constraint query: a fact is admissible iff it is
    /// present, its body hashes to its CID, and — recursively — every
    /// derivation-fact it cites is itself admissible. Assumptions that are not
    /// derivation-facts (axiom-sets, classical principles like LEM) are scoped
    /// trust-roots: leaves, satisfied by assumption. The multicodec tag on
    /// each CID is what tells the checker which case it is in.
    fn check(&self, cid: Cid, depth: usize) -> Result<(), String> {
        let pad = "  ".repeat(depth + 3);

        // Non-derivation CIDs are scoped trust roots (the "Γ" of the sequent).
        if cid.codec != C_DERIVATION_FACT {
            println!("{pad}• trust-root {cid}  (scoped assumption — leaf)");
            return Ok(());
        }

        // Constraint 1: the cited fact must exist in the store.
        let body = self
            .facts
            .get(&cid.to_text())
            .ok_or_else(|| format!("unsatisfied citation: {cid} not in store"))?;

        // Constraint 2: its bytes must hash to its advertised CID.
        if Cid::of(C_DERIVATION_FACT, body) != cid {
            return Err(format!("hash mismatch for {cid}"));
        }

        let f = parse_fact(body).ok_or_else(|| format!("malformed body for {cid}"))?;
        println!("{pad}✓ {cid}  [{}]", logic_name(f.logic));

        // Constraint 3: every cited derivation must itself check (transitively).
        for a in &f.assumptions {
            self.check(*a, depth + 1)?;
        }
        Ok(())
    }
}

fn section(title: &str) {
    println!("\n\x1b[1m{title}\x1b[0m");
    println!("{}", "─".repeat(title.len()));
}

fn main() {
    println!("covalence ⇄ Coln — multiformat derivation-fact interchange (alpha demo)\n");
    println!(
        "wire CID = multibase('f') · multicodec(content-type) · multihash(blake3=0x1e, 32, digest)\n\
         neutral hash = plain BLAKE3 = covalence O256::blob; each side re-keys to its own identity."
    );

    // -- Section 1: covalence authors a classical HOL theorem ----------------
    section("1. covalence authors a classical HOL theorem");

    let hol_axioms = Cid::of(C_AXIOM_SET, b"theory:HOL-classical/opentheory-base");
    let hol_prop = b"|- !p q. (p /\\ q) ==> (q /\\ p)".to_vec();
    // The proof term is content-addressed but never inspected by consumers —
    // the waist only asserts that *some* derivation exists.
    let hol_deriv = Cid::of(
        C_MM_DERIVATION,
        b"derivation:and-comm:CONJ;CONJUNCT2;CONJUNCT1;DISCH",
    );

    let cov_thm = DerivationFact {
        logic: L_HOL,
        axioms: hol_axioms,
        prop_codec: C_COV_HOL_THM,
        prop: hol_prop,
        assumptions: vec![], // proved outright in HOL
        derivation: hol_deriv,
    };
    let cov_thm_cid = cov_thm.cid();
    let cov_thm_body = cov_thm.encode();
    println!("  authored fact: {cov_thm_cid}");
    println!("  wire CID     : {}", cov_thm_cid.to_text());
    println!("  body size    : {} bytes", cov_thm_body.len());
    // roundtrip: re-encoding reproduces the same content address
    assert!(Cid::of(C_DERIVATION_FACT, &cov_thm.encode()) == cov_thm_cid);
    println!("  roundtrip    : re-encode → identical CID ✓");

    // -- Section 2: Coln imports it (borrow classical power) -----------------
    section("2. Coln authors a geometric sequent that BORROWS the HOL theorem");

    // Coln's kernel is geometric (weaker than HOL). To use a classical result
    // it imports the covalence Thm's CID as a *scoped hypothesis* — covalence's
    // own "borrow power without changing the foundation" pattern. A classical
    // principle (LEM) is likewise an explicit, content-addressed assumption.
    let lem_axiom = Cid::of(C_AXIOM_SET, b"assumption:classical/LEM");
    let geom_axioms = Cid::of(C_AXIOM_SET, b"theory:geometric-base/arithmetic-universe");
    let geom_prop = b"x:Comm |- mul-commutes(x)".to_vec();
    let geom_deriv = Cid::of(
        C_MM_DERIVATION,
        b"derivation:import(cov_thm)+geometric-glue",
    );

    let coln_fact = DerivationFact {
        logic: L_GEOMETRIC,
        axioms: geom_axioms,
        prop_codec: C_COLN_GEOM_SEQ,
        prop: geom_prop,
        assumptions: vec![lem_axiom, cov_thm_cid], // ← the bridge: cites covalence's Thm by CID
        derivation: geom_deriv,
    };
    let coln_fact_cid = coln_fact.cid();
    let coln_fact_body = coln_fact.encode();
    println!("  authored fact: {coln_fact_cid}");
    println!("  wire CID     : {}", coln_fact_cid.to_text());
    println!(
        "  imports covalence Thm as scoped hypothesis → {}",
        cov_thm_cid.to_text()
    );

    // -- Section 3: the other side reads it, multiformat-style ---------------
    section("3. each side reads the other's fact (self-describing → partial interop)");
    println!("\n  Coln reading the covalence-authored HOL theorem:");
    inspect("coln ", &cov_thm_body, cov_thm_cid);
    println!("\n  covalence reading the Coln-authored geometric sequent:");
    inspect("covln", &coln_fact_body, coln_fact_cid);

    // resolve the cross-link
    let cited = coln_fact.assumptions.iter().any(|a| *a == cov_thm_cid);
    println!(
        "\n  cross-link resolves: Coln's fact cites covalence's exact Thm CID? {}",
        if cited {
            "YES ✓ — the bridge holds"
        } else {
            "no"
        }
    );

    // -- Section 4: tamper-evidence -----------------------------------------
    section("4. content-addressing is tamper-evident");
    let mut tampered = cov_thm_body.clone();
    let last = tampered.len() - 1;
    tampered[last] ^= 0x01; // flip one bit of the proof-witness digest
    println!("  flip one bit of the covalence fact body, keep the old CID:");
    inspect("coln ", &tampered, cov_thm_cid);

    // -- Section 5: the waist equivalence -----------------------------------
    section("5. the hinge, made literal");
    println!(
        "  covalence waist : \"∃ derivation D of P under Ax (mod Γ)\"  ==  this DerivationFact\n  \
         Coln database   : \"proof checking is constraint checking\"   ==  does CID(fact) ∈ store?\n  \
         → one envelope. covalence cites it as a content-addressed Thm; Coln checks it as a\n    \
         membership query. Same bytes, same hash, two kernels."
    );

    // -- Section 6: run the hinge -------------------------------------------
    section("6. proof-checking AS a constraint query (executed)");
    let mut store = FactStore::default();
    store.put(&cov_thm);
    let coln_in_store = store.put(&coln_fact);
    println!("  store now holds {} facts.\n", store.facts.len());
    println!("  check(Coln sequent) — recurse over citations until trust-roots:");
    match store.check(coln_in_store, 0) {
        Ok(()) => {
            println!("  ⇒ ADMISSIBLE ✓  (every citation resolved across the kernel boundary)")
        }
        Err(e) => println!("  ⇒ REJECTED ✗  {e}"),
    }

    println!("\n  now drop covalence's Thm from the store and re-check the SAME Coln fact:");
    let mut broken = FactStore::default();
    broken.put(&coln_fact); // the imported HOL Thm is absent
    match broken.check(coln_in_store, 0) {
        Ok(()) => println!("  ⇒ ADMISSIBLE ✓"),
        Err(e) => println!(
            "  ⇒ REJECTED ✗  {e}\n     (referential integrity = proof well-formedness: a dangling citation is an open goal)"
        ),
    }

    section("next layers (not in this demo)");
    println!("  · ed25519-signed envelopes (covalence-sig) — federation / authored Thm exchange");
    println!("  · wire-CID ↦ internal identity (COV_ROOT Name256 / Coln Sedimentree address)");
    println!("  · ACSet-schema-as-geometric-theory soundness-certificate facts");
    println!("  · CAR-style bundles: a fact plus the transitive closure of its witnesses");
}
