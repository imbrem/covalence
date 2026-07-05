//! Option 2: bind the interchange format to the *real* covalence HOL kernel.
//!
//! The `coln_bridge` example simulates both sides in Rust. This one makes the
//! covalence end genuine. An envelope is authored from an actual
//! `covalence-core` `Thm`: the statement payload is the conclusion encoded as a
//! canonical **S-expression** (`term_to_sexp`), and the witness CID is pinned to
//! the conclusion's real `covalence-init` term hash. "Ingesting" then **parses
//! the payload back into a `Term`** (`term_from_sexp`), **re-checks it through
//! the kernel** (type-checks it at `bool`), and pins it to the witness hash —
//! before re-keying the verified neutral wire CID to covalence's internal
//! `Name256`. No hardcoded recipe: ingest accepts *any* HOL term it is handed.
//!
//! What it does NOT do is re-derive the proof: the waist treats derivations as
//! proof-irrelevant (only existence matters), so re-deriving would require the
//! envelope to carry the derivation steps. That is the federation trust
//! boundary, not a stub.
//!
//! Run:  `cargo run -p covalence-multiformat --example kernel_ingest`

use covalence_init::hash::hash_term;
use covalence_init::sexp::{term_from_sexp, term_to_sexp};
use covalence_init::{HolLightCtx, Term, Thm};
use covalence_multiformat::{Cid, DerivationFact, codec, identity};
use covalence_sexp::prettyprint;

fn section(title: &str) {
    println!("\n\x1b[1m{title}\x1b[0m");
    println!("{}", "─".repeat(title.chars().count()));
}

/// `⊢ x = x` for a `bool` variable `x` via HOL reflexivity — a genuine `Thm`.
/// (We use a free `bool` variable so the conclusion is built only from
/// constructors that round-trip through covalence-init's S-expression codec:
/// `app`, `eq`, `free`.)
fn eq_refl(name: &str) -> Thm {
    let ctx = HolLightCtx::new();
    Thm::refl(Term::free(name, ctx.bool_type())).expect("refl is total on well-typed terms")
}

/// Encode a term as canonical S-expression bytes (the `COV_HOL_THM` payload).
fn term_bytes(t: &Term) -> Vec<u8> {
    let sx = term_to_sexp(t).expect("term serialises");
    let mut buf = Vec::new();
    prettyprint(&[sx], &mut buf).expect("writing to a Vec is infallible");
    buf
}

/// Collapse pretty-printed s-expression bytes to one line for display.
fn compact(bytes: &[u8]) -> String {
    String::from_utf8_lossy(bytes)
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ")
}

/// Parse `COV_HOL_THM` payload bytes back into a kernel `Term`.
fn parse_term(bytes: &[u8]) -> Result<Term, String> {
    let text = std::str::from_utf8(bytes).map_err(|e| format!("utf8: {e}"))?;
    let sxs = covalence_sexp::parse(text).map_err(|e| format!("s-expr: {e:?}"))?;
    let sx = sxs.into_iter().next().ok_or("empty s-expression")?;
    term_from_sexp(&sx).map_err(|e| format!("term: {e}"))
}

/// Author an envelope *from* a real theorem.
fn author(thm: &Thm) -> DerivationFact {
    let concl = thm.concl();
    let term_hash = hash_term(concl);
    DerivationFact {
        logic: codec::logic::HOL,
        axioms: Cid::of(codec::AXIOM_SET, b"theory:HOL-classical/core"),
        prop_codec: codec::COV_HOL_THM,
        prop: term_bytes(concl),
        assumptions: vec![], // refl: proved outright, no scoped hypotheses
        derivation: Cid::from_digest(codec::MM_DERIVATION, *term_hash.as_bytes()),
    }
}

/// Ingest: parse the payload, re-check it through the kernel, pin it to the
/// witness hash. Returns the covalence-internal `Name256` on success.
fn ingest(body: &[u8], advertised: Cid) -> Result<covalence_hash::O256, String> {
    // 1. neutral wire integrity.
    if Cid::of(codec::DERIVATION_FACT, body) != advertised {
        return Err("wire hash mismatch".into());
    }
    let fact = DerivationFact::decode(body).map_err(|e| format!("decode: {e}"))?;
    if fact.logic != codec::logic::HOL || fact.prop_codec != codec::COV_HOL_THM {
        return Err("not a covalence HOL theorem fact".into());
    }

    // 2. parse the payload back into a real kernel Term (the deserializer).
    let term = parse_term(&fact.prop)?;

    // 3. re-check through the kernel: it must type-check at `bool`.
    let ty = term.type_of().map_err(|e| format!("ill-typed: {e}"))?;
    if !ty.is_bool() {
        return Err(format!("conclusion is not a bool proposition (got {ty})"));
    }

    // 4. pin the parsed term to the advertised witness hash.
    let hash = hash_term(&term);
    if fact.derivation != Cid::from_digest(codec::MM_DERIVATION, *hash.as_bytes()) {
        return Err("witness CID is not the hash of the payload term".into());
    }

    Ok(identity::covalence_name(&advertised))
}

fn report(label: &str, body: &[u8], wire: Cid) {
    match ingest(body, wire) {
        Ok(name) => println!("  ✓ {label}: ADMITTED — stored under Name256 {name}"),
        Err(e) => println!("  ✗ {label}: REJECTED — {e}"),
    }
}

fn main() {
    println!("covalence-multiformat — binding the wire format to the real HOL kernel\n");

    // -- 1. author an envelope from a genuine kernel theorem ----------------
    section("1. author from a real covalence-core Thm");
    let thm = eq_refl("x");
    println!("  kernel theorem : ⊢ {}", thm.concl());
    let fact = author(&thm);
    let wire = fact.cid();
    let body = fact.encode();
    println!("  S-expr payload : {}", compact(&fact.prop));
    println!("  wire CID       : {}", wire.to_text());
    println!("  internal Name256: {}", wire.covalence_name());

    // -- 2. ingest: parse + kernel re-check + hash-pin ----------------------
    section("2. ingest: parse the payload, re-check through the kernel");
    report("x = x", &body, wire);

    // -- 3. a *different* theorem ingests too (not recipe-bound) ------------
    section("3. ingest is general — a different theorem also round-trips");
    let other_thm = eq_refl("y");
    let other = author(&other_thm);
    println!("  kernel theorem : ⊢ {}", other_thm.concl());
    report("y = y", &other.encode(), other.cid());

    // -- 4. forgeries the kernel/hash refuse --------------------------------
    section("4. forgeries are refused");

    // (a) swap the statement to a different (well-typed) term, keep the witness.
    let ctx = HolLightCtx::new();
    let swapped = Term::free("z", ctx.bool_type()); // a different bool term
    let mut forged = fact.clone();
    forged.prop = term_bytes(&swapped);
    let fwire = forged.cid();
    println!("  (a) statement swapped to a different term, witness kept:");
    report("swapped-stmt", &forged.encode(), fwire);

    // (b) corrupt the payload so it no longer parses.
    let mut garbled = fact.clone();
    garbled.prop = b"(eq (and p".to_vec();
    let gwire = garbled.cid();
    println!("  (b) payload corrupted (unbalanced s-expression):");
    report("garbled", &garbled.encode(), gwire);

    section("what's real / what's deferred");
    println!("  real     : Thm, term hash, S-expr encode+parse, kernel type-check, Name256.");
    println!("  deferred : re-deriving the proof (waist is proof-irrelevant — needs the");
    println!("             envelope to carry derivation steps); Coln Sedimentree address.");
}
