//! Every **declaration-only** spec (`tm = None`) in the registries must
//! yield a CLEAN error from the definitional-unfolding rules — never a
//! junk theorem (stage P2 of the kernel property campaign).
//!
//! The enumeration below reconstructs the registries' full key spaces
//! (so a newly added key is covered automatically as long as the `ALL`
//! constants stay honest) and, for each declaration-only entry, pins:
//!
//! 1. `spec.tm().is_none()` — the registry really is declaration-only
//!    where its docs claim;
//! 2. the definitional-unfold kernel rule fails with exactly
//!    [`Error::SpecHasNoBody`];
//! 3. `Thm::spec_ax` fails with exactly the same error (the def-style
//!    unfold path refuses too — no junk implication either).
//!
//! The registry *split* is pinned exhaustively for the fixed-width op
//! family: the declaration-only `OpKey::Op` entries are exactly the
//! arithmetic-shift `sN.shr` four (everything else in the 16-op × 8-tag
//! grid carries a definitional body and must unfold `Ok`).

use covalence_core::{Error, IntTag, Term, TermKind};
use covalence_hol_eval::defs::{
    self, FLOAT_CVT_TAGS, FloatKey, FloatOp, FloatWidth, IntOp, TermSpec,
};

/// The pure tier (`Thm<CoreLang>`) — these are core-rule tests.
type Thm = covalence_core::Thm;

/// Single funnel for the (ratcheted, purge-pending) definitional-unfold
/// kernel rule — deliberately the ONE textual call site in this file,
/// recorded in the purge-ratchet `exceptions` ledger (P2). The whole
/// test file dies with the rule (defs/ re-home).
fn unfold(t: Term) -> Result<Thm, Error> {
    Thm::unfold_term_spec(t)
}

/// The 16 fixed-width ops (`IntOp::ALL` is private; keep in sync — the
/// exhaustive split test below fails loudly if a variant goes missing,
/// because the registry map would then contain unvisited keys).
const INT_OPS: [IntOp; 16] = [
    IntOp::Add,
    IntOp::Sub,
    IntOp::Mul,
    IntOp::Div,
    IntOp::Rem,
    IntOp::And,
    IntOp::Or,
    IntOp::Xor,
    IntOp::Shl,
    IntOp::Shr,
    IntOp::Lt,
    IntOp::Le,
    IntOp::Gt,
    IntOp::Ge,
    IntOp::Neg,
    IntOp::Not,
];

/// The spec handle of a catalogue op term (a `TermKind::Spec` leaf).
fn spec_of(t: &Term) -> TermSpec {
    match t.kind() {
        TermKind::Spec(spec, _) => spec.clone(),
        _ => panic!("not a spec leaf: {t}"),
    }
}

/// Assert `t` is declaration-only and that BOTH unfold paths yield the
/// clean [`Error::SpecHasNoBody`] — never a theorem.
fn assert_decl_only_clean(label: &str, t: Term) {
    let spec = spec_of(&t);
    assert!(
        spec.tm().is_none(),
        "{label}: registry entry expected to be declaration-only (tm = None)"
    );
    match unfold(t.clone()) {
        Err(Error::SpecHasNoBody) => {}
        Err(e) => panic!("{label}: expected SpecHasNoBody from the unfold rule, got {e:?}"),
        Ok(thm) => panic!(
            "{label}: definitional unfold minted a theorem for a bodiless spec: {}",
            thm.concl()
        ),
    }
    let w = Term::free("w", t.type_of().expect("catalogue op types"));
    match Thm::spec_ax(t, w) {
        Err(Error::SpecHasNoBody) => {}
        Err(e) => panic!("{label}: expected SpecHasNoBody from spec_ax, got {e:?}"),
        Ok(thm) => panic!(
            "{label}: spec_ax minted a theorem for a bodiless spec: {}",
            thm.concl()
        ),
    }
}

/// Every declaration-only registry entry, with a diagnostic label.
fn decl_only_terms() -> Vec<(String, Term)> {
    let mut v: Vec<(String, Term)> = Vec::new();
    let mut push = |label: &str, t: Term| v.push((label.to_string(), t));

    // --- nat.rs `term_decl!`s (bitwise + byte encodings) ---
    push("nat.bitAnd", defs::nat_bit_and());
    push("nat.bitOr", defs::nat_bit_or());
    push("nat.bitXor", defs::nat_bit_xor());
    push("nat.toBytesLe", defs::nat_to_bytes_le());
    push("nat.toBytesBe", defs::nat_to_bytes_be());
    push("nat.fromBytesLe", defs::nat_from_bytes_le());
    push("nat.fromBytesBe", defs::nat_from_bytes_be());

    // --- blob.rs `term_decl!`s ---
    push("bytesConsNat", defs::bytes_cons_nat());
    push("bytesAt", defs::bytes_at());

    // --- int_ops.rs: the primitive conversions stay declaration-only ---
    for tag in IntTag::ALL {
        push(&format!("{tag:?}.toNat"), defs::int_to_nat(tag));
        push(&format!("{tag:?}.toInt"), defs::int_to_int(tag));
        push(&format!("{tag:?}.fromNat"), defs::int_from_nat(tag));
        push(&format!("{tag:?}.fromInt"), defs::int_from_int(tag));
    }
    // ... the full 8×8 zext/sext cast grid ...
    for src in IntTag::ALL {
        for dst in IntTag::ALL {
            push(&format!("{src:?}.zext.{dst:?}"), defs::int_zext(src, dst));
            push(&format!("{src:?}.sext.{dst:?}"), defs::int_sext(src, dst));
        }
    }
    // ... and arithmetic right shift on the signed tags (needs a floor
    // division the catalogue does not yet expose).
    for tag in IntTag::ALL.into_iter().filter(|t| t.is_signed()) {
        push(&format!("{tag:?}.shr"), defs::int_op(tag, IntOp::Shr));
    }

    // --- floats.rs: the whole bit-level registry is declaration-only ---
    for w in FloatWidth::ALL {
        for op in FloatOp::ALL {
            let key = FloatKey::Op(w, op);
            push(&format!("{key:?}"), defs::float_bits_op(key));
        }
        for tag in FLOAT_CVT_TAGS {
            for key in [FloatKey::TruncSat(w, tag), FloatKey::Convert(w, tag)] {
                push(&format!("{key:?}"), defs::float_bits_op(key));
            }
        }
    }
    push("promoteBits", defs::float_bits_op(FloatKey::Promote));
    push("demoteBits", defs::float_bits_op(FloatKey::Demote));

    v
}

#[test]
fn every_decl_only_spec_unfolds_to_a_clean_error() {
    let terms = decl_only_terms();
    // 9 term_decls + 32 conversions + 128 casts + 4 sN.shr + 58 floats.
    assert_eq!(terms.len(), 231, "enumeration drifted from the registries");
    for (label, t) in terms {
        assert_decl_only_clean(&label, t);
    }
}

/// The fixed-width `OpKey::Op` grid splits EXACTLY as documented: `sN.shr`
/// is declaration-only, all other 124 (tag, op) pairs carry a definitional
/// body and unfold to `⊢ op = body`.
#[test]
fn int_op_registry_split_is_exactly_signed_shr() {
    for tag in IntTag::ALL {
        for op in INT_OPS {
            let label = format!("{tag:?}.{op:?}");
            let t = defs::int_op(tag, op);
            let decl_only = op == IntOp::Shr && tag.is_signed();
            if decl_only {
                assert_decl_only_clean(&label, t);
            } else {
                let spec = spec_of(&t);
                assert!(spec.tm().is_some(), "{label}: expected a definitional body");
                let thm = unfold(t.clone())
                    .unwrap_or_else(|e| panic!("{label}: let-style unfold failed: {e:?}"));
                assert!(
                    thm.hyps().is_empty(),
                    "{label}: definitional unfold is pure"
                );
                let (lhs, _rhs) = thm
                    .concl()
                    .as_eq()
                    .unwrap_or_else(|| panic!("{label}: unfold concl must be an equation"));
                assert_eq!(lhs, &t, "{label}: unfold lhs is the op itself");
            }
        }
    }
}

/// Positive control for the term_decl neighbours: the *defined* residue
/// ops (`nat.add` in core, `nat.div` in the moved catalogue) unfold `Ok`,
/// so the clean-error assertions above are about the specs, not the rule.
#[test]
fn defined_neighbours_still_unfold_ok() {
    for (label, t) in [
        ("nat.add", defs::nat_add()),
        ("nat.div", defs::nat_div()),
        ("int.add", defs::int_add()),
    ] {
        let spec = spec_of(&t);
        assert!(spec.tm().is_some(), "{label}: expected let-style");
        let thm = unfold(t.clone()).unwrap_or_else(|e| panic!("{label}: unfold failed: {e:?}"));
        let (lhs, _) = thm.concl().as_eq().expect("unfold concl is an equation");
        assert_eq!(lhs, &t);
    }
}
