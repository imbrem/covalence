//! The MANIFEST golden: pins the name-projected rule inventory of
//! [`Builtins`] to `docs/deps/builtins-manifest.txt` (the TCB-budget
//! golden — a PR that grows the trusted computation set shows it in-diff),
//! and checks the `admits`/manifest coherence contract.
//!
//! Regenerate with:
//! `COV_REGEN_GOLDEN=1 cargo test -p covalence-pure-eval --test manifest`

use std::any::TypeId;
use std::collections::HashSet;

use covalence_pure::{Error, Language, Val, canon};
use covalence_pure_eval::{Builtins, NatAdd, manifest_names};
use covalence_types::Nat;

const GOLDEN: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../../../docs/deps/builtins-manifest.txt"
);

#[test]
fn manifest_matches_golden() {
    let names = manifest_names();
    let m = <Builtins as Language>::MANIFEST.expect("Builtins has a static manifest");

    // Structure: the manifest is Builtins' own, parent-free, and the name
    // projection is 1:1 and in the same order.
    assert_eq!(m.ty, TypeId::of::<Builtins>());
    assert!(m.extends.is_empty(), "Builtins extends nothing");
    assert_eq!(names.len(), m.admits.len(), "name projection is 1:1");
    for ((name, ty), rec) in names.iter().zip(m.admits) {
        assert_eq!(*ty, rec.ty, "name/manifest order drift at {name}");
    }

    // Identity: no duplicate rules, no duplicate labels.
    let mut tys = HashSet::new();
    let mut labels = HashSet::new();
    for (name, ty) in &names {
        assert!(tys.insert(*ty), "duplicate rule TypeId for {name}");
        assert!(labels.insert(name.clone()), "duplicate label {name}");
    }

    // The golden.
    let ours: String = names
        .iter()
        .map(|(n, _)| n.as_str())
        .collect::<Vec<_>>()
        .join("\n")
        + "\n";
    if std::env::var_os("COV_REGEN_GOLDEN").is_some() {
        std::fs::write(GOLDEN, &ours).expect("write golden");
        return;
    }
    let golden = std::fs::read_to_string(GOLDEN)
        .expect("read docs/deps/builtins-manifest.txt (regenerate with COV_REGEN_GOLDEN=1)");
    assert_eq!(
        golden, ours,
        "the Builtins MANIFEST drifted from docs/deps/builtins-manifest.txt — \
         audit the diff, then regenerate with COV_REGEN_GOLDEN=1"
    );
}

#[test]
fn admits_iff_in_manifest() {
    let m = <Builtins as Language>::MANIFEST.unwrap();
    for rec in m.admits {
        assert!(Builtins.admits(rec.ty), "manifest rule not admitted");
    }
    // Non-rules are rejected: the language itself, the base `()`, a random
    // stdlib type.
    assert!(!Builtins.admits(TypeId::of::<Builtins>()));
    assert!(!Builtins.admits(TypeId::of::<()>()));
    assert!(!Builtins.admits(TypeId::of::<String>()));
    // No parents.
    assert!(!Builtins.extends(TypeId::of::<()>()));
    assert!(!Builtins.extends(TypeId::of::<Builtins>()));
}

#[test]
fn canon_gates_on_builtins() {
    let two = || Nat::from(2u8);
    // Admitted in Builtins: mints ⊢ App(NatAdd, Val(2, 2)) = Val(4).
    let thm = canon(NatAdd, (two(), two()), Builtins).expect("NatAdd admitted");
    assert_eq!(thm.rhs(), &Val(Nat::from(4u8)));
    // The same op is NOT admitted in the empty base language.
    assert!(matches!(
        canon(NatAdd, (two(), two()), ()),
        Err(Error::NotAdmitted(_))
    ));
}
