use covalence_hol_api::{EqualityRules, Hol, NativeHol, TermLanguage, TheoremView};

fn prove_reflexive<L>(logic: &L, term: L::Term) -> Result<L::Thm, L::Error>
where
    L: EqualityRules,
{
    logic.reflexivity(term)
}

#[test]
fn native_hol_adapts_to_dependency_free_logic_capabilities() {
    let logic = NativeHol;
    let proposition_type = Hol::bool_ty(&logic);
    let p = logic.variable("p", proposition_type);
    let theorem = prove_reflexive(&logic, p).unwrap();

    assert!(logic.hypotheses(&theorem).is_empty());
    let (left, right) =
        covalence_hol_api::logic::EqualitySyntax::as_equal(&logic, &logic.conclusion(&theorem))
            .expect("reflexivity concludes an equality");
    assert_eq!(left, right);
}
