//! Proof-bearing NativeHol realization of the JSON constructor layer.
//!
//! This module realizes the exact six-way layer `JsonF(X)` from A0007:
//!
//! ```text
//! 1 + bool + decimal + string + list X + list (string × X)
//! ```
//!
//! through the abstract [`covalence_inductive::InductiveBackend`] seam.  It
//! deliberately realizes a *layer at a caller-supplied `X`*, rather than
//! pretending that the current first-order inductive backend can solve the
//! nested equation `X ≅ JsonF(X)`.  The returned bundle nevertheless gives
//! genuine kernel theorems for all six constructor/view equations,
//! constructor injectivity, and constructor distinctness.  Arrays and ordered
//! syntax objects therefore have their honest recursive payload shapes now.
//!
//! The remaining fixpoint is tracked by
//! `json.polynomial-composition`. Semantic objects additionally require a
//! proved unique-name subset of the ordered member sequence; that separate
//! boundary is tracked by `json.semantic-object-native-hol`.

use covalence_core::{Term, Type};
use covalence_hol_eval::EvalThm as Thm;
use covalence_hol_eval::defs;
use covalence_inductive::{
    ArgSort, CtorSpec, IndResult, InductiveBackend, InductiveError, InductiveSpec, InductiveTheory,
};
use covalence_json_api::{JsonConstructor, json_value_family};

use super::decimal::dec_ty;
use super::inductive::ImpredicativeBackend;
use super::inductive::hol::NativeHol;

/// `string × X`, the payload of one ordered JSON object member.
pub fn json_member_layer_type(value: Type) -> Type {
    defs::prod(defs::string_ty(), value)
}

/// `list (string × X)`, preserving source order and duplicate names.
pub fn json_ordered_object_layer_type(value: Type) -> Type {
    defs::list(json_member_layer_type(value))
}

/// The six-constructor first-order presentation of one `JsonF(X)` layer.
///
/// `value` is intentionally external at this level. This makes the list
/// composition explicit in HOL (`list value`, not an opaque `Array`
/// parameter) while leaving the nested fixpoint to a backend that can prove
/// it.
pub fn json_layer_spec(value: Type) -> InductiveSpec<Type> {
    InductiveSpec::new(
        "json-layer",
        vec![
            CtorSpec::nullary("null"),
            CtorSpec::new("bool", [("value", ArgSort::Ext(Type::bool()))]),
            CtorSpec::new("number", [("value", ArgSort::Ext(dec_ty()))]),
            CtorSpec::new("string", [("value", ArgSort::Ext(defs::string_ty()))]),
            CtorSpec::new(
                "array",
                [("elements", ArgSort::Ext(defs::list(value.clone())))],
            ),
            CtorSpec::new(
                "object",
                [(
                    "members",
                    ArgSort::Ext(json_ordered_object_layer_type(value)),
                )],
            ),
        ],
    )
}

/// A proof-bearing realization of one JSON polynomial layer.
///
/// The carrier is opaque. Consumers construct and observe values only through
/// `theory`; the `value_type` records the exact recursive parameter used to
/// instantiate arrays and object members.
pub struct NativeJsonLayer {
    pub value_type: Type,
    pub theory: InductiveTheory<NativeHol>,
}

impl NativeJsonLayer {
    /// Apply one of the six constructors.
    pub fn constructor(
        &self,
        constructor: JsonConstructor,
        fields: &[Term],
    ) -> IndResult<Term, NativeHol> {
        self.theory
            .ctor_app(&NativeHol, constructor.index(), fields)
    }

    /// Interpret the layer with one handler per constructor.
    pub fn view(&self, handlers: &[Term], value: &Term) -> IndResult<Term, NativeHol> {
        self.theory.facts.rec_app(handlers, value)
    }

    /// Prove the constructor/view equation for one constructor.
    pub fn view_constructor(
        &self,
        handlers: &[Term],
        constructor: JsonConstructor,
    ) -> IndResult<Thm, NativeHol> {
        self.theory.facts.comp(handlers, constructor.index())
    }

    /// Prove injectivity of a unary JSON constructor.
    pub fn injective(
        &self,
        constructor: JsonConstructor,
        left: &Term,
        right: &Term,
    ) -> IndResult<Thm, NativeHol> {
        if constructor == JsonConstructor::Null {
            return Err(InductiveError::ArgIndex {
                ctor: "null".into(),
                index: 0,
                arity: 0,
            });
        }
        self.theory.facts.injective(
            constructor.index(),
            0,
            std::slice::from_ref(left),
            std::slice::from_ref(right),
        )
    }

    /// Prove two distinct JSON constructors have disjoint images.
    pub fn distinct(
        &self,
        left_constructor: JsonConstructor,
        left_fields: &[Term],
        right_constructor: JsonConstructor,
        right_fields: &[Term],
    ) -> IndResult<Thm, NativeHol> {
        self.theory.facts.distinct(
            left_constructor.index(),
            right_constructor.index(),
            left_fields,
            right_fields,
        )
    }
}

/// Realize one `JsonF(value)` layer using the generic proof-bearing Church
/// backend. No theorem is minted here: all facts are derived by that backend
/// through NativeHol rules.
pub fn realize_json_layer(value: Type) -> IndResult<NativeJsonLayer, NativeHol> {
    // Keep the portable family declaration on the exercised path: the native
    // lowering below must continue to correspond to a valid recursive A0007
    // family, rather than drifting into an unrelated six-way sum.
    json_value_family()
        .validate()
        .map_err(|error| InductiveError::SpecMismatch(error.to_string()))?;
    let theory =
        ImpredicativeBackend::new().realize(&NativeHol, &json_layer_spec(value.clone()))?;
    Ok(NativeJsonLayer {
        value_type: value,
        theory,
    })
}

// TODO(cov:json.semantic-object-native-hol, major): Define the canonical unique-name predicate over `list (string × json)`, prove duplicate rejection/lookup laws, and expose semantic objects as that subset; ordered syntax objects intentionally remain the raw list above.
// TODO(cov:json.decimal-a0006-native-hol-morphism, major): Prove the boundary between A0006 CanonicalDecimal and init's exact `(int,nat)` decimal representation, including normalization and signed exponents.

#[cfg(test)]
mod tests {
    use super::*;
    use covalence_hol_eval::{mk_bool, mk_int, mk_nat};

    fn false_handler(argument_types: &[Type]) -> Term {
        let mut handler = mk_bool(false);
        for ty in argument_types.iter().rev() {
            handler = Term::abs(ty.clone(), handler);
        }
        handler
    }

    fn handlers(value: &Type) -> Vec<Term> {
        vec![
            mk_bool(false),
            false_handler(&[Type::bool()]),
            false_handler(&[dec_ty()]),
            false_handler(&[defs::string_ty()]),
            false_handler(&[defs::list(value.clone())]),
            false_handler(&[json_ordered_object_layer_type(value.clone())]),
        ]
    }

    #[test]
    fn layer_has_exact_six_constructor_parameter_boundary() {
        let value = Type::tfree("json");
        let spec = json_layer_spec(value.clone());
        assert_eq!(spec.ctors.len(), JsonConstructor::ALL.len());
        assert_eq!(spec.ctors[JsonConstructor::Null.index()].arity(), 0);
        assert_eq!(
            spec.ctors[JsonConstructor::Bool.index()].args[0].1,
            ArgSort::Ext(Type::bool())
        );
        assert_eq!(
            spec.ctors[JsonConstructor::Number.index()].args[0].1,
            ArgSort::Ext(dec_ty())
        );
        assert_eq!(
            spec.ctors[JsonConstructor::String.index()].args[0].1,
            ArgSort::Ext(defs::string_ty())
        );
        assert_eq!(
            spec.ctors[JsonConstructor::Array.index()].args[0].1,
            ArgSort::Ext(defs::list(value.clone()))
        );
        assert_eq!(
            spec.ctors[JsonConstructor::Object.index()].args[0].1,
            ArgSort::Ext(json_ordered_object_layer_type(value))
        );
    }

    #[test]
    fn every_constructor_has_a_genuine_view_law() {
        let value = Type::nat();
        let layer = realize_json_layer(value.clone()).expect("JSON layer");
        let handlers = handlers(&value);
        for constructor in JsonConstructor::ALL {
            let theorem = layer
                .view_constructor(&handlers, constructor)
                .expect("constructor computation");
            assert!(theorem.hyps().is_empty());
            assert_eq!(theorem.concl().type_of().unwrap(), Type::bool());
        }
    }

    #[test]
    fn constructor_no_confusion_covers_payloads_and_tags() {
        let layer = realize_json_layer(Type::nat()).expect("JSON layer");
        let left_number = super::super::decimal::mk_dec(&mk_int(12), &mk_nat(1u32));
        let right_number = super::super::decimal::mk_dec(&mk_int(120), &mk_nat(2u32));
        let injection = layer
            .injective(JsonConstructor::Number, &left_number, &right_number)
            .expect("number injection");
        assert!(injection.hyps().is_empty());

        let array = Term::free("array", defs::list(Type::nat()));
        let distinct = layer
            .distinct(JsonConstructor::Null, &[], JsonConstructor::Array, &[array])
            .expect("null and array are distinct");
        assert!(distinct.hyps().is_empty());
    }

    #[test]
    fn ordered_object_payload_does_not_silently_claim_unique_names() {
        let value = Type::nat();
        let layer = realize_json_layer(value.clone()).expect("JSON layer");
        let members = Term::free("members", json_ordered_object_layer_type(value));
        let object = layer
            .constructor(JsonConstructor::Object, &[members])
            .expect("object constructor");
        assert_eq!(object.type_of().unwrap(), layer.theory.ty);
        assert!(
            !layer.theory.facts.caps().mem_trivial,
            "the Church layer is membership-relativized, not an exact closed fixpoint"
        );
    }
}
