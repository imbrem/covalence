//! Test battery (the signed-integer parsing **benchmark**): genuineness of the
//! general theorems for every radix, plus concrete end-to-end parses over signs,
//! leading zeros, empty / sign-only / embedded-stop inputs, and large values in
//! the NP1 binary normal form — all as genuine (hypothesis- and oracle-free)
//! theorems.

use super::*;
use crate::init::list::{head_cons, head_nil, tail_cons};
use crate::init::nat_parse::ceval::{ch, decide, eval_bin_go, eval_go, eval_parse, pair_parts, s};

/// The four radix configurations as `(is_digit, value)` pairs.
fn configs() -> Vec<(Term, Term)> {
    vec![
        (is_digit_bin(), nat_of_bin_digits()),
        (is_digit_oct(), nat_of_digits(&digit_val_dec(), &lit(8))),
        (is_digit_dec(), nat_of_digits(&digit_val_dec(), &lit(10))),
        (is_digit_hex(), nat_of_digits(&digit_val_hex(), &lit(16))),
    ]
}

/// `⊢ head_is k (s input) = <T|F>` — decide whether `input` starts with the
/// codepoint-`k` char, genuinely (no hypotheses).
fn decide_head_is(k: u64, input: &[u8]) -> (Thm, bool) {
    let ss = s(input);
    let oc_term = head_is(k, &ss);
    if input.is_empty() {
        let hn = head_nil(&char_t()).unwrap(); // head nil = none
        let cn = case_none(&char_t(), &bool_t(), &Term::bool_lit(false), &char_is(k)).unwrap();
        let eq = Thm::refl(oc_term)
            .unwrap()
            .rhs_conv(|t| t.rw_all(&hn))
            .unwrap()
            .trans(cn)
            .unwrap();
        return (eq, false);
    }
    let k0 = input[0] as u64;
    let c0 = ch(k0);
    let cs0 = s(&input[1..]);
    let hc = head_cons(&char_t(), &c0, &cs0).unwrap(); // head (cons c0 cs0) = some c0
    let cse = case_some(
        &char_t(),
        &bool_t(),
        &Term::bool_lit(false),
        &char_is(k),
        &c0,
    )
    .unwrap();
    let (dec, is_k) = decide(&Term::app(char_is(k), c0.clone()), &[k0]);
    let eq = Thm::refl(oc_term)
        .unwrap()
        .rhs_conv(|t| t.rw_all(&hc))
        .unwrap()
        .trans(cse)
        .unwrap()
        .trans(dec)
        .unwrap();
    (eq, is_k)
}

/// `⊢ parse_int_gen is_digit value (s input) = <result>` — the full signed
/// parser, computed for concrete `input`. `pre` is the (Rust-known) maximal
/// digit prefix of the **post-sign** run; `value_of(prefix)` supplies
/// `⊢ value <prefix> = <magnitude>` (radix-specific).
fn eval_parse_int(
    is_digit: &Term,
    value: &Term,
    input: &[u8],
    pre: &[u8],
    value_of: &dyn Fn(&[u8]) -> Thm,
) -> Thm {
    let ss = s(input);
    let (hd45, is45) = decide_head_is(45, input);
    let (hd43, is43) = decide_head_is(43, input);

    // Select the branch, and the (post-sign) substring the nat parser sees.
    let (sel, neg, sub_input, is_sign) = if is45 {
        (
            select_minus(is_digit, value, &ss, &hd45).unwrap(),
            true,
            &input[1..],
            true,
        )
    } else if is43 {
        (
            select_plus(is_digit, value, &ss, &hd45, &hd43).unwrap(),
            false,
            &input[1..],
            true,
        )
    } else {
        (
            select_bare(is_digit, value, &ss, &hd45, &hd43).unwrap(),
            false,
            input,
            false,
        )
    };

    // The nat parse on the substring: `⊢ parse_nat is_digit value (s sub_input)
    // = <nat result>`.
    let nat_res = eval_parse(is_digit, value, sub_input, pre, value_of);

    // Bridge to the term the selection produced (`parse_nat … (tail s)` for a
    // sign, `parse_nat … s` for the bare case).
    let bridged = if is_sign {
        let c0 = ch(input[0] as u64);
        let cs0 = s(&input[1..]);
        tail_cons(&char_t(), &c0, &cs0)
            .unwrap()
            .cong_arg(parse_nat(is_digit, value))
            .unwrap() // parse_nat (tail s) = parse_nat (s sub_input)
            .trans(nat_res)
            .unwrap()
    } else {
        nat_res
    };

    let lifted = sel.rhs_conv(|t| t.rw_all(&bridged)).unwrap(); // parse_int s = lift_signed neg <nat result>

    // Resolve the lift: `some (pair n suf)` → signed some ; `none` → none.
    let res_rhs = rhs_of(&bridged);
    if let Some(payload) = res_rhs
        .as_app()
        .filter(|(f, _)| f.as_app().is_none() && f.as_spec().is_some())
        .map(|(_, p)| p.clone())
    {
        // `some (pair n suf)`.
        let (n, suf) = pair_parts(&payload);
        let lift = if neg {
            lift_neg_some(&n, &suf).unwrap()
        } else {
            lift_pos_some(&n, &suf).unwrap()
        };
        lifted.trans(lift).unwrap()
    } else {
        // `none`.
        lifted
            .trans(lift_none(&Term::bool_lit(neg)).unwrap())
            .unwrap()
    }
}

// ---- genuineness of the general theorems ----

#[test]
fn parse_int_correct_is_genuine() {
    for (is_digit, value) in configs() {
        let thm = parse_int_correct(&is_digit, &value).unwrap();
        assert!(
            thm.hyps().is_empty(),
            "parse_int_correct must be hypothesis-free"
        );
        assert!(thm.concl().type_of().unwrap().is_bool());
    }
}

#[test]
fn lift_and_select_lemmas_are_genuine() {
    let n = Term::free("n", nat_t());
    let suf = Term::free("suf", str_t());
    for t in [
        lift_pos_some(&n, &suf).unwrap(),
        lift_neg_some(&n, &suf).unwrap(),
        lift_none(&Term::bool_lit(true)).unwrap(),
        lift_none(&Term::bool_lit(false)).unwrap(),
    ] {
        assert!(t.hyps().is_empty(), "lift lemma must be axiom-free");
    }
    // positive lift = nat_to_int n ; negative = int_neg (nat_to_int n).
    assert_eq!(
        rhs_of(&lift_pos_some(&n, &suf).unwrap()),
        some_is(pair_is(to_int(n.clone()), suf.clone()))
    );
    assert_eq!(
        rhs_of(&lift_neg_some(&n, &suf).unwrap()),
        some_is(pair_is(neg_wrap(n.clone()), suf.clone()))
    );
}

#[test]
fn sign_reconstruct_is_genuine() {
    let ss = Term::free("s", str_t());
    for k in [45u64, 43] {
        let thm = sign_reconstruct(k, &ss).unwrap();
        assert!(thm.hyps().is_empty(), "sign_reconstruct must be axiom-free");
        assert!(thm.concl().type_of().unwrap().is_bool());
    }
}

#[test]
fn parse_int_builds_and_types() {
    for p in [
        parse_int_bin(),
        parse_int_oct(),
        parse_int(),
        parse_int_hex(),
    ] {
        assert_eq!(p.type_of().unwrap(), Type::fun(str_t(), opt_is_t()));
    }
}

// ---- concrete decimal parses (signs, leading zeros, embedded stops) ----

fn dec_value() -> Term {
    nat_of_digits(&digit_val_dec(), &lit(10))
}

fn dec_value_of(pre: &[u8]) -> Thm {
    eval_go(&digit_val_dec(), &lit(10), pre, &lit(0))
}

/// Extract the `some (pair v rest)` payload of a concrete parse result.
fn some_payload(thm: &Thm) -> (Term, Term) {
    let payload = rhs_of(thm).as_app().unwrap().1.clone();
    pair_parts(&payload)
}

#[test]
fn parse_decimal_negative() {
    // "-42x" → (int_neg (nat_to_int 42), "x").
    let thm = eval_parse_int(&is_digit_dec(), &dec_value(), b"-42x", b"42", &dec_value_of);
    assert!(thm.hyps().is_empty(), "parse must be oracle-free");
    let (v, rest) = some_payload(&thm);
    assert_eq!(v, neg_wrap(lit(42)));
    assert_eq!(rest, s(b"x"));
}

#[test]
fn parse_decimal_plus() {
    // "+42" → (nat_to_int 42, "").
    let thm = eval_parse_int(&is_digit_dec(), &dec_value(), b"+42", b"42", &dec_value_of);
    assert!(thm.hyps().is_empty());
    let (v, rest) = some_payload(&thm);
    assert_eq!(v, to_int(lit(42)));
    assert_eq!(rest, s(b""));
}

#[test]
fn parse_decimal_bare() {
    // "42" (no sign) → (nat_to_int 42, "").
    let thm = eval_parse_int(&is_digit_dec(), &dec_value(), b"42", b"42", &dec_value_of);
    assert!(thm.hyps().is_empty());
    let (v, rest) = some_payload(&thm);
    assert_eq!(v, to_int(lit(42)));
    assert_eq!(rest, s(b""));
}

#[test]
fn parse_decimal_leading_zeros() {
    // "007," → (nat_to_int 7, ","): leading zeros collapse, stop at ','.
    let thm = eval_parse_int(
        &is_digit_dec(),
        &dec_value(),
        b"007,",
        b"007",
        &dec_value_of,
    );
    assert!(thm.hyps().is_empty());
    let (v, rest) = some_payload(&thm);
    assert_eq!(v, to_int(lit(7)));
    assert_eq!(rest, s(b","));
}

#[test]
fn parse_decimal_negative_zero() {
    // "-0" → (int_neg (nat_to_int 0), ""): "-0" is the integer 0 (no neg zero).
    let thm = eval_parse_int(&is_digit_dec(), &dec_value(), b"-0", b"0", &dec_value_of);
    assert!(thm.hyps().is_empty());
    let (v, rest) = some_payload(&thm);
    assert_eq!(v, neg_wrap(lit(0)));
    assert_eq!(rest, s(b""));
    // The value reduces to the `int` literal 0 (negation fixes zero).
    let red = Thm::refl(v).unwrap().rhs_conv(|t| t.reduce()).unwrap();
    assert_eq!(rhs_of(&red), covalence_hol_eval::mk_int(0));
}

// ---- other radices with signs ----

#[test]
fn parse_octal_negative() {
    // "-777" octal → (int_neg (nat_to_int 511), "").
    let value = nat_of_digits(&digit_val_dec(), &lit(8));
    let thm = eval_parse_int(&is_digit_oct(), &value, b"-777", b"777", &|pre| {
        eval_go(&digit_val_dec(), &lit(8), pre, &lit(0))
    });
    assert!(thm.hyps().is_empty());
    let (v, rest) = some_payload(&thm);
    assert_eq!(v, neg_wrap(lit(0o777))); // 511
    assert_eq!(rest, s(b""));
}

#[test]
fn parse_hex_negative_embedded_stop() {
    // "-ff " hex → (int_neg (nat_to_int 255), " ").
    let value = nat_of_digits(&digit_val_hex(), &lit(16));
    let thm = eval_parse_int(&is_digit_hex(), &value, b"-ff ", b"ff", &|pre| {
        eval_go(&digit_val_hex(), &lit(16), pre, &lit(0))
    });
    assert!(thm.hyps().is_empty());
    let (v, rest) = some_payload(&thm);
    assert_eq!(v, neg_wrap(lit(255)));
    assert_eq!(rest, s(b" "));
}

#[test]
fn parse_binary_negative_normal_form() {
    // "-101101" binary → (int_neg (nat_to_int 0b101101), ""), the magnitude in
    // the NP1 log-depth `bit0`/`bit1` normal form (= 45).
    use crate::init::nat_binary::{bit0, bit1};
    let value = nat_of_bin_digits();
    let thm = eval_parse_int(&is_digit_bin(), &value, b"-101101", b"101101", &|pre| {
        eval_bin_go(pre, &lit(0))
    });
    assert!(thm.hyps().is_empty());
    let (v, rest) = some_payload(&thm);
    let mag = bit1(bit0(bit1(bit1(bit0(bit1(lit(0)))))));
    assert_eq!(v, neg_wrap(mag));
    assert_eq!(rest, s(b""));
}

// ---- `none` cases: empty, sign-only, leading non-digit ----

#[test]
fn parse_none_cases() {
    // Empty, bare sign, sign-then-nondigit, leading non-digit → all `none`.
    let never = |_pre: &[u8]| -> Thm { unreachable!("value not evaluated on the none path") };
    for input in [
        b"".as_slice(),
        b"-".as_slice(),
        b"+".as_slice(),
        b"-x".as_slice(),
        b"x".as_slice(),
        b" 12".as_slice(),
    ] {
        let thm = eval_parse_int(&is_digit_dec(), &dec_value(), input, b"", &never);
        assert!(thm.hyps().is_empty(), "parse {input:?} must be oracle-free");
        assert_eq!(rhs_of(&thm), none_is(), "parse {input:?} = none");
    }
}

// ---- the universal theorem tied to computation ----

#[test]
fn parse_int_correct_applied_to_a_concrete_input() {
    // Instantiate the universal decimal theorem at parse "-42x" = (-42, "x")
    // and discharge the hypothesis with the concrete computation. `imp_elim`
    // succeeds only if the concrete output matches the theorem's hypothesis
    // exactly, tying the spec to computation.
    let value = dec_value();
    let corr = parse_int_correct(&is_digit_dec(), &value).unwrap();
    let concrete = eval_parse_int(&is_digit_dec(), &value, b"-42x", b"42", &dec_value_of);
    let (v, rest) = some_payload(&concrete);
    let facts = corr
        .all_elim(s(b"-42x"))
        .unwrap()
        .all_elim(v)
        .unwrap()
        .all_elim(rest)
        .unwrap()
        .imp_elim(concrete)
        .unwrap();
    assert!(facts.hyps().is_empty(), "derived facts must be oracle-free");
    // The conclusion is the 3-way conjunction of guarded case-implications.
    let parts = facts.into_conjuncts();
    assert_eq!(parts.len(), 3);
    // The negative guard fires: `head_is 45 "-42x" = T ⟹ NEG`; discharge it and
    // read off the 4 NEG facts (partition ∧ all-digits ∧ maximal ∧ value).
    let neg = parts[0].clone();
    let g = decide_head_is(45, b"-42x").0; // ⊢ head_is 45 "-42x" = T
    let neg_facts = neg.imp_elim(g).unwrap();
    assert!(neg_facts.hyps().is_empty());
    assert_eq!(neg_facts.into_conjuncts().len(), 4);
}
