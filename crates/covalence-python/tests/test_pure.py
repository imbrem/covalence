"""Tests for the covalence.Type / Term / Thm bindings."""

import pytest

from covalence import Type, Term, Thm


# ---------- Type ----------

def test_type_constructors():
    assert str(Type.prop()) == "prop"
    assert str(Type.bytes()) == "bytes"
    assert str(Type.tfree("a")) == "'a"
    assert str(Type.fun(Type.bytes(), Type.prop())) == "(bytes ⇒ prop)"
    assert str(Type.tycon("bool", [])) == "bool"


def test_type_equality_and_hash():
    a = Type.fun(Type.bytes(), Type.prop())
    b = Type.fun(Type.bytes(), Type.prop())
    assert a == b
    assert hash(a) == hash(b)


# ---------- Term ----------

def test_term_constructors_and_type_of():
    x = Term.free("x", Type.bytes())
    assert x.type_of() == Type.bytes()

    eq_xx = Term.eq(x, x)
    assert eq_xx.type_of() == Type.prop()

    blob = Term.blob(b"hello")
    assert blob.type_of() == Type.bytes()


def test_alpha_equivalent_terms_compare_equal():
    a = Term.abs("x", Type.bytes(), Term.bound(0))
    b = Term.abs("y", Type.bytes(), Term.bound(0))
    assert a == b


def test_open_term_rejected_by_type_of():
    t = Term.bound(0)
    with pytest.raises(ValueError):
        t.type_of()


def test_has_no_obs():
    t = Term.free("x", Type.bytes())
    assert t.has_no_obs()


# ---------- Thm ----------

def test_refl():
    x = Term.free("x", Type.bytes())
    thm = Thm.refl(x)
    assert thm.hyps() == []
    assert thm.concl() == Term.eq(x, x)
    assert thm.has_no_obs()


def test_assume_and_imp_intro():
    p = Term.eq(Term.free("x", Type.bytes()), Term.free("x", Type.bytes()))
    assumed = Thm.assume(p)
    assert assumed.hyps() == [p]

    intro = assumed.imp_intro(p)
    assert intro.hyps() == []
    assert intro.concl() == Term.imp(p, p)


def test_imp_elim():
    p = Term.eq(Term.free("x", Type.bytes()), Term.free("x", Type.bytes()))
    q = Term.eq(Term.free("y", Type.bytes()), Term.free("y", Type.bytes()))

    impl_thm = Thm.assume(Term.imp(p, q))
    hyp_thm = Thm.assume(p)
    combined = impl_thm.imp_elim(hyp_thm)
    assert combined.concl() == q


def test_beta_conv():
    id_fn = Term.abs("x", Type.bytes(), Term.bound(0))
    arg = Term.blob(b"hi")
    app = Term.app(id_fn, arg)
    beta = Thm.beta_conv(app)
    # ⊢ (λx:bytes. x) "hi"  ≡  "hi"
    assert beta.concl() == Term.eq(app, arg)


def test_eta_conv():
    f_ty = Type.fun(Type.bytes(), Type.bytes())
    f = Term.free("f", f_ty)
    body = Term.app(f, Term.bound(0))
    abs_ = Term.abs("x", Type.bytes(), body)
    eta = Thm.eta_conv(abs_)
    assert eta.concl() == Term.eq(abs_, f)


def test_all_intro_then_elim():
    x = Term.free("x", Type.bytes())
    refl = Thm.refl(x)
    universal = refl.all_intro("x", Type.bytes())
    assert universal.hyps() == []

    blob = Term.blob(b"hello")
    instantiated = universal.all_elim(blob)
    # The result should be ⊢ blob ≡ blob.
    assert instantiated.concl() == Term.eq(blob, blob)


def test_inst_tfree():
    a_ty = Type.tfree("a")
    x_a = Term.free("x", a_ty)
    thm = Thm.refl(x_a)
    instantiated = thm.inst_tfree("a", Type.bytes())
    expected = Term.eq(
        Term.free("x", Type.bytes()),
        Term.free("x", Type.bytes()),
    )
    assert instantiated.concl() == expected


def test_tycon_obs_distinct_calls():
    a = Type.tycon_obs("T", [])
    b = Type.tycon_obs("T", [])
    assert a != b


def test_tycon_obs_clone_preserves_identity():
    a = Type.tycon_obs("Foo", [])
    b = a
    assert a == b


def test_new_type_definition_returns_bundle():
    # Witness: assume P x where P : bytes → prop, x : bytes.
    alpha = Type.bytes()
    p = Term.free("P", Type.fun(alpha, Type.prop()))
    x = Term.free("witness", alpha)
    p_x = Term.app(p, x)
    witness = Thm.assume(p_x)

    td = Thm.new_type_definition("τ", "abs", "rep", witness)

    # tau is a fresh tycon-obs.
    assert td.tau != Type.bytes()
    # Empty tvars (alpha was ground).
    assert td.tvars == []
    # Three bijection theorems.
    assert len(td.abs_rep.hyps()) == 1  # P x propagated
    assert len(td.rep_abs_fwd.hyps()) == 1
    assert len(td.rep_abs_back.hyps()) == 1
    # abs and rep are distinct terms.
    assert td.abs_ != td.rep


def test_new_type_definition_polymorphic():
    # Witness over 'a → prop.
    alpha = Type.tfree("a")
    p = Term.free("P", Type.fun(alpha, Type.prop()))
    x = Term.free("witness", alpha)
    p_x = Term.app(p, x)
    witness = Thm.assume(p_x)

    td = Thm.new_type_definition("List", "abs", "rep", witness)
    assert td.tvars == ["a"]
