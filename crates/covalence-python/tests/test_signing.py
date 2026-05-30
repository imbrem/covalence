"""Tests for the signing API: Principal, Signature, Signer."""

import pytest
import covalence


def test_signer_generate():
    """Signer.generate() produces a signer."""
    s = covalence.Signer.generate()
    assert isinstance(s, covalence.Signer)


def test_signer_principal():
    """Signer.principal() returns a Principal."""
    s = covalence.Signer.generate()
    p = s.principal()
    assert isinstance(p, covalence.Principal)


def test_sign_verify_roundtrip():
    """Sign data, verify with same principal and data -> True."""
    s = covalence.Signer.generate()
    data = b"hello world"
    sig = s.sign(data)
    p = s.principal()
    assert sig.verify(p, data) is True


def test_wrong_principal():
    """Sign with A, verify with B's principal -> False."""
    a = covalence.Signer.generate()
    b = covalence.Signer.generate()
    data = b"test data"
    sig = a.sign(data)
    assert sig.verify(b.principal(), data) is False


def test_wrong_data():
    """Sign data A, verify with data B -> False."""
    s = covalence.Signer.generate()
    sig = s.sign(b"data A")
    assert sig.verify(s.principal(), b"data B") is False


def test_principal_bytes_roundtrip():
    """Principal(p.bytes()) == p."""
    s = covalence.Signer.generate()
    p = s.principal()
    p2 = covalence.Principal(p.bytes())
    assert p == p2


def test_principal_equality():
    """Same signer -> equal principals, different signers -> not equal."""
    a = covalence.Signer.generate()
    b = covalence.Signer.generate()
    assert a.principal() == a.principal()
    assert a.principal() != b.principal()


def test_principal_hash():
    """Equal principals have the same __hash__."""
    s = covalence.Signer.generate()
    p1 = s.principal()
    p2 = s.principal()
    assert hash(p1) == hash(p2)


def test_principal_invalid_bytes():
    """Wrong-length bytes for Principal constructor -> error."""
    with pytest.raises(ValueError):
        covalence.Principal(b"too short")
    with pytest.raises(ValueError):
        covalence.Principal(b"\x00" * 33)


def test_deterministic_signing():
    """Same key + same data -> verify always succeeds."""
    s = covalence.Signer.generate()
    data = b"deterministic"
    for _ in range(5):
        sig = s.sign(data)
        assert sig.verify(s.principal(), data) is True


def test_repr():
    """Check repr strings exist for all three types."""
    s = covalence.Signer.generate()
    p = s.principal()
    sig = s.sign(b"data")
    assert "Signer(" in repr(s)
    assert "Principal(" in repr(p)
    assert "Signature(" in repr(sig)


def test_signature_is_opaque():
    """Signature has no bytes() method."""
    s = covalence.Signer.generate()
    sig = s.sign(b"data")
    assert not hasattr(sig, "bytes")
