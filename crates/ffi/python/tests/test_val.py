"""Tests for Val and ValType component model value types."""

import pytest
from covalence import Val, ValType


# -- ValType constructors and properties --------------------------------------

class TestValType:
    def test_primitive_kinds(self):
        assert ValType.bool().kind == "bool"
        assert ValType.u8().kind == "u8"
        assert ValType.s8().kind == "s8"
        assert ValType.u16().kind == "u16"
        assert ValType.s16().kind == "s16"
        assert ValType.u32().kind == "u32"
        assert ValType.s32().kind == "s32"
        assert ValType.u64().kind == "u64"
        assert ValType.s64().kind == "s64"
        assert ValType.f32().kind == "f32"
        assert ValType.f64().kind == "f64"
        assert ValType.v128().kind == "v128"
        assert ValType.char().kind == "char"
        assert ValType.string().kind == "string"

    def test_list(self):
        ty = ValType.list(ValType.u32())
        assert ty.kind == "list"
        assert str(ty) == "(list u32)"

    def test_record(self):
        ty = ValType.record([("name", ValType.string()), ("value", ValType.u32())])
        assert ty.kind == "record"
        assert str(ty) == '(record (field "name" string) (field "value" u32))'

    def test_tuple(self):
        ty = ValType.tuple([ValType.u32(), ValType.string()])
        assert ty.kind == "tuple"
        assert str(ty) == "(tuple u32 string)"

    def test_variant(self):
        ty = ValType.variant([("none", None), ("some", ValType.u32())])
        assert ty.kind == "variant"
        assert str(ty) == '(variant (case "none") (case "some" u32))'

    def test_enum(self):
        ty = ValType.enum_(["red", "green", "blue"])
        assert ty.kind == "enum"
        assert str(ty) == '(enum "red" "green" "blue")'

    def test_option(self):
        ty = ValType.option(ValType.u32())
        assert ty.kind == "option"
        assert str(ty) == "(option u32)"

    def test_result(self):
        ty = ValType.result(ok=ValType.string(), err=ValType.u32())
        assert ty.kind == "result"
        assert str(ty) == "(result (ok string) (error u32))"

    def test_result_no_payloads(self):
        ty = ValType.result()
        assert str(ty) == "(result)"

    def test_flags(self):
        ty = ValType.flags(["read", "write", "execute"])
        assert ty.kind == "flags"
        assert str(ty) == '(flags "read" "write" "execute")'

    def test_equality(self):
        assert ValType.u32() == ValType.u32()
        assert ValType.u32() != ValType.s32()
        assert ValType.list(ValType.u32()) == ValType.list(ValType.u32())
        assert ValType.list(ValType.u32()) != ValType.list(ValType.s32())

    def test_repr(self):
        assert repr(ValType.u32()) == "ValType(u32)"
        assert repr(ValType.list(ValType.string())) == "ValType((list string))"


# -- Val constructors and properties ------------------------------------------

class TestVal:
    def test_primitives(self):
        assert Val.bool(True).kind == "bool"
        assert Val.u8(255).kind == "u8"
        assert Val.s8(-1).kind == "s8"
        assert Val.u16(65535).kind == "u16"
        assert Val.s16(-1).kind == "s16"
        assert Val.u32(42).kind == "u32"
        assert Val.s32(-42).kind == "s32"
        assert Val.u64(100).kind == "u64"
        assert Val.s64(-100).kind == "s64"
        assert Val.f32(3.14).kind == "f32"
        assert Val.f64(2.718).kind == "f64"
        assert Val.char("x").kind == "char"
        assert Val.string("hello").kind == "string"

    def test_list(self):
        v = Val.list([Val.u32(1), Val.u32(2), Val.u32(3)])
        assert v.kind == "list"
        assert str(v) == "[1, 2, 3]"

    def test_record(self):
        v = Val.record({"name": Val.string("foo"), "age": Val.u32(42)})
        assert v.kind == "record"

    def test_tuple(self):
        v = Val.tuple([Val.u32(1), Val.string("two")])
        assert v.kind == "tuple"
        assert str(v) == '(1, "two")'

    def test_variant_with_payload(self):
        v = Val.variant("some", Val.u32(42))
        assert v.kind == "variant"
        assert str(v) == "some(42)"

    def test_variant_without_payload(self):
        v = Val.variant("none")
        assert v.kind == "variant"
        assert str(v) == "none"

    def test_enum(self):
        v = Val.enum_("red")
        assert v.kind == "enum"
        assert str(v) == "red"

    def test_option_some(self):
        v = Val.option(Val.u32(42))
        assert v.kind == "option"
        assert str(v) == "some(42)"

    def test_option_none(self):
        v = Val.none()
        assert v.kind == "option"
        assert str(v) == "none"

    def test_ok(self):
        v = Val.ok(Val.string("yes"))
        assert v.kind == "result"
        assert str(v) == 'ok("yes")'

    def test_err(self):
        v = Val.err(Val.string("no"))
        assert v.kind == "result"
        assert str(v) == 'err("no")'

    def test_ok_unit(self):
        v = Val.ok()
        assert str(v) == "ok"

    def test_err_unit(self):
        v = Val.err()
        assert str(v) == "err"

    def test_flags(self):
        v = Val.flags(["read", "write"])
        assert v.kind == "flags"
        assert str(v) == "{read, write}"

    def test_v128(self):
        v = Val.v128(42)
        assert v.kind == "v128"
        assert str(v) == "42"

    def test_equality(self):
        assert Val.u32(42) == Val.u32(42)
        assert Val.u32(42) != Val.u32(43)
        assert Val.string("a") == Val.string("a")
        assert Val.string("a") != Val.string("b")


# -- val_type property --------------------------------------------------------

class TestValTypeInference:
    def test_primitive(self):
        assert Val.bool(True).val_type == ValType.bool()
        assert Val.u32(42).val_type == ValType.u32()
        assert Val.string("hi").val_type == ValType.string()

    def test_list(self):
        v = Val.list([Val.u32(1), Val.u32(2)])
        assert v.val_type == ValType.list(ValType.u32())

    def test_record(self):
        v = Val.record({"x": Val.u32(1)})
        assert v.val_type == ValType.record([("x", ValType.u32())])

    def test_tuple(self):
        v = Val.tuple([Val.u32(1), Val.string("two")])
        assert v.val_type == ValType.tuple([ValType.u32(), ValType.string()])


# -- conforms_to --------------------------------------------------------------

class TestConformsTo:
    def test_primitive_match(self):
        assert Val.u32(42).conforms_to(ValType.u32())
        assert Val.bool(True).conforms_to(ValType.bool())

    def test_primitive_mismatch(self):
        assert not Val.u32(42).conforms_to(ValType.s32())
        assert not Val.bool(True).conforms_to(ValType.u32())

    def test_list(self):
        ty = ValType.list(ValType.u32())
        assert Val.list([Val.u32(1), Val.u32(2)]).conforms_to(ty)
        assert Val.list([]).conforms_to(ty)
        assert not Val.list([Val.string("x")]).conforms_to(ty)

    def test_record(self):
        ty = ValType.record([("name", ValType.string()), ("age", ValType.u32())])
        good = Val.record({"name": Val.string("foo"), "age": Val.u32(42)})
        assert good.conforms_to(ty)

    def test_enum(self):
        ty = ValType.enum_(["red", "green", "blue"])
        assert Val.enum_("red").conforms_to(ty)
        assert not Val.enum_("yellow").conforms_to(ty)

    def test_variant(self):
        ty = ValType.variant([("none", None), ("some", ValType.u32())])
        assert Val.variant("none").conforms_to(ty)
        assert Val.variant("some", Val.u32(42)).conforms_to(ty)
        assert not Val.variant("other").conforms_to(ty)

    def test_flags(self):
        ty = ValType.flags(["read", "write", "execute"])
        assert Val.flags(["read", "write"]).conforms_to(ty)
        assert Val.flags([]).conforms_to(ty)
        assert not Val.flags(["delete"]).conforms_to(ty)

    def test_option(self):
        ty = ValType.option(ValType.u32())
        assert Val.option(Val.u32(42)).conforms_to(ty)
        assert Val.none().conforms_to(ty)
        assert not Val.option(Val.string("x")).conforms_to(ty)

    def test_result(self):
        ty = ValType.result(ok=ValType.string(), err=ValType.u32())
        assert Val.ok(Val.string("yes")).conforms_to(ty)
        assert Val.err(Val.u32(1)).conforms_to(ty)
        assert not Val.ok(Val.u32(1)).conforms_to(ty)

    def test_tuple(self):
        ty = ValType.tuple([ValType.u32(), ValType.string()])
        assert Val.tuple([Val.u32(1), Val.string("two")]).conforms_to(ty)
        assert not Val.tuple([Val.u32(1)]).conforms_to(ty)

    def test_v128(self):
        assert Val.v128(0).conforms_to(ValType.v128())
        assert not Val.v128(0).conforms_to(ValType.u32())


# -- to_python ----------------------------------------------------------------

class TestToPython:
    def test_bool(self):
        assert Val.bool(True).to_python() is True
        assert Val.bool(False).to_python() is False

    def test_integers(self):
        assert Val.u32(42).to_python() == 42
        assert Val.s32(-1).to_python() == -1
        assert Val.u64(100).to_python() == 100
        assert Val.s8(-128).to_python() == -128

    def test_floats(self):
        assert isinstance(Val.f64(3.14).to_python(), float)
        assert isinstance(Val.f32(1.0).to_python(), float)

    def test_string(self):
        assert Val.string("hello").to_python() == "hello"

    def test_char(self):
        assert Val.char("x").to_python() == "x"

    def test_list(self):
        result = Val.list([Val.u32(1), Val.u32(2), Val.u32(3)]).to_python()
        assert result == [1, 2, 3]
        assert isinstance(result, list)

    def test_record(self):
        result = Val.record({"name": Val.string("foo"), "age": Val.u32(42)}).to_python()
        assert isinstance(result, dict)
        assert result["name"] == "foo"
        assert result["age"] == 42

    def test_tuple(self):
        result = Val.tuple([Val.u32(1), Val.string("two")]).to_python()
        assert isinstance(result, tuple)
        assert result == (1, "two")

    def test_enum(self):
        assert Val.enum_("red").to_python() == "red"

    def test_option_some(self):
        assert Val.option(Val.u32(42)).to_python() == 42

    def test_option_none(self):
        assert Val.none().to_python() is None

    def test_ok(self):
        result = Val.ok(Val.string("yes")).to_python()
        assert result == {"ok": True, "value": "yes"}

    def test_err(self):
        result = Val.err(Val.string("no")).to_python()
        assert result == {"ok": False, "value": "no"}

    def test_variant(self):
        result = Val.variant("some", Val.u32(42)).to_python()
        assert result == {"case": "some", "payload": 42}

    def test_variant_no_payload(self):
        result = Val.variant("none").to_python()
        assert result == {"case": "none", "payload": None}

    def test_flags(self):
        result = Val.flags(["read", "write"]).to_python()
        assert result == ["read", "write"]

    def test_v128(self):
        result = Val.v128(42).to_python()
        assert result == 42
        assert isinstance(result, int)


# -- from_python --------------------------------------------------------------

class TestFromPython:
    def test_bool(self):
        v = Val.from_python(ValType.bool(), True)
        assert v == Val.bool(True)

    def test_u32(self):
        v = Val.from_python(ValType.u32(), 42)
        assert v == Val.u32(42)

    def test_string(self):
        v = Val.from_python(ValType.string(), "hello")
        assert v == Val.string("hello")

    def test_list(self):
        v = Val.from_python(ValType.list(ValType.u32()), [1, 2, 3])
        assert v == Val.list([Val.u32(1), Val.u32(2), Val.u32(3)])

    def test_record(self):
        ty = ValType.record([("name", ValType.string()), ("age", ValType.u32())])
        v = Val.from_python(ty, {"name": "foo", "age": 42})
        assert v.kind == "record"
        assert v.conforms_to(ty)

    def test_tuple(self):
        ty = ValType.tuple([ValType.u32(), ValType.string()])
        v = Val.from_python(ty, (1, "two"))
        assert v == Val.tuple([Val.u32(1), Val.string("two")])

    def test_enum(self):
        ty = ValType.enum_(["red", "green", "blue"])
        v = Val.from_python(ty, "red")
        assert v == Val.enum_("red")

    def test_enum_invalid(self):
        ty = ValType.enum_(["red", "green", "blue"])
        with pytest.raises(ValueError, match="unknown enum case"):
            Val.from_python(ty, "yellow")

    def test_option_some(self):
        ty = ValType.option(ValType.u32())
        v = Val.from_python(ty, 42)
        assert v == Val.option(Val.u32(42))

    def test_option_none(self):
        ty = ValType.option(ValType.u32())
        v = Val.from_python(ty, None)
        assert v == Val.none()

    def test_flags(self):
        ty = ValType.flags(["read", "write", "execute"])
        v = Val.from_python(ty, ["read", "write"])
        assert v == Val.flags(["read", "write"])

    def test_flags_invalid(self):
        ty = ValType.flags(["read", "write", "execute"])
        with pytest.raises(ValueError, match="unknown flag"):
            Val.from_python(ty, ["delete"])

    def test_result_ok(self):
        ty = ValType.result(ok=ValType.string())
        v = Val.from_python(ty, {"ok": True, "value": "yes"})
        assert v == Val.ok(Val.string("yes"))

    def test_result_err(self):
        ty = ValType.result(err=ValType.u32())
        v = Val.from_python(ty, {"ok": False, "value": 1})
        assert v == Val.err(Val.u32(1))

    def test_variant(self):
        ty = ValType.variant([("none", None), ("some", ValType.u32())])
        v = Val.from_python(ty, {"case": "some", "payload": 42})
        assert v == Val.variant("some", Val.u32(42))

    def test_variant_no_payload(self):
        ty = ValType.variant([("none", None), ("some", ValType.u32())])
        v = Val.from_python(ty, {"case": "none"})
        assert v == Val.variant("none")

    def test_v128(self):
        v = Val.from_python(ValType.v128(), 42)
        assert v == Val.v128(42)

    def test_char(self):
        v = Val.from_python(ValType.char(), "x")
        assert v == Val.char("x")

    def test_char_invalid(self):
        with pytest.raises(ValueError):
            Val.from_python(ValType.char(), "")

    def test_roundtrip(self):
        """from_python(ty, val.to_python()) should round-trip."""
        ty = ValType.record([("name", ValType.string()), ("scores", ValType.list(ValType.u32()))])
        original = Val.record({
            "name": Val.string("test"),
            "scores": Val.list([Val.u32(10), Val.u32(20)])
        })
        py_val = original.to_python()
        reconstructed = Val.from_python(ty, py_val)
        assert reconstructed.conforms_to(ty)
