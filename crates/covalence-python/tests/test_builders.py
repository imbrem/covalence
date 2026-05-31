"""Tests for ContainerBuilder, ComponentBuilder, ModuleBuilder."""

import pytest

import covalence


# ---------------------------------------------------------------------------
# ModuleBuilder
# ---------------------------------------------------------------------------

class TestModuleBuilder:
    def test_empty_module(self):
        m = covalence.ModuleBuilder()
        mod = m.build()
        assert isinstance(mod, covalence.Module)

    def test_with_import(self):
        m = covalence.ModuleBuilder()
        m.import_func("env", "foo", params=["i32"], results=["i32"])
        mod = m.build()
        assert ("env", "foo") in mod.imports

    def test_with_start_and_calls(self):
        m = covalence.ModuleBuilder()
        fn = m.import_func("env", "bar")
        f = m.func()
        f.call(fn)
        m.start(f)
        mod = m.build()
        assert isinstance(mod, covalence.Module)

    def test_with_export(self):
        m = covalence.ModuleBuilder()
        f = m.func()
        m.export_func("run", f)
        mod = m.build()
        assert "run" in mod.exports

    def test_func_builder_instructions(self):
        m = covalence.ModuleBuilder()
        f = m.func(params=["i32", "i32"], results=["i32"])
        f.local_get(0)
        f.local_get(1)
        f.i32_add()
        wat = m.wat
        assert "i32.add" in wat
        assert "local.get 0" in wat

    def test_func_builder_locals(self):
        m = covalence.ModuleBuilder()
        f = m.func()
        idx = f.local("i32")
        f.i32_const(42)
        f.local_set(idx)
        wat = m.wat
        assert "(local i32)" in wat
        assert "local.set" in wat

    def test_wat_property(self):
        m = covalence.ModuleBuilder()
        m.import_func("env", "attest")
        wat = m.wat
        assert "(module" in wat
        assert '(import "env" "attest"' in wat

    def test_noop_export(self):
        m = covalence.ModuleBuilder()
        m.export_func("run")
        mod = m.build()
        assert "run" in mod.exports

    def test_func_builder_more_instructions(self):
        m = covalence.ModuleBuilder()
        f = m.func(params=["i32"], results=["i32"])
        f.local_get(0)
        f.i32_eqz()
        f.drop_()
        f.i32_const(1)
        f.return_()
        wat = m.wat
        assert "i32.eqz" in wat
        assert "drop" in wat
        assert "return" in wat


# ---------------------------------------------------------------------------
# ComponentBuilder
# ---------------------------------------------------------------------------

class TestComponentBuilder:
    def test_standalone(self):
        comp = covalence.ComponentBuilder()
        m = comp.module()
        assert comp.container is None
        assert isinstance(m, covalence.ModuleBuilder)

    def test_with_container(self):
        c = covalence.ContainerBuilder()
        comp = c.component
        assert isinstance(comp, covalence.ComponentBuilder)

    def test_build(self):
        comp = covalence.ComponentBuilder()
        result = comp.build()
        assert isinstance(result, covalence.Component)


# ---------------------------------------------------------------------------
# ContainerBuilder
# ---------------------------------------------------------------------------

class TestContainerBuilder:
    def test_empty(self):
        c = covalence.ContainerBuilder()
        container = c.build()
        assert isinstance(container, covalence.Container)
        assert container.imports == []

    def test_attest(self):
        c = covalence.ContainerBuilder()
        m = c.module()
        m.attest()
        container = c.build()
        k = covalence.local()
        pytest.skip("kernel.prove removed during phase 0")
        result = k.prove(container)
        assert result["decision"] == "sat"

    def test_prove_dep(self):
        k = covalence.local()

        # Build dep with export
        dep_c = covalence.ContainerBuilder()
        dep_m = dep_c.module()
        dep_m.attest()
        dep_m.export_func("go")
        dep = dep_c.build()
        dep_hex = str(dep.hash)
        k.store(dep)

        # Build parent that proves dep
        parent_c = covalence.ContainerBuilder()
        parent_m = parent_c.module()
        ref = parent_m.prove(dep, exports=["go"])
        parent_m.call(ref, "go")
        parent_m.attest()
        parent = parent_c.build()

        pytest.skip("kernel.prove removed during phase 0")
        result = k.prove(parent)
        assert result["decision"] == "sat"
        assert dep_hex in result["proved"]
        assert str(parent.hash) in result["proved"]

    def test_link_dep(self):
        k = covalence.local()

        # Build a dep
        dep_c = covalence.ContainerBuilder()
        dep_m = dep_c.module()
        dep_m.attest()
        dep_m.export_func("init")
        dep = dep_c.build()
        k.store(dep)

        # Build container with link
        c = covalence.ContainerBuilder()
        m = c.module()
        lib = m.link(dep.hash, exports=["init"])
        m.call(lib, "init")
        m.attest()
        container = c.build()

        assert any("link-" in imp for imp in container.imports)

    def test_copy_dep(self):
        k = covalence.local()

        dep_c = covalence.ContainerBuilder()
        dep_m = dep_c.module()
        dep_m.attest()
        dep_m.export_func("f")
        dep = dep_c.build()
        k.store(dep)

        c = covalence.ContainerBuilder()
        m = c.module()
        fresh = m.copy(dep.hash, exports=["f"])
        m.call(fresh, "f")
        m.attest()
        container = c.build()

        assert any("copy-" in imp for imp in container.imports)

    def test_export_func(self):
        c = covalence.ContainerBuilder()
        m = c.module()
        m.attest()
        m.export_func("run")
        container = c.build()
        assert "run" in container.exports

    def test_wat_property(self):
        c = covalence.ContainerBuilder()
        m = c.module()
        m.attest()
        wat = c.wat
        assert "(component" in wat
        assert '"attest"' in wat

    def test_hash_polymorphism_o256(self):
        """prove accepts O256."""
        k = covalence.local()
        dep_c = covalence.ContainerBuilder()
        dep_m = dep_c.module()
        dep_m.attest()
        dep_m.export_func("go")
        dep = dep_c.build()
        k.store(dep)

        c = covalence.ContainerBuilder()
        m = c.module()
        ref = m.prove(dep.hash, exports=["go"])  # O256
        m.call(ref, "go")
        m.attest()
        container = c.build()
        pytest.skip("kernel.prove removed during phase 0")
        result = k.prove(container)
        assert result["decision"] == "sat"

    def test_hash_polymorphism_hex_string(self):
        """prove accepts hex string."""
        k = covalence.local()
        dep_c = covalence.ContainerBuilder()
        dep_m = dep_c.module()
        dep_m.attest()
        dep_m.export_func("go")
        dep = dep_c.build()
        dep_hex = str(dep.hash)
        k.store(dep)

        c = covalence.ContainerBuilder()
        m = c.module()
        ref = m.prove(dep_hex, exports=["go"])  # hex string
        m.call(ref, "go")
        m.attest()
        container = c.build()
        pytest.skip("kernel.prove removed during phase 0")
        result = k.prove(container)
        assert result["decision"] == "sat"

    def test_hash_polymorphism_container(self):
        """prove accepts Container directly."""
        k = covalence.local()
        dep_c = covalence.ContainerBuilder()
        dep_m = dep_c.module()
        dep_m.attest()
        dep_m.export_func("go")
        dep = dep_c.build()
        k.store(dep)

        c = covalence.ContainerBuilder()
        m = c.module()
        # Pass Container object directly
        ref = m.prove(dep, exports=["go"])
        m.call(ref, "go")
        m.attest()
        container = c.build()
        pytest.skip("kernel.prove removed during phase 0")
        result = k.prove(container)
        assert result["decision"] == "sat"

    def test_from_link(self):
        """from_link works as prove arg."""
        k = covalence.local()
        dep_c = covalence.ContainerBuilder()
        dep_m = dep_c.module()
        dep_m.attest()
        dep_m.export_func("go")
        dep = dep_c.build()
        k.store(dep)

        # Use from_link
        link = covalence.ContainerBuilder.from_link(dep.hash)

        c = covalence.ContainerBuilder()
        m = c.module()
        ref = m.prove(link, exports=["go"])
        m.call(ref, "go")
        m.attest()
        container = c.build()
        pytest.skip("kernel.prove removed during phase 0")
        result = k.prove(container)
        assert result["decision"] == "sat"

    def test_attest_errors_without_container(self):
        """Standalone ModuleBuilder.attest() errors."""
        m = covalence.ModuleBuilder()
        with pytest.raises(ValueError, match="container chain"):
            m.attest()

    def test_full_composition(self):
        """Build dep with builder, store, build parent, prove → sat with both hashes."""
        k = covalence.local()

        # Build dep
        dep_c = covalence.ContainerBuilder()
        dep_m = dep_c.module()
        dep_m.attest()
        dep_m.export_func("dummy")
        dep = dep_c.build()
        k.store(dep)

        # Build parent
        parent_c = covalence.ContainerBuilder()
        parent_m = parent_c.module()
        inst = parent_m.prove(dep, exports=["dummy"])
        parent_m.call(inst, "dummy")
        parent_m.attest()
        parent = parent_c.build()

        pytest.skip("kernel.prove removed during phase 0")
        result = k.prove(parent)
        assert result["decision"] == "sat"
        assert str(dep.hash) in result["proved"]
        assert str(parent.hash) in result["proved"]
