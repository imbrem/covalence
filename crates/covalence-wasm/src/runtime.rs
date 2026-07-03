//! Runtime + build trait impls for the `cov:wasm@0.1.0` WIT package.
//!
//! See `wit/cov-wasm.wit` for the interface definitions and
//! `notes/vibes/design/proposals/wasm-runtime/` for the broader plan.
//!
//! The build interface is intentionally a 1:1 mirror of
//! `crate::build::{ModuleBuilder, FuncBody}` — every WIT method on
//! `module-builder` delegates straight through to the builder. The
//! `module_builder_methods!` macro below collapses the otherwise
//! identical `lookup → call current FuncBody method → Ok(())` pattern
//! across every instruction binding.

use wasmtime::component::{Component, Linker as CompLinker, ResourceTable};
use wasmtime::{Engine, Module, Store};

// Resource keys in `with:` use the form `pkg:name/interface.resource`
// (dot, not slash, between interface and resource).
// `imports: { default: trappable }` makes import methods return
// `Result<T, String>` directly rather than `Result<Result<T, String>, wasmtime::Error>`.
wasmtime::component::bindgen!({
    path: "wit/cov-wasm.wit",
    world: "cov-wasm-guest",
    with: {
        "cov:wasm/runtime.component": HostComponent,
        "cov:wasm/runtime.instance": HostInstance,
        "cov:wasm/build.module-builder": HostModuleBuilder,
    },
    imports: { default: trappable },
});

use crate::is_component;

/// Backing type for the `cov:wasm/runtime/component` resource.
/// Holds either a compiled component or a compiled core module; the
/// discriminator is set at compile time from the wasm version word.
pub enum HostComponent {
    Component(Component),
    Module(Module),
}

/// Backing type for the `cov:wasm/runtime/instance` resource.
/// One store per instance for MVP; revisit when adding multi-component
/// linking (the "process" abstraction).
pub enum HostInstance {
    Component {
        store: Store<()>,
        instance: wasmtime::component::Instance,
    },
    Module {
        store: Store<()>,
        instance: wasmtime::Instance,
    },
}

/// State the host carries while serving runtime+build calls.
pub struct RuntimeHost {
    engine: Engine,
    table: ResourceTable,
}

impl RuntimeHost {
    pub fn new() -> wasmtime::Result<Self> {
        let mut config = wasmtime::Config::new();
        config.wasm_component_model(true);
        let engine = Engine::new(&config)?;
        Ok(Self {
            engine,
            table: ResourceTable::new(),
        })
    }

    pub fn engine(&self) -> &Engine {
        &self.engine
    }
}

impl cov::wasm::runtime::HostComponent for RuntimeHost {
    fn drop(&mut self, rep: wasmtime::component::Resource<HostComponent>) -> wasmtime::Result<()> {
        self.table.delete(rep)?;
        Ok(())
    }
}

impl cov::wasm::runtime::HostInstance for RuntimeHost {
    fn drop(&mut self, rep: wasmtime::component::Resource<HostInstance>) -> wasmtime::Result<()> {
        self.table.delete(rep)?;
        Ok(())
    }
}

// bindgen wraps each trappable-import body in `wasmtime::Result<...>` —
// outer = trap signal, inner = WIT-level result.
type Trappable<T> = wasmtime::Result<Result<T, String>>;

impl cov::wasm::runtime::Host for RuntimeHost {
    fn compile(
        &mut self,
        bytes: Vec<u8>,
    ) -> Trappable<wasmtime::component::Resource<HostComponent>> {
        let compiled = if is_component(&bytes) {
            match Component::from_binary(&self.engine, &bytes) {
                Ok(c) => HostComponent::Component(c),
                Err(e) => return Ok(Err(e.to_string())),
            }
        } else {
            match Module::from_binary(&self.engine, &bytes) {
                Ok(m) => HostComponent::Module(m),
                Err(e) => return Ok(Err(e.to_string())),
            }
        };
        let rep = self.table.push(compiled).map_err(wasmtime::Error::from)?;
        Ok(Ok(rep))
    }

    fn instantiate(
        &mut self,
        c: wasmtime::component::Resource<HostComponent>,
    ) -> Trappable<wasmtime::component::Resource<HostInstance>> {
        let host_component = self.table.get(&c).map_err(wasmtime::Error::from)?;
        let mut store = Store::new(&self.engine, ());
        let inst = match host_component {
            HostComponent::Component(component) => {
                let mut linker = CompLinker::<()>::new(&self.engine);
                if let Err(e) = linker.define_unknown_imports_as_traps(component) {
                    return Ok(Err(e.to_string()));
                }
                match linker.instantiate(&mut store, component) {
                    Ok(instance) => HostInstance::Component { store, instance },
                    Err(e) => return Ok(Err(e.to_string())),
                }
            }
            HostComponent::Module(module) => {
                // Core modules: empty linker, traps on any unsatisfied import.
                let linker = wasmtime::Linker::<()>::new(&self.engine);
                match linker.instantiate(&mut store, module) {
                    Ok(instance) => HostInstance::Module { store, instance },
                    Err(e) => return Ok(Err(e.to_string())),
                }
            }
        };
        let rep = self.table.push(inst).map_err(wasmtime::Error::from)?;
        Ok(Ok(rep))
    }

    fn call_u32(
        &mut self,
        inst: wasmtime::component::Resource<HostInstance>,
        name: String,
        arg: u32,
    ) -> Trappable<u32> {
        let host_inst = self.table.get_mut(&inst).map_err(wasmtime::Error::from)?;
        match host_inst {
            HostInstance::Component { store, instance } => {
                let func = match instance
                    .get_export_index(&mut *store, None, &name)
                    .and_then(|idx| instance.get_func(&mut *store, &idx))
                {
                    Some(f) => f,
                    None => return Ok(Err(format!("export not found or not a function: {name}"))),
                };
                let typed = match func.typed::<(u32,), (u32,)>(&*store) {
                    Ok(t) => t,
                    Err(e) => return Ok(Err(format!("typing export {name}: {e}"))),
                };
                Ok(typed
                    .call(&mut *store, (arg,))
                    .map(|(out,)| out)
                    .map_err(|e| e.to_string()))
            }
            HostInstance::Module { store, instance } => {
                let func = match instance.get_func(&mut *store, &name) {
                    Some(f) => f,
                    None => return Ok(Err(format!("export not found or not a function: {name}"))),
                };
                let typed = match func.typed::<i32, i32>(&*store) {
                    Ok(t) => t,
                    Err(e) => return Ok(Err(format!("typing export {name}: {e}"))),
                };
                Ok(typed
                    .call(&mut *store, arg as i32)
                    .map(|out| out as u32)
                    .map_err(|e| e.to_string()))
            }
        }
    }
}

impl cov::wasm::build::Host for RuntimeHost {
    fn build_add_module(&mut self, export_name: String, delta: i32) -> Trappable<Vec<u8>> {
        use crate::build::{ModuleBuilder, ValType};
        let mut m = ModuleBuilder::new();
        let mut f = m.func(&[ValType::I32], &[ValType::I32]);
        // `FuncBody::finish` appends the terminal `End` opcode itself —
        // don't call `.end()` here or we'll emit two and produce
        // malformed wasm.
        f.local_get(0).i32_const(delta).i32_add();
        let f_idx = f.finish(&mut m);
        m.export_func(&export_name, f_idx);
        Ok(Ok(m.finish()))
    }
}

/// Backing type for `cov:wasm/build/module-builder`. Holds the actual
/// `crate::build::ModuleBuilder` plus the currently-open `FuncBody` if
/// any — no parallel recording layer. `finish` is one-shot (consumes
/// the builder); subsequent calls trap.
pub struct HostModuleBuilder {
    builder: Option<crate::build::ModuleBuilder>,
    current: Option<crate::build::FuncBody>,
}

fn val_type_from_wit(v: cov::wasm::build::ValType) -> crate::build::ValType {
    use crate::build::ValType as B;
    use cov::wasm::build::ValType as W;
    match v {
        W::I32 => B::I32,
        W::I64 => B::I64,
    }
}

fn block_type_from_wit(b: cov::wasm::build::BlockType) -> crate::build::BlockType {
    use crate::build::BlockType as B;
    use cov::wasm::build::BlockType as W;
    match b {
        W::Empty => B::Empty,
        W::Result(v) => B::Result(val_type_from_wit(v)),
    }
}

fn current<'a>(b: &'a mut HostModuleBuilder) -> wasmtime::Result<&'a mut crate::build::FuncBody> {
    b.current
        .as_mut()
        .ok_or_else(|| wasmtime::Error::msg("no function is open; call start-func first"))
}

fn builder_mut<'a>(
    b: &'a mut HostModuleBuilder,
) -> wasmtime::Result<&'a mut crate::build::ModuleBuilder> {
    b.builder
        .as_mut()
        .ok_or_else(|| wasmtime::Error::msg("module-builder already finished"))
}

/// Generate the bulk of `HostModuleBuilder` instruction methods.
///
/// Each entry expands to a single trait method that looks up the
/// builder, dereferences the currently-open `FuncBody`, calls the
/// matching `crate::build::FuncBody` method, and returns `Ok(())`.
macro_rules! module_builder_methods {
    (
        $($iname:ident ( $($iarg:ident : $ity:ty),* $(,)? ) => $imethod:ident ( $($iarg2:expr),* $(,)? ) ;)*
    ) => {
        $(
            fn $iname(
                &mut self,
                rep: wasmtime::component::Resource<HostModuleBuilder>,
                $($iarg: $ity),*
            ) -> wasmtime::Result<()> {
                current(self.table.get_mut(&rep)?)?.$imethod($($iarg2),*);
                Ok(())
            }
        )*
    };
}

impl cov::wasm::build::HostModuleBuilder for RuntimeHost {
    fn new(&mut self) -> wasmtime::Result<wasmtime::component::Resource<HostModuleBuilder>> {
        self.table
            .push(HostModuleBuilder {
                builder: Some(crate::build::ModuleBuilder::new()),
                current: None,
            })
            .map_err(wasmtime::Error::from)
    }

    // ----- Hand-written top-level methods (signature-translating or one-shot) -----

    fn import_func(
        &mut self,
        rep: wasmtime::component::Resource<HostModuleBuilder>,
        module: String,
        name: String,
        params: Vec<cov::wasm::build::ValType>,
        results: Vec<cov::wasm::build::ValType>,
    ) -> wasmtime::Result<u32> {
        let params: Vec<_> = params.into_iter().map(val_type_from_wit).collect();
        let results: Vec<_> = results.into_iter().map(val_type_from_wit).collect();
        Ok(builder_mut(self.table.get_mut(&rep)?)?
            .import_func(&module, &name, &params, &results)
            .0)
    }

    fn start_func(
        &mut self,
        rep: wasmtime::component::Resource<HostModuleBuilder>,
        params: Vec<cov::wasm::build::ValType>,
        results: Vec<cov::wasm::build::ValType>,
    ) -> wasmtime::Result<u32> {
        let b = self.table.get_mut(&rep)?;
        if b.current.is_some() {
            return Err(wasmtime::Error::msg("a function is already open"));
        }
        let params: Vec<_> = params.into_iter().map(val_type_from_wit).collect();
        let results: Vec<_> = results.into_iter().map(val_type_from_wit).collect();
        let body = builder_mut(b)?.func(&params, &results);
        let idx = body.idx().0;
        b.current = Some(body);
        Ok(idx)
    }

    fn end_func(
        &mut self,
        rep: wasmtime::component::Resource<HostModuleBuilder>,
    ) -> wasmtime::Result<()> {
        let b = self.table.get_mut(&rep)?;
        let body = b
            .current
            .take()
            .ok_or_else(|| wasmtime::Error::msg("no function is open; call start-func first"))?;
        let builder = builder_mut(b)?;
        body.finish(builder);
        Ok(())
    }

    fn export_func(
        &mut self,
        rep: wasmtime::component::Resource<HostModuleBuilder>,
        name: String,
        idx: u32,
    ) -> wasmtime::Result<()> {
        builder_mut(self.table.get_mut(&rep)?)?.export_func(&name, crate::build::FuncIdx(idx));
        Ok(())
    }

    fn export_memory(
        &mut self,
        rep: wasmtime::component::Resource<HostModuleBuilder>,
        name: String,
        idx: u32,
    ) -> wasmtime::Result<()> {
        builder_mut(self.table.get_mut(&rep)?)?.export_memory(&name, crate::build::MemIdx(idx));
        Ok(())
    }

    fn export_global(
        &mut self,
        rep: wasmtime::component::Resource<HostModuleBuilder>,
        name: String,
        idx: u32,
    ) -> wasmtime::Result<()> {
        builder_mut(self.table.get_mut(&rep)?)?.export_global(&name, crate::build::GlobalIdx(idx));
        Ok(())
    }

    fn start(
        &mut self,
        rep: wasmtime::component::Resource<HostModuleBuilder>,
        idx: u32,
    ) -> wasmtime::Result<()> {
        builder_mut(self.table.get_mut(&rep)?)?.start(crate::build::FuncIdx(idx));
        Ok(())
    }

    fn data_active(
        &mut self,
        rep: wasmtime::component::Resource<HostModuleBuilder>,
        mem: u32,
        offset: u32,
        bytes: Vec<u8>,
    ) -> wasmtime::Result<()> {
        builder_mut(self.table.get_mut(&rep)?)?.data_active(
            crate::build::MemIdx(mem),
            offset,
            &bytes,
        );
        Ok(())
    }

    fn finish(
        &mut self,
        rep: wasmtime::component::Resource<HostModuleBuilder>,
    ) -> wasmtime::Result<Vec<u8>> {
        let b = self.table.get_mut(&rep)?;
        let builder = b
            .builder
            .take()
            .ok_or_else(|| wasmtime::Error::msg("module-builder already finished"))?;
        Ok(builder.finish())
    }

    fn finish_validated(
        &mut self,
        rep: wasmtime::component::Resource<HostModuleBuilder>,
    ) -> Trappable<Vec<u8>> {
        let b = self.table.get_mut(&rep).map_err(wasmtime::Error::from)?;
        let builder = b
            .builder
            .take()
            .ok_or_else(|| wasmtime::Error::msg("module-builder already finished"))?;
        Ok(builder.finish_validated().map_err(|e| e.to_string()))
    }

    fn drop(
        &mut self,
        rep: wasmtime::component::Resource<HostModuleBuilder>,
    ) -> wasmtime::Result<()> {
        self.table.delete(rep)?;
        Ok(())
    }

    // ----- Top-level builder calls (each returns a u32 index) -----

    fn memory(
        &mut self,
        rep: wasmtime::component::Resource<HostModuleBuilder>,
        initial_pages: u32,
    ) -> wasmtime::Result<u32> {
        Ok(builder_mut(self.table.get_mut(&rep)?)?
            .memory(initial_pages)
            .0)
    }

    fn global_i32(
        &mut self,
        rep: wasmtime::component::Resource<HostModuleBuilder>,
        init: i32,
    ) -> wasmtime::Result<u32> {
        Ok(builder_mut(self.table.get_mut(&rep)?)?.global_i32(init).0)
    }

    fn global_i32_mut(
        &mut self,
        rep: wasmtime::component::Resource<HostModuleBuilder>,
        init: i32,
    ) -> wasmtime::Result<u32> {
        Ok(builder_mut(self.table.get_mut(&rep)?)?
            .global_i32_mut(init)
            .0)
    }

    fn global_i64(
        &mut self,
        rep: wasmtime::component::Resource<HostModuleBuilder>,
        init: i64,
    ) -> wasmtime::Result<u32> {
        Ok(builder_mut(self.table.get_mut(&rep)?)?.global_i64(init).0)
    }

    fn global_i64_mut(
        &mut self,
        rep: wasmtime::component::Resource<HostModuleBuilder>,
        init: i64,
    ) -> wasmtime::Result<u32> {
        Ok(builder_mut(self.table.get_mut(&rep)?)?
            .global_i64_mut(init)
            .0)
    }

    // ----- Instruction methods (open-function delegations) -----

    module_builder_methods! {
        // Control flow. WIT keywords (`loop`, `if`, `else`, `return`)
        // come through bindgen as `loop_`, `if_`, `else_`, `return_` —
        // matching `crate::build::FuncBody`'s underscored spellings.
        unreachable() => unreachable();
        nop() => nop();
        block(ty: cov::wasm::build::BlockType) => block(block_type_from_wit(ty));
        loop_(ty: cov::wasm::build::BlockType) => loop_(block_type_from_wit(ty));
        if_(ty: cov::wasm::build::BlockType) => if_(block_type_from_wit(ty));
        else_() => else_();
        end() => end();
        br(depth: u32) => br(depth);
        br_if(depth: u32) => br_if(depth);
        return_() => return_();
        // (`drop` instruction intentionally omitted — collides
        // with bindgen's auto-generated resource `drop` method.)
        call(idx: u32) => call(crate::build::FuncIdx(idx));

        // Locals.
        local_get(idx: u32) => local_get(idx);
        local_set(idx: u32) => local_set(idx);
        local_tee(idx: u32) => local_tee(idx);

        // Globals.
        global_get(idx: u32) => global_get(crate::build::GlobalIdx(idx));
        global_set(idx: u32) => global_set(crate::build::GlobalIdx(idx));

        // i32 ops.
        i32_const(val: i32) => i32_const(val);
        i32_add() => i32_add();
        i32_sub() => i32_sub();
        i32_mul() => i32_mul();
        i32_and() => i32_and();
        i32_or() => i32_or();
        i32_xor() => i32_xor();
        i32_shl() => i32_shl();
        i32_shr_s() => i32_shr_s();
        i32_shr_u() => i32_shr_u();
        i32_eqz() => i32_eqz();
        i32_eq() => i32_eq();
        i32_ne() => i32_ne();
        i32_lt_s() => i32_lt_s();
        i32_lt_u() => i32_lt_u();
        i32_gt_s() => i32_gt_s();
        i32_gt_u() => i32_gt_u();
        i32_le_s() => i32_le_s();
        i32_le_u() => i32_le_u();
        i32_ge_s() => i32_ge_s();
        i32_ge_u() => i32_ge_u();

        // i64 ops.
        i64_const(val: i64) => i64_const(val);
        i64_add() => i64_add();
        i64_sub() => i64_sub();
        i64_mul() => i64_mul();
        i64_eqz() => i64_eqz();
        i64_eq() => i64_eq();
        i64_ne() => i64_ne();

        // Conversions.
        i32_wrap_i64() => i32_wrap_i64();
        i64_extend_i32_s() => i64_extend_i32_s();
        i64_extend_i32_u() => i64_extend_i32_u();

        // Memory ops (mem-idx + offset). The Rust API picks alignment.
        i32_load(mem: u32, offset: u32) => i32_load(crate::build::MemIdx(mem), offset);
        i32_store(mem: u32, offset: u32) => i32_store(crate::build::MemIdx(mem), offset);
        i32_load8_u(mem: u32, offset: u32) => i32_load8_u(crate::build::MemIdx(mem), offset);
        i32_store8(mem: u32, offset: u32) => i32_store8(crate::build::MemIdx(mem), offset);
        i64_load(mem: u32, offset: u32) => i64_load(crate::build::MemIdx(mem), offset);
        i64_store(mem: u32, offset: u32) => i64_store(crate::build::MemIdx(mem), offset);
        memory_grow(mem: u32) => memory_grow(crate::build::MemIdx(mem));
        memory_size(mem: u32) => memory_size(crate::build::MemIdx(mem));
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use cov::wasm::{build::Host as _, runtime::Host as _};

    /// Smallest possible self-contained component: a core module with a
    /// single `(u32) -> u32` function exported at the component root.
    fn answer_component() -> Vec<u8> {
        let wat = r#"
            (component
              (core module $m
                (func (export "answer") (param $x i32) (result i32)
                  local.get $x
                  i32.const 1
                  i32.add))
              (core instance $i (instantiate $m))
              (func (export "answer") (param "x" u32) (result u32)
                (canon lift (core func $i "answer")))
            )
        "#;
        wat::parse_str(wat).expect("parse component wat")
    }

    fn unwrap_trappable<T>(r: Trappable<T>, ctx: &str) -> T {
        r.unwrap_or_else(|e| panic!("trap in {ctx}: {e}"))
            .unwrap_or_else(|e| panic!("err in {ctx}: {e}"))
    }

    #[test]
    fn compile_instantiate_call_component() {
        let mut host = RuntimeHost::new().expect("host");
        let comp = unwrap_trappable(host.compile(answer_component()), "compile");
        let inst = unwrap_trappable(host.instantiate(comp), "instantiate");
        let out = unwrap_trappable(host.call_u32(inst, "answer".to_string(), 41), "call");
        assert_eq!(out, 42);
    }

    #[test]
    fn missing_export_errors() {
        let mut host = RuntimeHost::new().expect("host");
        let comp = unwrap_trappable(host.compile(answer_component()), "compile");
        let inst = unwrap_trappable(host.instantiate(comp), "instantiate");
        let err = host
            .call_u32(inst, "nope".to_string(), 0)
            .expect("outer")
            .expect_err("inner");
        assert!(err.contains("nope"), "error message: {err}");
    }

    /// Metacircular smoke test: `build` produces bytes that `runtime`
    /// then compiles, instantiates, and calls. Same loop a guest WASM
    /// component would drive through the WIT.
    #[test]
    fn build_then_run_core_module() {
        let mut host = RuntimeHost::new().expect("host");
        let bytes = unwrap_trappable(host.build_add_module("plus5".to_string(), 5), "build");
        let comp = unwrap_trappable(host.compile(bytes), "compile");
        let inst = unwrap_trappable(host.instantiate(comp), "instantiate");
        let out = unwrap_trappable(host.call_u32(inst, "plus5".to_string(), 37), "call");
        assert_eq!(out, 42);
    }

    /// `Resource<T>` is not Clone; each method call must receive a fresh
    /// handle. Construct one via `Resource::new_borrow(rep)` since all
    /// our resource methods are self-borrow at the WIT level.
    fn borrow(rep: u32) -> wasmtime::component::Resource<HostModuleBuilder> {
        wasmtime::component::Resource::new_borrow(rep)
    }

    fn new_builder_rep(host: &mut RuntimeHost) -> u32 {
        <RuntimeHost as cov::wasm::build::HostModuleBuilder>::new(host)
            .expect("new builder")
            .rep()
    }

    /// Build the same `plus5` module via the `module-builder` resource
    /// (vs. the canned `build-add-module` recipe). Exercises the WIT
    /// resource machinery — constructor, mutating methods, finish.
    #[test]
    fn module_builder_resource_plus5() {
        use cov::wasm::build::{HostModuleBuilder as _, ValType};
        let mut host = RuntimeHost::new().expect("host");
        let b_rep = new_builder_rep(&mut host);

        let f_idx = host
            .start_func(borrow(b_rep), vec![ValType::I32], vec![ValType::I32])
            .expect("start-func");
        host.local_get(borrow(b_rep), 0).expect("local-get");
        host.i32_const(borrow(b_rep), 5).expect("i32-const");
        host.i32_add(borrow(b_rep)).expect("i32-add");
        host.end_func(borrow(b_rep)).expect("end-func");
        host.export_func(borrow(b_rep), "plus5".to_string(), f_idx)
            .expect("export-func");
        let bytes = host.finish(borrow(b_rep)).expect("finish");

        let comp = unwrap_trappable(
            cov::wasm::runtime::Host::compile(&mut host, bytes),
            "compile",
        );
        let inst = unwrap_trappable(
            cov::wasm::runtime::Host::instantiate(&mut host, comp),
            "instantiate",
        );
        let out = unwrap_trappable(
            cov::wasm::runtime::Host::call_u32(&mut host, inst, "plus5".to_string(), 37),
            "call",
        );
        assert_eq!(out, 42);
    }

    /// Two-function module: `triple(x) = x * 3`, plus `triple_plus_one(x)
    /// = triple(x) + 1`. Exercises multi-function builds and `call`.
    #[test]
    fn module_builder_two_functions_with_call() {
        use cov::wasm::build::{HostModuleBuilder as _, ValType};
        let mut host = RuntimeHost::new().expect("host");
        let b_rep = new_builder_rep(&mut host);

        // triple(x) = x * 3
        let triple_idx = host
            .start_func(borrow(b_rep), vec![ValType::I32], vec![ValType::I32])
            .unwrap();
        host.local_get(borrow(b_rep), 0).unwrap();
        host.i32_const(borrow(b_rep), 3).unwrap();
        host.i32_mul(borrow(b_rep)).unwrap();
        host.end_func(borrow(b_rep)).unwrap();

        // triple_plus_one(x) = triple(x) + 1
        let composed_idx = host
            .start_func(borrow(b_rep), vec![ValType::I32], vec![ValType::I32])
            .unwrap();
        host.local_get(borrow(b_rep), 0).unwrap();
        host.call(borrow(b_rep), triple_idx).unwrap();
        host.i32_const(borrow(b_rep), 1).unwrap();
        host.i32_add(borrow(b_rep)).unwrap();
        host.end_func(borrow(b_rep)).unwrap();

        host.export_func(borrow(b_rep), "triple_plus_one".to_string(), composed_idx)
            .unwrap();
        let bytes = host.finish(borrow(b_rep)).expect("finish");

        let comp = unwrap_trappable(
            cov::wasm::runtime::Host::compile(&mut host, bytes),
            "compile",
        );
        let inst = unwrap_trappable(
            cov::wasm::runtime::Host::instantiate(&mut host, comp),
            "instantiate",
        );
        let out = unwrap_trappable(
            cov::wasm::runtime::Host::call_u32(&mut host, inst, "triple_plus_one".to_string(), 10),
            "call",
        );
        assert_eq!(out, 31); // triple(10) + 1 = 30 + 1
    }

    #[test]
    fn module_builder_errors_with_no_open_func() {
        use cov::wasm::build::HostModuleBuilder as _;
        let mut host = RuntimeHost::new().expect("host");
        let b_rep = new_builder_rep(&mut host);
        let err = host.i32_const(borrow(b_rep), 1).expect_err("should trap");
        assert!(err.to_string().contains("no function"), "msg: {err}");
    }

    /// Exercise the freshly-exposed memory + global + control-flow WIT
    /// surface end-to-end: build a module via the WIT, run it through
    /// the same host's runtime.
    #[test]
    fn module_builder_memory_and_globals() {
        use cov::wasm::build::{BlockType as BT, HostModuleBuilder as _, ValType};
        let mut host = RuntimeHost::new().expect("host");
        let b_rep = new_builder_rep(&mut host);

        let mem = host.memory(borrow(b_rep), 1).unwrap();
        let g = host.global_i32_mut(borrow(b_rep), 0).unwrap();

        // store_and_load(x): mem[0] = x; return mem[0] + global
        let idx = host
            .start_func(borrow(b_rep), vec![ValType::I32], vec![ValType::I32])
            .unwrap();
        host.i32_const(borrow(b_rep), 0).unwrap();
        host.local_get(borrow(b_rep), 0).unwrap();
        host.i32_store(borrow(b_rep), mem, 0).unwrap();
        host.i32_const(borrow(b_rep), 0).unwrap();
        host.i32_load(borrow(b_rep), mem, 0).unwrap();
        host.global_get(borrow(b_rep), g).unwrap();
        host.i32_add(borrow(b_rep)).unwrap();
        host.end_func(borrow(b_rep)).unwrap();

        host.export_func(borrow(b_rep), "go".to_string(), idx)
            .unwrap();
        host.export_memory(borrow(b_rep), "mem".to_string(), mem)
            .unwrap();

        // Throw a block in for control-flow coverage even though the
        // outer fn doesn't need it.
        let noop_idx = host.start_func(borrow(b_rep), vec![], vec![]).unwrap();
        host.block(borrow(b_rep), BT::Empty).unwrap();
        host.end(borrow(b_rep)).unwrap();
        host.end_func(borrow(b_rep)).unwrap();
        host.export_func(borrow(b_rep), "noop".to_string(), noop_idx)
            .unwrap();

        let bytes = host
            .finish_validated(borrow(b_rep))
            .expect("outer")
            .expect("validated");

        let comp = unwrap_trappable(
            cov::wasm::runtime::Host::compile(&mut host, bytes),
            "compile",
        );
        let inst = unwrap_trappable(
            cov::wasm::runtime::Host::instantiate(&mut host, comp),
            "instantiate",
        );
        let out = unwrap_trappable(
            cov::wasm::runtime::Host::call_u32(&mut host, inst, "go".to_string(), 42),
            "call",
        );
        assert_eq!(out, 42); // global is 0, so load + global = 42 + 0
    }
}
