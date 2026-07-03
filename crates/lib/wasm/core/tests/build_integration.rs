//! Integration tests for the WASM module builder.
//!
//! These tests build modules using [`ModuleBuilder`], then instantiate them
//! with wasmtime to verify the generated code actually runs correctly.

use covalence_wasm::build::{BlockType, ModuleBuilder, ValType};
use covalence_wasm::engine::wasmtime::{Engine, Instance, Module, Store};

fn run_module(wasm: &[u8]) -> (Store<()>, Instance) {
    let engine = Engine::default();
    let module = Module::new(&engine, wasm).expect("valid module");
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).expect("instantiate");
    (store, instance)
}

#[test]
fn add_function_executes() {
    let mut b = ModuleBuilder::new();
    let mut f = b.func(&[ValType::I32, ValType::I32], &[ValType::I32]);
    f.local_get(0).local_get(1).i32_add();
    let idx = f.finish(&mut b);
    b.export_func("add", idx);

    let wasm = b.finish();
    let (mut store, instance) = run_module(&wasm);
    let add = instance
        .get_typed_func::<(i32, i32), i32>(&mut store, "add")
        .unwrap();

    assert_eq!(add.call(&mut store, (3, 4)).unwrap(), 7);
    assert_eq!(add.call(&mut store, (0, 0)).unwrap(), 0);
    assert_eq!(add.call(&mut store, (-1, 1)).unwrap(), 0);
}

#[test]
fn locals_work_correctly() {
    let mut b = ModuleBuilder::new();
    // func(a, b) -> (a + b) * 2, using locals
    let mut f = b.func(&[ValType::I32, ValType::I32], &[ValType::I32]);
    let sum = f.local(ValType::I32);
    f.local_get(0).local_get(1).i32_add().local_set(sum);
    f.local_get(sum).i32_const(2).i32_mul();
    let idx = f.finish(&mut b);
    b.export_func("calc", idx);

    let wasm = b.finish();
    let (mut store, instance) = run_module(&wasm);
    let calc = instance
        .get_typed_func::<(i32, i32), i32>(&mut store, "calc")
        .unwrap();

    assert_eq!(calc.call(&mut store, (3, 4)).unwrap(), 14);
    assert_eq!(calc.call(&mut store, (10, 5)).unwrap(), 30);
}

#[test]
fn global_get_set() {
    let mut b = ModuleBuilder::new();
    let g = b.global_i32_mut(0);

    let mut f = b.func(&[ValType::I32], &[]);
    f.local_get(0).global_set(g);
    let set = f.finish(&mut b);
    b.export_func("set", set);

    let mut f = b.func(&[], &[ValType::I32]);
    f.global_get(g);
    let get = f.finish(&mut b);
    b.export_func("get", get);

    let wasm = b.finish();
    let (mut store, instance) = run_module(&wasm);
    let set = instance
        .get_typed_func::<i32, ()>(&mut store, "set")
        .unwrap();
    let get = instance
        .get_typed_func::<(), i32>(&mut store, "get")
        .unwrap();

    assert_eq!(get.call(&mut store, ()).unwrap(), 0);
    set.call(&mut store, 42).unwrap();
    assert_eq!(get.call(&mut store, ()).unwrap(), 42);
}

#[test]
fn if_else_executes() {
    let mut b = ModuleBuilder::new();
    // abs(x)
    let mut f = b.func(&[ValType::I32], &[ValType::I32]);
    f.local_get(0)
        .i32_const(0)
        .i32_lt_s()
        .if_(BlockType::Result(ValType::I32))
        .i32_const(0)
        .local_get(0)
        .i32_sub()
        .else_()
        .local_get(0)
        .end();
    let idx = f.finish(&mut b);
    b.export_func("abs", idx);

    let wasm = b.finish();
    let (mut store, instance) = run_module(&wasm);
    let abs = instance
        .get_typed_func::<i32, i32>(&mut store, "abs")
        .unwrap();

    assert_eq!(abs.call(&mut store, 5).unwrap(), 5);
    assert_eq!(abs.call(&mut store, -5).unwrap(), 5);
    assert_eq!(abs.call(&mut store, 0).unwrap(), 0);
}

#[test]
fn loop_countdown() {
    let mut b = ModuleBuilder::new();
    // Counts down n to 0, returns 0
    let mut f = b.func(&[ValType::I32], &[ValType::I32]);
    f.block(BlockType::Empty)
        .loop_(BlockType::Empty)
        .local_get(0)
        .i32_eqz()
        .br_if(1)
        .local_get(0)
        .i32_const(1)
        .i32_sub()
        .local_set(0)
        .br(0)
        .end()
        .end();
    f.local_get(0);
    let idx = f.finish(&mut b);
    b.export_func("countdown", idx);

    let wasm = b.finish();
    let (mut store, instance) = run_module(&wasm);
    let countdown = instance
        .get_typed_func::<i32, i32>(&mut store, "countdown")
        .unwrap();

    assert_eq!(countdown.call(&mut store, 10).unwrap(), 0);
    assert_eq!(countdown.call(&mut store, 0).unwrap(), 0);
}

#[test]
fn memory_store_and_load() {
    let mut b = ModuleBuilder::new();
    let mem = b.memory(1);
    b.export_memory("mem", mem);

    let mut f = b.func(&[ValType::I32, ValType::I32], &[]);
    f.local_get(0).local_get(1).i32_store(mem, 0);
    let store_fn = f.finish(&mut b);
    b.export_func("store", store_fn);

    let mut f = b.func(&[ValType::I32], &[ValType::I32]);
    f.local_get(0).i32_load(mem, 0);
    let load_fn = f.finish(&mut b);
    b.export_func("load", load_fn);

    let wasm = b.finish();
    let (mut store, instance) = run_module(&wasm);
    let store_f = instance
        .get_typed_func::<(i32, i32), ()>(&mut store, "store")
        .unwrap();
    let load_f = instance
        .get_typed_func::<i32, i32>(&mut store, "load")
        .unwrap();

    store_f
        .call(&mut store, (0, 0xDEAD_BEEF_u32 as i32))
        .unwrap();
    assert_eq!(load_f.call(&mut store, 0).unwrap(), 0xDEAD_BEEF_u32 as i32);
}

#[test]
fn data_segment_initialized() {
    let mut b = ModuleBuilder::new();
    let mem = b.memory(1);
    b.export_memory("mem", mem);
    b.data_active(mem, 0, &[0x01, 0x02, 0x03, 0x04]);

    let mut f = b.func(&[], &[ValType::I32]);
    f.i32_const(0).i32_load(mem, 0);
    let idx = f.finish(&mut b);
    b.export_func("load_init", idx);

    let wasm = b.finish();
    let (mut store, instance) = run_module(&wasm);
    let load = instance
        .get_typed_func::<(), i32>(&mut store, "load_init")
        .unwrap();

    assert_eq!(load.call(&mut store, ()).unwrap(), 0x04030201); // little-endian
}

#[test]
fn start_function_runs() {
    let mut b = ModuleBuilder::new();
    let g = b.global_i32_mut(0);

    let mut f = b.func(&[], &[]);
    f.i32_const(99).global_set(g);
    let init = f.finish(&mut b);
    b.start(init);

    let mut f = b.func(&[], &[ValType::I32]);
    f.global_get(g);
    let get = f.finish(&mut b);
    b.export_func("get", get);

    let wasm = b.finish();
    let (mut store, instance) = run_module(&wasm);
    let get = instance
        .get_typed_func::<(), i32>(&mut store, "get")
        .unwrap();

    // Start function should have set global to 99
    assert_eq!(get.call(&mut store, ()).unwrap(), 99);
}

#[test]
fn call_between_functions() {
    let mut b = ModuleBuilder::new();

    // Helper: double(x) -> x * 2
    let mut f = b.func(&[ValType::I32], &[ValType::I32]);
    f.local_get(0).i32_const(2).i32_mul();
    let double = f.finish(&mut b);

    // Main: calls double(x) + double(y)
    let mut f = b.func(&[ValType::I32, ValType::I32], &[ValType::I32]);
    f.local_get(0).call(double);
    f.local_get(1).call(double);
    f.i32_add();
    let main = f.finish(&mut b);
    b.export_func("main", main);

    let wasm = b.finish();
    let (mut store, instance) = run_module(&wasm);
    let main = instance
        .get_typed_func::<(i32, i32), i32>(&mut store, "main")
        .unwrap();

    assert_eq!(main.call(&mut store, (3, 5)).unwrap(), 16); // 6 + 10
}

#[test]
fn local_tee() {
    let mut b = ModuleBuilder::new();
    // local.tee stores and leaves value on stack
    let mut f = b.func(&[ValType::I32], &[ValType::I32]);
    let x = f.local(ValType::I32);
    // tee stores param 0 into x, leaves it on stack, then add x (same value)
    f.local_get(0).local_tee(x).local_get(x).i32_add();
    let idx = f.finish(&mut b);
    b.export_func("double", idx);

    let wasm = b.finish();
    let (mut store, instance) = run_module(&wasm);
    let double = instance
        .get_typed_func::<i32, i32>(&mut store, "double")
        .unwrap();

    assert_eq!(double.call(&mut store, 7).unwrap(), 14);
}
