# Replace WAT string building with `covalence_wasm::build::ModuleBuilder`

## Goal
Replace hand-built WAT strings in `system_builder.rs` with the typed `covalence_wasm::build::ModuleBuilder` API for core module generation. Replace `wat` getter properties with `prettyprint()` methods.

## Data model changes in `system_builder.rs`

### Type string → `ValType`
- `FuncData.params/results/locals`: `Vec<String>` → `Vec<ValType>`
- `ImportedFunc.params/results`: `Vec<String>` → `Vec<ValType>`
- Add helper `parse_valtype(s: &str) -> PyResult<ValType>` ("i32" → `ValType::I32`, etc.)

### Instruction strings → typed enum
- `FuncData.body`: `Vec<String>` → `Vec<Insn>`
- New `Insn` enum covering the 16 instructions Python FuncBuilder exposes:
  `Call(usize)`, `LocalGet/Set/Tee(usize)`, `I32Const(i32)`, `I64Const(i64)`,
  `I32Add/Sub/Mul`, `I32Eq/Ne/Eqz`, `Drop`, `Return`, `Unreachable`

### Start calls → typed indices
- `ModuleData.start_calls`: `Vec<String>` → `Vec<usize>` (func indices)

## Build path changes in `system_builder.rs`

### Replace `generate_module_wat` → `build_module_bytes`

New method `build_module_bytes(&self, module_id: ModuleId) -> Vec<u8>`:
1. Create `covalence_wasm::build::ModuleBuilder`
2. Add imports via `b.import_func()`
3. Add functions: `b.func()` → replay typed `Insn` → `f.finish(&mut b)`
4. Handle start: if `start_calls` non-empty, create start func with calls → `b.start()`; if `explicit_start`, set directly
5. Handle exports: `NoOp` → create empty func + export; `Explicit` → export existing
6. `b.finish()` → binary bytes

### Update `generate_container_wat`

1. Call `build_module_bytes()` for the core module
2. Decompile via `covalence_wasm::wasm_to_wat()` to get WAT text
3. Embed decompiled WAT in the component WAT string (same as before)
4. Rest of component WAT generation unchanged

### Update `build_component_wat`

Same approach — build module bytes, decompile, embed in component WAT.

## Python wrapper changes

### `module_builder.rs` — FuncBuilder
All instruction methods push typed `Insn` instead of format strings:
- `f.call(target)` → `Insn::Call(idx)`
- `f.i32_add()` → `Insn::I32Add`
- `f.local_get(i)` → `Insn::LocalGet(i)`
- etc.

### `module_builder.rs` — ModuleBuilder
- `import_func()`: parse param/result strings to `Vec<ValType>`
- `func()`: parse param/result strings to `Vec<ValType>`
- `local()`: parse type string to `ValType`
- `attest()`: push `usize` to `start_calls` instead of format string
- `call()`: push `usize` to `start_calls` instead of format string

### `wat` getter → `prettyprint()` method (all three builders)
- `ModuleBuilder.prettyprint()`: `build_module_bytes()` → `wasm_to_wat()`
- `ContainerBuilder.prettyprint()`: `generate_container_wat()` (still WAT, unchanged)
- `ComponentBuilder.prettyprint()`: decompile built component bytes or delegate to `build_component_wat()`

### Build methods
- `ModuleBuilder.build()`: `build_module_bytes()` → `Module::from_bytes()`
- `ContainerBuilder.build()`: `generate_container_wat()` → `Container::from_wat()` (unchanged)
- `ComponentBuilder.build()`: `build_component_wat()` → `Component::from_wat()` (unchanged)

## Test changes

- `m.wat` → `m.prettyprint()` (6 occurrences in test_builders.py)
- `c.wat` → `c.prettyprint()` (1 occurrence in test_builders.py)
- Assertions against WAT content should still pass since `wasm_to_wat()` output contains the same instructions
- `test_component.py`: `c1.wat` is on `Component` (not a builder), unchanged

## Files modified
1. `system_builder.rs` — data model + build methods
2. `module_builder.rs` — FuncBuilder instructions, ModuleBuilder type parsing, `prettyprint()`
3. `container_builder.rs` — `prettyprint()` instead of `wat` getter
4. `component_builder.rs` — `prettyprint()` instead of `wat` getter
5. `tests/test_builders.py` — `.wat` → `.prettyprint()`
