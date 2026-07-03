//! Higher-level WASM core module builder.
//!
//! Wraps [`wasm_encoder`] with typed index handles and a fluent function
//! builder. Instructions are encoded directly into a byte buffer via
//! [`wasm_encoder::InstructionSink`] — no parallel `enum Insn` shadow
//! representation — and the full `wasm_encoder` crate is re-exported so
//! advanced callers can drop down when the typed surface is missing
//! something.

pub use wasm_encoder;
pub use wasm_encoder::{BlockType, InstructionSink, MemArg, ValType};

use wasm_encoder::{ConstExpr, EntityType, ExportKind, GlobalType, MemoryType};

// ---------------------------------------------------------------------------
// Typed indices
// ---------------------------------------------------------------------------

macro_rules! typed_idx {
    ($($(#[$attr:meta])* $name:ident),* $(,)?) => {
        $(
            $(#[$attr])*
            #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
            pub struct $name(pub u32);

            impl From<$name> for u32 {
                fn from(idx: $name) -> u32 {
                    idx.0
                }
            }
        )*
    };
}

typed_idx! {
    /// Index into the module's function index space.
    FuncIdx,
    /// Index into the module's memory index space.
    MemIdx,
    /// Index into the module's global index space.
    GlobalIdx,
    /// Index into the module's type index space.
    TypeIdx,
}

// ---------------------------------------------------------------------------
// ModuleBuilder
// ---------------------------------------------------------------------------

/// High-level WASM core module builder.
///
/// Sections are emitted in WASM-spec order on [`finish`](Self::finish);
/// empty sections are elided. Function and instruction encoding is
/// delegated to [`wasm_encoder`]; this type just tracks index spaces and
/// presents a fluent typed surface.
///
/// `Clone` exists so callers can snapshot an in-progress builder
/// without consuming it (e.g. to render WAT mid-construction).
/// Cloning duplicates the underlying section byte buffers; finishing a
/// clone does not affect the original.
#[derive(Clone)]
pub struct ModuleBuilder {
    types: wasm_encoder::TypeSection,
    imports: wasm_encoder::ImportSection,
    functions: wasm_encoder::FunctionSection,
    memories: wasm_encoder::MemorySection,
    globals: wasm_encoder::GlobalSection,
    exports: wasm_encoder::ExportSection,
    code: wasm_encoder::CodeSection,
    data: wasm_encoder::DataSection,
    // index-space cursors
    next_type: u32,
    next_func: u32,
    num_imports: u32,
    next_mem: u32,
    next_global: u32,
    num_data: u32,
    start: Option<u32>,
}

impl ModuleBuilder {
    pub fn new() -> Self {
        Self {
            types: wasm_encoder::TypeSection::new(),
            imports: wasm_encoder::ImportSection::new(),
            functions: wasm_encoder::FunctionSection::new(),
            memories: wasm_encoder::MemorySection::new(),
            globals: wasm_encoder::GlobalSection::new(),
            exports: wasm_encoder::ExportSection::new(),
            code: wasm_encoder::CodeSection::new(),
            data: wasm_encoder::DataSection::new(),
            next_type: 0,
            next_func: 0,
            num_imports: 0,
            next_mem: 0,
            next_global: 0,
            num_data: 0,
            start: None,
        }
    }

    // -- Types & imports --

    fn push_function_type(&mut self, params: &[ValType], results: &[ValType]) -> u32 {
        let idx = self.next_type;
        self.next_type += 1;
        self.types
            .ty()
            .function(params.iter().copied(), results.iter().copied());
        idx
    }

    /// Import a function. Returns its index in the (shared) function
    /// index space, where imports come before locally-defined functions.
    pub fn import_func(
        &mut self,
        module: &str,
        name: &str,
        params: &[ValType],
        results: &[ValType],
    ) -> FuncIdx {
        let type_idx = self.push_function_type(params, results);
        self.imports
            .import(module, name, EntityType::Function(type_idx));
        let func_idx = self.next_func;
        self.next_func += 1;
        self.num_imports += 1;
        FuncIdx(func_idx)
    }

    // -- Memories --

    /// Declare a memory with the given initial page count.
    pub fn memory(&mut self, initial_pages: u32) -> MemIdx {
        self.memory_with(initial_pages, None)
    }

    /// Declare a memory with both minimum and maximum page counts.
    pub fn memory_with(&mut self, initial_pages: u32, maximum_pages: Option<u32>) -> MemIdx {
        self.memories.memory(MemoryType {
            minimum: initial_pages as u64,
            maximum: maximum_pages.map(|m| m as u64),
            memory64: false,
            shared: false,
            page_size_log2: None,
        });
        let idx = self.next_mem;
        self.next_mem += 1;
        MemIdx(idx)
    }

    // -- Globals --

    fn push_global(&mut self, val_type: ValType, mutable: bool, init: &ConstExpr) -> GlobalIdx {
        self.globals.global(
            GlobalType {
                val_type,
                mutable,
                shared: false,
            },
            init,
        );
        let idx = self.next_global;
        self.next_global += 1;
        GlobalIdx(idx)
    }

    /// Declare an immutable i32 global.
    pub fn global_i32(&mut self, init: i32) -> GlobalIdx {
        self.push_global(ValType::I32, false, &ConstExpr::i32_const(init))
    }

    /// Declare a mutable i32 global.
    pub fn global_i32_mut(&mut self, init: i32) -> GlobalIdx {
        self.push_global(ValType::I32, true, &ConstExpr::i32_const(init))
    }

    /// Declare an immutable i64 global.
    pub fn global_i64(&mut self, init: i64) -> GlobalIdx {
        self.push_global(ValType::I64, false, &ConstExpr::i64_const(init))
    }

    /// Declare a mutable i64 global.
    pub fn global_i64_mut(&mut self, init: i64) -> GlobalIdx {
        self.push_global(ValType::I64, true, &ConstExpr::i64_const(init))
    }

    // -- Functions --

    /// Begin building a function body. Call [`FuncBody::finish`] to register it.
    pub fn func(&mut self, params: &[ValType], results: &[ValType]) -> FuncBody {
        let _type_idx = self.push_function_type(params, results);
        let func_idx = FuncIdx(self.next_func);
        self.next_func += 1;
        self.functions.function(self.next_type - 1);

        FuncBody {
            locals: Vec::new(),
            insn_bytes: Vec::new(),
            func_idx,
            num_params: params.len() as u32,
        }
    }

    // -- Exports --

    /// Export a function by name.
    pub fn export_func(&mut self, name: &str, func: FuncIdx) {
        self.exports.export(name, ExportKind::Func, func.0);
    }

    /// Export a memory by name.
    pub fn export_memory(&mut self, name: &str, mem: MemIdx) {
        self.exports.export(name, ExportKind::Memory, mem.0);
    }

    /// Export a global by name.
    pub fn export_global(&mut self, name: &str, global: GlobalIdx) {
        self.exports.export(name, ExportKind::Global, global.0);
    }

    // -- Data --

    /// Active data segment: initialize `mem` at `offset` with `bytes`.
    pub fn data_active(&mut self, mem: MemIdx, offset: u32, bytes: &[u8]) {
        self.data.active(
            mem.0,
            &ConstExpr::i32_const(offset as i32),
            bytes.iter().copied(),
        );
        self.num_data += 1;
    }

    // -- Start --

    /// Set the module start function.
    pub fn start(&mut self, func: FuncIdx) {
        self.start = Some(func.0);
    }

    // -- Encode --

    /// Assemble all sections into WASM binary bytes.
    ///
    /// Sections are emitted in the order required by the WASM core spec
    /// (type, import, function, memory, global, export, start, code,
    /// data); empty sections are elided.
    pub fn finish(self) -> Vec<u8> {
        let mut module = wasm_encoder::Module::new();

        if self.next_type > 0 {
            module.section(&self.types);
        }
        if self.num_imports > 0 {
            module.section(&self.imports);
        }
        if self.next_func > self.num_imports {
            module.section(&self.functions);
        }
        if self.next_mem > 0 {
            module.section(&self.memories);
        }
        if self.next_global > 0 {
            module.section(&self.globals);
        }
        // Always emit exports for parity with prior behaviour even when
        // there are none — empty export section is cheap and matches
        // every test fixture in tree.
        module.section(&self.exports);
        if let Some(function_index) = self.start {
            module.section(&wasm_encoder::StartSection { function_index });
        }
        if self.next_func > self.num_imports {
            module.section(&self.code);
        }
        if self.num_data > 0 {
            module.section(&self.data);
        }

        module.finish()
    }

    /// Like [`finish`](Self::finish), but additionally validate the
    /// encoded bytes with [`wasmparser`]. Returns the bytes on success or
    /// a [`crate::WasmError::InvalidModule`] describing the validation
    /// failure.
    pub fn finish_validated(self) -> Result<Vec<u8>, crate::WasmError> {
        let bytes = self.finish();
        wasmparser::Validator::new()
            .validate_all(&bytes)
            .map_err(|e| crate::WasmError::InvalidModule(e.to_string()))?;
        Ok(bytes)
    }
}

impl Default for ModuleBuilder {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// FuncBody
// ---------------------------------------------------------------------------

/// A function body being built. Accumulates locals plus a raw
/// instruction byte buffer (encoded directly via [`InstructionSink`]),
/// then registers the assembled [`wasm_encoder::Function`] on
/// [`finish`](Self::finish).
///
/// `Clone` exists for the same reason as on [`ModuleBuilder`]:
/// snapshotting an in-progress body. *Each clone still finishes into
/// the same function-index slot* the original was allocated for —
/// finishing a clone twice into the same builder would emit two code
/// entries for one slot, so don't.
#[derive(Clone)]
pub struct FuncBody {
    locals: Vec<ValType>,
    insn_bytes: Vec<u8>,
    func_idx: FuncIdx,
    num_params: u32,
}

impl FuncBody {
    /// Declare a local variable. Returns its local index (params come first).
    pub fn local(&mut self, ty: ValType) -> u32 {
        let idx = self.num_params + self.locals.len() as u32;
        self.locals.push(ty);
        idx
    }

    /// Get the function index that will be assigned to this function.
    pub fn idx(&self) -> FuncIdx {
        self.func_idx
    }

    /// Direct access to the underlying [`InstructionSink`] for emitting
    /// instructions outside the typed convenience surface (anything
    /// `wasm_encoder` supports — SIMD, atomics, GC, etc.).
    pub fn insns(&mut self) -> InstructionSink<'_> {
        InstructionSink::new(&mut self.insn_bytes)
    }

    /// Finish the function body and register it with the builder.
    /// Returns the function's index.
    pub fn finish(self, builder: &mut ModuleBuilder) -> FuncIdx {
        let mut local_groups: Vec<(u32, ValType)> = Vec::new();
        for &ty in &self.locals {
            if let Some(last) = local_groups.last_mut() {
                if last.1 == ty {
                    last.0 += 1;
                    continue;
                }
            }
            local_groups.push((1, ty));
        }

        let mut func = wasm_encoder::Function::new(local_groups);
        func.raw(self.insn_bytes);
        // Terminal End — the function-body end opcode the spec requires.
        func.instructions().end();

        builder.code.function(&func);
        self.func_idx
    }
}

// -- Instruction passthroughs --
//
// Each delegates to the underlying `InstructionSink` and returns `&mut
// Self` to keep the fluent chain on `FuncBody`. The macro handles the
// raw-u32-arg (or no-arg) shape; the typed-wrapper variants
// (`FuncIdx`, `MemIdx`, `GlobalIdx`, memargs) are spelled out below.

macro_rules! insn_passthrough {
    ($($(#[$attr:meta])* $name:ident($($arg:ident: $ty:ty),*) ),* $(,)?) => {
        impl FuncBody {
            $(
                $(#[$attr])*
                pub fn $name(&mut self, $($arg: $ty),*) -> &mut Self {
                    InstructionSink::new(&mut self.insn_bytes).$name($($arg),*);
                    self
                }
            )*
        }
    };
}

insn_passthrough! {
    // -- Control flow --
    unreachable(),
    nop(),
    block(ty: BlockType),
    loop_(ty: BlockType),
    if_(ty: BlockType),
    else_(),
    end(),
    br(depth: u32),
    br_if(depth: u32),
    return_(),
    drop(),

    // -- Locals --
    local_get(idx: u32),
    local_set(idx: u32),
    local_tee(idx: u32),

    // -- i32 constants & arithmetic --
    i32_const(val: i32),
    i32_add(),
    i32_sub(),
    i32_mul(),
    i32_div_s(),
    i32_div_u(),
    i32_rem_s(),
    i32_rem_u(),
    i32_and(),
    i32_or(),
    i32_xor(),
    i32_shl(),
    i32_shr_s(),
    i32_shr_u(),
    i32_rotl(),
    i32_rotr(),
    i32_eqz(),
    i32_eq(),
    i32_ne(),
    i32_lt_s(),
    i32_lt_u(),
    i32_gt_s(),
    i32_gt_u(),
    i32_le_s(),
    i32_le_u(),
    i32_ge_s(),
    i32_ge_u(),

    // -- i64 constants & arithmetic --
    i64_const(val: i64),
    i64_add(),
    i64_sub(),
    i64_mul(),
    i64_div_s(),
    i64_div_u(),
    i64_rem_s(),
    i64_rem_u(),
    i64_and(),
    i64_or(),
    i64_xor(),
    i64_shl(),
    i64_shr_s(),
    i64_shr_u(),
    i64_eqz(),
    i64_eq(),
    i64_ne(),
    i64_lt_s(),
    i64_lt_u(),
    i64_gt_s(),
    i64_gt_u(),
    i64_le_s(),
    i64_le_u(),
    i64_ge_s(),
    i64_ge_u(),

    // -- Conversions --
    i32_wrap_i64(),
    i64_extend_i32_s(),
    i64_extend_i32_u(),
}

// -- Typed-wrapper passthroughs --

impl FuncBody {
    pub fn call(&mut self, func: FuncIdx) -> &mut Self {
        self.insns().call(func.0);
        self
    }

    pub fn global_get(&mut self, g: GlobalIdx) -> &mut Self {
        self.insns().global_get(g.0);
        self
    }

    pub fn global_set(&mut self, g: GlobalIdx) -> &mut Self {
        self.insns().global_set(g.0);
        self
    }

    /// `br_table` with a label vector and a default depth. `wasm_encoder`
    /// requires an [`ExactSizeIterator`], which a `&[u32]` slice
    /// satisfies cleanly.
    pub fn br_table(&mut self, labels: &[u32], default: u32) -> &mut Self {
        self.insns().br_table(labels.iter().copied(), default);
        self
    }

    pub fn memory_grow(&mut self, mem: MemIdx) -> &mut Self {
        self.insns().memory_grow(mem.0);
        self
    }

    pub fn memory_size(&mut self, mem: MemIdx) -> &mut Self {
        self.insns().memory_size(mem.0);
        self
    }

    // -- i32 memory ops (4-byte alignment for full-width; 0 for byte ops) --

    pub fn i32_load(&mut self, mem: MemIdx, offset: u32) -> &mut Self {
        self.insns().i32_load(memarg(mem, offset, 2));
        self
    }

    pub fn i32_store(&mut self, mem: MemIdx, offset: u32) -> &mut Self {
        self.insns().i32_store(memarg(mem, offset, 2));
        self
    }

    pub fn i32_load8_s(&mut self, mem: MemIdx, offset: u32) -> &mut Self {
        self.insns().i32_load8_s(memarg(mem, offset, 0));
        self
    }

    pub fn i32_load8_u(&mut self, mem: MemIdx, offset: u32) -> &mut Self {
        self.insns().i32_load8_u(memarg(mem, offset, 0));
        self
    }

    pub fn i32_load16_s(&mut self, mem: MemIdx, offset: u32) -> &mut Self {
        self.insns().i32_load16_s(memarg(mem, offset, 1));
        self
    }

    pub fn i32_load16_u(&mut self, mem: MemIdx, offset: u32) -> &mut Self {
        self.insns().i32_load16_u(memarg(mem, offset, 1));
        self
    }

    pub fn i32_store8(&mut self, mem: MemIdx, offset: u32) -> &mut Self {
        self.insns().i32_store8(memarg(mem, offset, 0));
        self
    }

    pub fn i32_store16(&mut self, mem: MemIdx, offset: u32) -> &mut Self {
        self.insns().i32_store16(memarg(mem, offset, 1));
        self
    }

    // -- i64 memory ops --

    pub fn i64_load(&mut self, mem: MemIdx, offset: u32) -> &mut Self {
        self.insns().i64_load(memarg(mem, offset, 3));
        self
    }

    pub fn i64_store(&mut self, mem: MemIdx, offset: u32) -> &mut Self {
        self.insns().i64_store(memarg(mem, offset, 3));
        self
    }

    pub fn i64_load8_u(&mut self, mem: MemIdx, offset: u32) -> &mut Self {
        self.insns().i64_load8_u(memarg(mem, offset, 0));
        self
    }

    pub fn i64_store8(&mut self, mem: MemIdx, offset: u32) -> &mut Self {
        self.insns().i64_store8(memarg(mem, offset, 0));
        self
    }
}

fn memarg(mem: MemIdx, offset: u32, align: u32) -> MemArg {
    MemArg {
        offset: offset as u64,
        align,
        memory_index: mem.0,
    }
}

// -- Compatibility aliases for Rust-keyword-collision spellings.
//
// `drop` and `return_` were exposed as `drop_` / `return_` in the
// pre-rename API; map both to keep the existing test surface working
// without forcing all callers to update at once.

impl FuncBody {
    pub fn drop_(&mut self) -> &mut Self {
        self.drop()
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn trivial_module_builds_and_decompiles() {
        let mut b = ModuleBuilder::new();
        let mem = b.memory(1);
        b.export_memory("memory", mem);

        let mut f = b.func(&[ValType::I32, ValType::I32], &[ValType::I32]);
        f.local_get(0).local_get(1).i32_add();
        let idx = f.finish(&mut b);
        b.export_func("add", idx);

        let wasm = b.finish();
        let wat = crate::wasm_to_wat(&wasm).expect("decompile");
        assert!(wat.contains("func"), "WAT should contain func: {wat}");
        assert!(wat.contains("i32.add"), "WAT should contain i32.add: {wat}");
    }

    #[test]
    fn multi_memory_and_globals() {
        let mut b = ModuleBuilder::new();
        let m0 = b.memory(1);
        let m1 = b.memory(2);
        let g0 = b.global_i32(42);
        let g1 = b.global_i32_mut(0);

        let mut f = b.func(&[], &[ValType::I32]);
        f.global_get(g0).global_get(g1).i32_add();
        let idx = f.finish(&mut b);
        b.export_func("test", idx);
        b.export_memory("m0", m0);
        b.export_memory("m1", m1);

        let wasm = b.finish();
        let wat = crate::wasm_to_wat(&wasm).expect("decompile");
        assert!(
            wat.contains("memory") && wat.contains("global"),
            "WAT should have memories and globals: {wat}"
        );
    }

    #[test]
    fn control_flow_builds() {
        let mut b = ModuleBuilder::new();
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
        b.export_func("count_down", idx);

        let wasm = b.finish();
        let wat = crate::wasm_to_wat(&wasm).expect("decompile");
        assert!(wat.contains("loop"), "WAT should contain loop: {wat}");
        assert!(wat.contains("br_if"), "WAT should contain br_if: {wat}");
    }

    #[test]
    fn import_func_works() {
        let mut b = ModuleBuilder::new();
        let log = b.import_func("env", "log", &[ValType::I32], &[]);

        let mut f = b.func(&[], &[]);
        f.i32_const(42).call(log);
        let idx = f.finish(&mut b);
        b.export_func("main", idx);

        let wasm = b.finish();
        let wat = crate::wasm_to_wat(&wasm).expect("decompile");
        assert!(wat.contains("import"), "WAT should contain import: {wat}");
    }

    #[test]
    fn data_segment() {
        let mut b = ModuleBuilder::new();
        let mem = b.memory(1);
        b.export_memory("memory", mem);
        b.data_active(mem, 0, b"hello");

        let mut f = b.func(&[], &[ValType::I32]);
        f.i32_const(0).i32_load(mem, 0);
        let idx = f.finish(&mut b);
        b.export_func("load", idx);

        let wasm = b.finish();
        let wat = crate::wasm_to_wat(&wasm).expect("decompile");
        assert!(wat.contains("data"), "WAT should contain data: {wat}");
    }

    #[test]
    fn locals_have_correct_indices() {
        let mut b = ModuleBuilder::new();
        let mut f = b.func(&[ValType::I32, ValType::I32], &[ValType::I32]);
        let x = f.local(ValType::I32);
        let y = f.local(ValType::I32);
        assert_eq!(x, 2);
        assert_eq!(y, 3);
        f.local_get(0).local_get(1).i32_add().local_set(x);
        f.local_get(x).i32_const(2).i32_mul().local_set(y);
        f.local_get(y);
        let idx = f.finish(&mut b);
        b.export_func("calc", idx);

        let wasm = b.finish();
        let wat = crate::wasm_to_wat(&wasm).expect("decompile");
        assert!(wat.contains("local"), "WAT should declare locals: {wat}");
    }

    #[test]
    fn func_idx_returns_correct_index() {
        let mut b = ModuleBuilder::new();
        let f = b.func(&[], &[]);
        assert_eq!(f.idx(), FuncIdx(0));
        f.finish(&mut b);

        let f = b.func(&[], &[]);
        assert_eq!(f.idx(), FuncIdx(1));
        f.finish(&mut b);
    }

    #[test]
    fn import_and_local_funcs_share_index_space() {
        let mut b = ModuleBuilder::new();
        let imp = b.import_func("env", "log", &[ValType::I32], &[]);
        assert_eq!(imp, FuncIdx(0));

        let f = b.func(&[], &[]);
        assert_eq!(f.idx(), FuncIdx(1));
        f.finish(&mut b);

        let wasm = b.finish();
        crate::wasm_to_wat(&wasm).expect("valid module");
    }

    #[test]
    fn start_function() {
        let mut b = ModuleBuilder::new();
        let g = b.global_i32_mut(0);

        let mut f = b.func(&[], &[]);
        f.i32_const(42).global_set(g);
        let idx = f.finish(&mut b);
        b.start(idx);

        let mut f = b.func(&[], &[ValType::I32]);
        f.global_get(g);
        let get = f.finish(&mut b);
        b.export_func("get", get);

        let wasm = b.finish();
        let wat = crate::wasm_to_wat(&wasm).expect("decompile");
        assert!(
            wat.contains("start"),
            "WAT should have start section: {wat}"
        );
    }

    #[test]
    fn if_else_builds() {
        let mut b = ModuleBuilder::new();
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
        let wat = crate::wasm_to_wat(&wasm).expect("decompile");
        assert!(wat.contains("if"), "WAT should contain if: {wat}");
        assert!(wat.contains("else"), "WAT should contain else: {wat}");
    }

    #[test]
    fn empty_function() {
        let mut b = ModuleBuilder::new();
        let f = b.func(&[], &[]);
        let idx = f.finish(&mut b);
        b.export_func("noop", idx);

        let wasm = b.finish();
        crate::wasm_to_wat(&wasm).expect("valid module with empty func");
    }

    #[test]
    fn memory_ops() {
        let mut b = ModuleBuilder::new();
        let mem = b.memory(1);
        b.export_memory("mem", mem);

        let mut f = b.func(&[ValType::I32, ValType::I32], &[]);
        f.local_get(0).local_get(1).i32_store(mem, 0);
        let store = f.finish(&mut b);
        b.export_func("store", store);

        let mut f = b.func(&[ValType::I32], &[ValType::I32]);
        f.local_get(0).i32_load(mem, 0);
        let load = f.finish(&mut b);
        b.export_func("load", load);

        let mut f = b.func(&[ValType::I32, ValType::I32], &[]);
        f.local_get(0).local_get(1).i32_store8(mem, 0);
        let store8 = f.finish(&mut b);
        b.export_func("store8", store8);

        let mut f = b.func(&[ValType::I32], &[ValType::I32]);
        f.local_get(0).i32_load8_u(mem, 0);
        let load8u = f.finish(&mut b);
        b.export_func("load8u", load8u);

        let wasm = b.finish();
        let wat = crate::wasm_to_wat(&wasm).expect("decompile");
        assert!(wat.contains("i32.store"), "should have i32.store: {wat}");
        assert!(wat.contains("i32.load"), "should have i32.load: {wat}");
    }

    #[test]
    fn i64_round_trip() {
        let mut b = ModuleBuilder::new();
        let g = b.global_i64_mut(0);
        let mut f = b.func(&[ValType::I64], &[ValType::I64]);
        f.local_get(0)
            .i64_const(1)
            .i64_add()
            .global_set(g)
            .global_get(g);
        let idx = f.finish(&mut b);
        b.export_func("inc", idx);

        let wasm = b.finish_validated().expect("valid module");
        let wat = crate::wasm_to_wat(&wasm).expect("decompile");
        assert!(wat.contains("i64.add"), "expected i64.add: {wat}");
    }

    #[test]
    fn finish_validated_catches_malformed() {
        // Construct a function whose body underflows: pop two without
        // pushing anything first.
        let mut b = ModuleBuilder::new();
        let mut f = b.func(&[], &[ValType::I32]);
        // No operands pushed → i32_add traps the validator.
        f.i32_add();
        f.finish(&mut b);

        let err = b.finish_validated().expect_err("should fail validation");
        assert!(
            matches!(err, crate::WasmError::InvalidModule(_)),
            "wrong error variant: {err:?}"
        );
    }

    #[test]
    fn insns_escape_hatch_works() {
        let mut b = ModuleBuilder::new();
        let mut f = b.func(&[ValType::I32], &[ValType::I32]);
        // Use the raw InstructionSink directly.
        f.insns().local_get(0).i32_const(7).i32_xor();
        let idx = f.finish(&mut b);
        b.export_func("xor7", idx);
        let wasm = b.finish_validated().expect("valid module");
        let wat = crate::wasm_to_wat(&wasm).expect("decompile");
        assert!(wat.contains("i32.xor"), "WAT should contain i32.xor: {wat}");
    }
}
