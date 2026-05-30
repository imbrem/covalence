//! Higher-level WASM core module builder.
//!
//! Wraps [`wasm_encoder`] with typed index handles and convenience methods
//! for the instruction set needed by generated checkers. The full
//! `wasm_encoder` crate is re-exported for advanced use.

pub use wasm_encoder;
pub use wasm_encoder::{BlockType, MemArg, ValType};

// ---------------------------------------------------------------------------
// Typed indices
// ---------------------------------------------------------------------------

/// Index into the module's function index space.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FuncIdx(pub u32);

/// Index into the module's memory index space.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MemIdx(pub u32);

/// Index into the module's global index space.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct GlobalIdx(pub u32);

/// Index into the module's type index space.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TypeIdx(pub u32);

// ---------------------------------------------------------------------------
// ModuleBuilder
// ---------------------------------------------------------------------------

/// High-level WASM core module builder.
pub struct ModuleBuilder {
    types: wasm_encoder::TypeSection,
    imports: wasm_encoder::ImportSection,
    functions: wasm_encoder::FunctionSection,
    memories: wasm_encoder::MemorySection,
    globals: wasm_encoder::GlobalSection,
    exports: wasm_encoder::ExportSection,
    code: wasm_encoder::CodeSection,
    data: wasm_encoder::DataSection,
    // tracking
    next_type: u32,
    next_func: u32,
    num_imports: u32,
    next_mem: u32,
    next_global: u32,
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
            start: None,
        }
    }

    // -- Types & imports --

    /// Import a function. Returns its index in the function index space.
    pub fn import_func(
        &mut self,
        module: &str,
        name: &str,
        params: &[ValType],
        results: &[ValType],
    ) -> FuncIdx {
        let type_idx = self.next_type;
        self.next_type += 1;
        self.types
            .ty()
            .function(params.iter().copied(), results.iter().copied());
        self.imports
            .import(module, name, wasm_encoder::EntityType::Function(type_idx));
        let func_idx = self.next_func;
        self.next_func += 1;
        self.num_imports += 1;
        FuncIdx(func_idx)
    }

    // -- Memories --

    /// Declare a memory with the given initial page count.
    pub fn memory(&mut self, initial_pages: u32) -> MemIdx {
        self.memories.memory(wasm_encoder::MemoryType {
            minimum: initial_pages as u64,
            maximum: None,
            memory64: false,
            shared: false,
            page_size_log2: None,
        });
        let idx = self.next_mem;
        self.next_mem += 1;
        MemIdx(idx)
    }

    // -- Globals --

    /// Declare an immutable i32 global.
    pub fn global_i32(&mut self, init: i32) -> GlobalIdx {
        self.globals.global(
            wasm_encoder::GlobalType {
                val_type: ValType::I32,
                mutable: false,
                shared: false,
            },
            &wasm_encoder::ConstExpr::i32_const(init),
        );
        let idx = self.next_global;
        self.next_global += 1;
        GlobalIdx(idx)
    }

    /// Declare a mutable i32 global.
    pub fn global_i32_mut(&mut self, init: i32) -> GlobalIdx {
        self.globals.global(
            wasm_encoder::GlobalType {
                val_type: ValType::I32,
                mutable: true,
                shared: false,
            },
            &wasm_encoder::ConstExpr::i32_const(init),
        );
        let idx = self.next_global;
        self.next_global += 1;
        GlobalIdx(idx)
    }

    // -- Functions --

    /// Begin building a function body. Call [`FuncBody::finish`] to register it.
    pub fn func(&mut self, params: &[ValType], results: &[ValType]) -> FuncBody {
        let type_idx = self.next_type;
        self.next_type += 1;
        self.types
            .ty()
            .function(params.iter().copied(), results.iter().copied());

        let func_idx = FuncIdx(self.next_func);
        self.next_func += 1;
        self.functions.function(type_idx);

        FuncBody {
            locals: Vec::new(),
            insns: Vec::new(),
            func_idx,
            num_params: params.len() as u32,
        }
    }

    // -- Exports --

    /// Export a function by name.
    pub fn export_func(&mut self, name: &str, func: FuncIdx) {
        self.exports
            .export(name, wasm_encoder::ExportKind::Func, func.0);
    }

    /// Export a memory by name.
    pub fn export_memory(&mut self, name: &str, mem: MemIdx) {
        self.exports
            .export(name, wasm_encoder::ExportKind::Memory, mem.0);
    }

    // -- Data --

    /// Active data segment: initialize `mem` at `offset` with `bytes`.
    pub fn data_active(&mut self, mem: MemIdx, offset: u32, bytes: &[u8]) {
        self.data.active(
            mem.0,
            &wasm_encoder::ConstExpr::i32_const(offset as i32),
            bytes.iter().copied(),
        );
    }

    // -- Start --

    /// Set the module start function.
    pub fn start(&mut self, func: FuncIdx) {
        self.start = Some(func.0);
    }

    // -- Encode --

    /// Assemble all sections into WASM binary bytes.
    pub fn finish(self) -> Vec<u8> {
        let mut module = wasm_encoder::Module::new();

        module.section(&self.types);

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

        module.section(&self.exports);

        if let Some(start_idx) = self.start {
            module.section(&wasm_encoder::StartSection {
                function_index: start_idx,
            });
        }

        if self.next_func > self.num_imports {
            module.section(&self.code);
        }

        // Always emit data section if there are data segments.
        module.section(&self.data);

        module.finish()
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

/// A function body being built. Accumulates locals and instructions,
/// then assembles the final `wasm_encoder::Function` on [`finish`](FuncBody::finish).
pub struct FuncBody {
    locals: Vec<ValType>,
    insns: Vec<Insn>,
    func_idx: FuncIdx,
    num_params: u32,
}

/// Stored instruction — either a thin enum variant or an i32/u32 payload.
/// We avoid storing borrowed `wasm_encoder::Instruction` values by replaying
/// them in [`FuncBody::finish`].
enum Insn {
    I32Const(i32),
    LocalGet(u32),
    LocalSet(u32),
    LocalTee(u32),
    GlobalGet(u32),
    GlobalSet(u32),
    I32Load(MemArg),
    I32Store(MemArg),
    I32Load8U(MemArg),
    I32Store8(MemArg),
    I32Add,
    I32Sub,
    I32Mul,
    I32Eq,
    I32Ne,
    I32LtS,
    I32GtS,
    I32LeS,
    I32GeS,
    I32Eqz,
    I32And,
    I32Or,
    I32Shl,
    I32ShrS,
    Call(u32),
    Block(BlockType),
    Loop(BlockType),
    If(BlockType),
    Else,
    End,
    Br(u32),
    BrIf(u32),
    Return,
    Unreachable,
    Drop,
    MemoryGrow(u32),
    MemorySize(u32),
    Nop,
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

    // -- Instruction helpers --

    pub fn i32_const(&mut self, val: i32) -> &mut Self {
        self.insns.push(Insn::I32Const(val));
        self
    }

    pub fn local_get(&mut self, idx: u32) -> &mut Self {
        self.insns.push(Insn::LocalGet(idx));
        self
    }

    pub fn local_set(&mut self, idx: u32) -> &mut Self {
        self.insns.push(Insn::LocalSet(idx));
        self
    }

    pub fn local_tee(&mut self, idx: u32) -> &mut Self {
        self.insns.push(Insn::LocalTee(idx));
        self
    }

    pub fn global_get(&mut self, idx: GlobalIdx) -> &mut Self {
        self.insns.push(Insn::GlobalGet(idx.0));
        self
    }

    pub fn global_set(&mut self, idx: GlobalIdx) -> &mut Self {
        self.insns.push(Insn::GlobalSet(idx.0));
        self
    }

    pub fn i32_load(&mut self, mem: MemIdx, offset: u32) -> &mut Self {
        self.insns.push(Insn::I32Load(MemArg {
            offset: offset as u64,
            align: 2,
            memory_index: mem.0,
        }));
        self
    }

    pub fn i32_store(&mut self, mem: MemIdx, offset: u32) -> &mut Self {
        self.insns.push(Insn::I32Store(MemArg {
            offset: offset as u64,
            align: 2,
            memory_index: mem.0,
        }));
        self
    }

    pub fn i32_load8_u(&mut self, mem: MemIdx, offset: u32) -> &mut Self {
        self.insns.push(Insn::I32Load8U(MemArg {
            offset: offset as u64,
            align: 0,
            memory_index: mem.0,
        }));
        self
    }

    pub fn i32_store8(&mut self, mem: MemIdx, offset: u32) -> &mut Self {
        self.insns.push(Insn::I32Store8(MemArg {
            offset: offset as u64,
            align: 0,
            memory_index: mem.0,
        }));
        self
    }

    pub fn i32_add(&mut self) -> &mut Self {
        self.insns.push(Insn::I32Add);
        self
    }

    pub fn i32_sub(&mut self) -> &mut Self {
        self.insns.push(Insn::I32Sub);
        self
    }

    pub fn i32_mul(&mut self) -> &mut Self {
        self.insns.push(Insn::I32Mul);
        self
    }

    pub fn i32_eq(&mut self) -> &mut Self {
        self.insns.push(Insn::I32Eq);
        self
    }

    pub fn i32_ne(&mut self) -> &mut Self {
        self.insns.push(Insn::I32Ne);
        self
    }

    pub fn i32_lt_s(&mut self) -> &mut Self {
        self.insns.push(Insn::I32LtS);
        self
    }

    pub fn i32_gt_s(&mut self) -> &mut Self {
        self.insns.push(Insn::I32GtS);
        self
    }

    pub fn i32_le_s(&mut self) -> &mut Self {
        self.insns.push(Insn::I32LeS);
        self
    }

    pub fn i32_ge_s(&mut self) -> &mut Self {
        self.insns.push(Insn::I32GeS);
        self
    }

    pub fn i32_eqz(&mut self) -> &mut Self {
        self.insns.push(Insn::I32Eqz);
        self
    }

    pub fn i32_and(&mut self) -> &mut Self {
        self.insns.push(Insn::I32And);
        self
    }

    pub fn i32_or(&mut self) -> &mut Self {
        self.insns.push(Insn::I32Or);
        self
    }

    pub fn i32_shl(&mut self) -> &mut Self {
        self.insns.push(Insn::I32Shl);
        self
    }

    pub fn i32_shr_s(&mut self) -> &mut Self {
        self.insns.push(Insn::I32ShrS);
        self
    }

    pub fn call(&mut self, func: FuncIdx) -> &mut Self {
        self.insns.push(Insn::Call(func.0));
        self
    }

    pub fn block(&mut self, ty: BlockType) -> &mut Self {
        self.insns.push(Insn::Block(ty));
        self
    }

    pub fn loop_(&mut self, ty: BlockType) -> &mut Self {
        self.insns.push(Insn::Loop(ty));
        self
    }

    pub fn if_(&mut self, ty: BlockType) -> &mut Self {
        self.insns.push(Insn::If(ty));
        self
    }

    pub fn else_(&mut self) -> &mut Self {
        self.insns.push(Insn::Else);
        self
    }

    pub fn end(&mut self) -> &mut Self {
        self.insns.push(Insn::End);
        self
    }

    pub fn br(&mut self, depth: u32) -> &mut Self {
        self.insns.push(Insn::Br(depth));
        self
    }

    pub fn br_if(&mut self, depth: u32) -> &mut Self {
        self.insns.push(Insn::BrIf(depth));
        self
    }

    pub fn return_(&mut self) -> &mut Self {
        self.insns.push(Insn::Return);
        self
    }

    pub fn unreachable(&mut self) -> &mut Self {
        self.insns.push(Insn::Unreachable);
        self
    }

    pub fn drop_(&mut self) -> &mut Self {
        self.insns.push(Insn::Drop);
        self
    }

    pub fn memory_grow(&mut self, mem: MemIdx) -> &mut Self {
        self.insns.push(Insn::MemoryGrow(mem.0));
        self
    }

    pub fn memory_size(&mut self, mem: MemIdx) -> &mut Self {
        self.insns.push(Insn::MemorySize(mem.0));
        self
    }

    pub fn nop(&mut self) -> &mut Self {
        self.insns.push(Insn::Nop);
        self
    }

    /// Finish the function body and register it with the builder.
    /// Returns the function's index.
    pub fn finish(self, builder: &mut ModuleBuilder) -> FuncIdx {
        use wasm_encoder::Instruction as I;

        // Collect locals as (count, type) pairs with run-length encoding.
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
        for insn in &self.insns {
            let i = match *insn {
                Insn::I32Const(v) => I::I32Const(v),
                Insn::LocalGet(v) => I::LocalGet(v),
                Insn::LocalSet(v) => I::LocalSet(v),
                Insn::LocalTee(v) => I::LocalTee(v),
                Insn::GlobalGet(v) => I::GlobalGet(v),
                Insn::GlobalSet(v) => I::GlobalSet(v),
                Insn::I32Load(m) => I::I32Load(m),
                Insn::I32Store(m) => I::I32Store(m),
                Insn::I32Load8U(m) => I::I32Load8U(m),
                Insn::I32Store8(m) => I::I32Store8(m),
                Insn::I32Add => I::I32Add,
                Insn::I32Sub => I::I32Sub,
                Insn::I32Mul => I::I32Mul,
                Insn::I32Eq => I::I32Eq,
                Insn::I32Ne => I::I32Ne,
                Insn::I32LtS => I::I32LtS,
                Insn::I32GtS => I::I32GtS,
                Insn::I32LeS => I::I32LeS,
                Insn::I32GeS => I::I32GeS,
                Insn::I32Eqz => I::I32Eqz,
                Insn::I32And => I::I32And,
                Insn::I32Or => I::I32Or,
                Insn::I32Shl => I::I32Shl,
                Insn::I32ShrS => I::I32ShrS,
                Insn::Call(v) => I::Call(v),
                Insn::Block(ty) => I::Block(ty),
                Insn::Loop(ty) => I::Loop(ty),
                Insn::If(ty) => I::If(ty),
                Insn::Else => I::Else,
                Insn::End => I::End,
                Insn::Br(d) => I::Br(d),
                Insn::BrIf(d) => I::BrIf(d),
                Insn::Return => I::Return,
                Insn::Unreachable => I::Unreachable,
                Insn::Drop => I::Drop,
                Insn::MemoryGrow(m) => I::MemoryGrow(m),
                Insn::MemorySize(m) => I::MemorySize(m),
                Insn::Nop => I::Nop,
            };
            func.instruction(&i);
        }
        func.instruction(&I::End);

        builder.code.function(&func);
        self.func_idx
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

        // Function that counts down from n to 0
        let mut f = b.func(&[ValType::I32], &[ValType::I32]);
        f.block(BlockType::Empty)
            .loop_(BlockType::Empty)
            // decrement param
            .local_get(0)
            .i32_eqz()
            .br_if(1) // break if 0
            .local_get(0)
            .i32_const(1)
            .i32_sub()
            .local_set(0)
            .br(0) // continue loop
            .end() // loop
            .end(); // block
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
        // func(a: i32, b: i32) with two locals
        let mut f = b.func(&[ValType::I32, ValType::I32], &[ValType::I32]);
        let x = f.local(ValType::I32); // should be index 2
        let y = f.local(ValType::I32); // should be index 3
        assert_eq!(x, 2);
        assert_eq!(y, 3);
        // x = a + b; y = x * 2; return y
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
        // abs(x): if x < 0 then -x else x
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

        // store(addr, val): mem[addr] = val
        let mut f = b.func(&[ValType::I32, ValType::I32], &[]);
        f.local_get(0).local_get(1).i32_store(mem, 0);
        let store = f.finish(&mut b);
        b.export_func("store", store);

        // load(addr) -> val
        let mut f = b.func(&[ValType::I32], &[ValType::I32]);
        f.local_get(0).i32_load(mem, 0);
        let load = f.finish(&mut b);
        b.export_func("load", load);

        // store8/load8
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
}
