//! DRAT proof checker as a generated WASM core module.
//!
//! Uses [`covalence_wasm::build::ModuleBuilder`] to programmatically emit a
//! WASM module that checks DRAT proofs via the same naive O(n²) algorithm as
//! [`NaiveDratChecker`](crate::NaiveDratChecker).
//!
//! # Memory layout
//!
//! Two memories are used:
//!
//! | Memory | Purpose |
//! |--------|---------|
//! | `mem_problem` | Clause DB (offset, length, active), literal data |
//! | `mem_state` | Assignment array (1 byte/var), trail |
//!
//! # Exported functions
//!
//! | Export | Signature | Description |
//! |--------|-----------|-------------|
//! | `reset` | `() -> ()` | Zero all state |
//! | `add_clause` | `(ptr, len) -> ()` | Add an original clause |
//! | `set_problem` | `() -> ()` | Freeze original clauses, transition to proving |
//! | `drat_add` | `(ptr, len) -> i32` | AT/RAT check; returns 1 if valid |
//! | `drat_delete` | `(ptr, len) -> ()` | Mark a matching clause inactive |
//! | `done` | `() -> i32` | Returns `complete && valid` |

use covalence_wasm::build::{BlockType, FuncIdx, GlobalIdx, MemIdx, ModuleBuilder, ValType};

/// Decompile WASM binary to WAT text for auditing.
pub fn decompile(bytes: &[u8]) -> String {
    covalence_wasm::wasm_to_wat(bytes).expect("valid WASM")
}

// ---------------------------------------------------------------------------
// Memory layout constants
// ---------------------------------------------------------------------------

/// Clause DB entry: 12 bytes (offset: i32, length: i32, active: i32).
const CLAUSE_ENTRY_SIZE: i32 = 12;

/// Clause DB starts at offset 0 in mem_problem.
/// Max 64K clauses → 64K * 12 = 768 KB.
const CLAUSE_DB_BASE: i32 = 0;

/// Literal data starts at 1 MB in mem_problem.
/// Each literal is 4 bytes (i32, DIMACS encoding).
const LIT_DATA_BASE: i32 = 1024 * 1024;

/// Assignment array starts at offset 0 in mem_state (1 byte per variable).
/// 0 = unknown, 1 = true, 2 = false.
const ASSIGN_BASE: i32 = 0;

/// Trail starts at 256 KB in mem_state (i32 per entry = variable index).
const TRAIL_BASE: i32 = 256 * 1024;

// ---------------------------------------------------------------------------
// Global indices (assigned in order by the builder)
// ---------------------------------------------------------------------------

struct Globals {
    state: GlobalIdx,       // 0=BUILDING, 1=PROVING, 2=COMPLETE
    num_vars: GlobalIdx,    // highest variable index seen
    num_clauses: GlobalIdx, // total clause count
    problem_clauses: GlobalIdx,
    complete: GlobalIdx,      // 1 if empty clause derived
    valid: GlobalIdx,         // 1 if all drat-add steps passed
    clause_db_ptr: GlobalIdx, // next free byte in clause DB
    lit_data_ptr: GlobalIdx,  // next free byte in literal data
    trail_len: GlobalIdx,     // current trail length
}

struct Funcs {
    reset: FuncIdx,
    add_clause: FuncIdx,
    set_problem: FuncIdx,
    drat_add: FuncIdx,
    drat_delete: FuncIdx,
    done: FuncIdx,
    // internal helpers
    copy_lits_to_db: FuncIdx,
    ensure_var: FuncIdx,
    clear_trail: FuncIdx,
    unit_propagate: FuncIdx,
    is_at: FuncIdx,
    is_rat: FuncIdx,
    lits_match: FuncIdx,
}

/// Generate the core WASM module bytes for the DRAT checker.
pub fn drat_checker_module() -> Vec<u8> {
    let mut b = ModuleBuilder::new();

    // -- Memories --
    let mem_problem = b.memory(32); // 2 MB
    let mem_state = b.memory(8); // 512 KB

    // -- Globals --
    let g = Globals {
        state: b.global_i32_mut(0),
        num_vars: b.global_i32_mut(0),
        num_clauses: b.global_i32_mut(0),
        problem_clauses: b.global_i32_mut(0),
        complete: b.global_i32_mut(0),
        valid: b.global_i32_mut(1),
        clause_db_ptr: b.global_i32_mut(CLAUSE_DB_BASE),
        lit_data_ptr: b.global_i32_mut(LIT_DATA_BASE),
        trail_len: b.global_i32_mut(0),
    };

    // Build all functions. We need forward references, so we pre-allocate
    // indices and fill them in order.
    let funcs = build_functions(&mut b, mem_problem, mem_state, &g);

    // -- Exports --
    b.export_func("reset", funcs.reset);
    b.export_func("add_clause", funcs.add_clause);
    b.export_func("set_problem", funcs.set_problem);
    b.export_func("drat_add", funcs.drat_add);
    b.export_func("drat_delete", funcs.drat_delete);
    b.export_func("done", funcs.done);
    b.export_memory("mem_problem", mem_problem);
    b.export_memory("mem_state", mem_state);

    b.finish()
}

fn build_functions(b: &mut ModuleBuilder, mp: MemIdx, ms: MemIdx, g: &Globals) -> Funcs {
    // Build in dependency order (callees before callers).

    // -- ensure_var(var_idx: i32) --
    let ensure_var = {
        let mut f = b.func(&[ValType::I32], &[]);
        // if var_idx > g_num_vars { g_num_vars = var_idx }
        f.local_get(0)
            .global_get(g.num_vars)
            .i32_gt_s()
            .if_(BlockType::Empty)
            .local_get(0)
            .global_set(g.num_vars)
            .end();
        f.finish(b)
    };

    // -- clear_trail() --
    // Undo all assignments on the trail, reset trail_len to 0.
    let clear_trail = {
        let mut f = b.func(&[], &[]);
        let i = f.local(ValType::I32); // loop index
        let var_idx = f.local(ValType::I32);

        // i = g_trail_len - 1
        f.global_get(g.trail_len)
            .i32_const(1)
            .i32_sub()
            .local_set(i);

        // while i >= 0
        f.block(BlockType::Empty)
            .loop_(BlockType::Empty)
            .local_get(i)
            .i32_const(0)
            .i32_lt_s()
            .br_if(1); // break

        // var_idx = mem_state[TRAIL_BASE + i*4]
        f.local_get(i)
            .i32_const(4)
            .i32_mul()
            .i32_load(ms, TRAIL_BASE as u32)
            .local_set(var_idx);

        // mem_state[ASSIGN_BASE + var_idx] = 0 (unknown)
        f.local_get(var_idx)
            .i32_const(0)
            .i32_store8(ms, ASSIGN_BASE as u32);

        // i--
        f.local_get(i).i32_const(1).i32_sub().local_set(i);
        f.br(0); // continue
        f.end(); // loop
        f.end(); // block

        // g_trail_len = 0
        f.i32_const(0).global_set(g.trail_len);
        f.finish(b)
    };

    // -- copy_lits_to_db(ptr: i32, len: i32) --
    // Copy len literals from mem_problem[ptr] to the literal data area,
    // create a clause DB entry, and update globals.
    let copy_lits_to_db = {
        let mut f = b.func(&[ValType::I32, ValType::I32], &[]);
        let ptr = 0u32; // param 0
        let len = 1u32; // param 1
        let entry_addr = f.local(ValType::I32);
        let lit_offset = f.local(ValType::I32);
        let i = f.local(ValType::I32);
        let lit_val = f.local(ValType::I32);
        let abs_val = f.local(ValType::I32);

        // entry_addr = g_clause_db_ptr
        f.global_get(g.clause_db_ptr).local_set(entry_addr);
        // lit_offset = g_lit_data_ptr
        f.global_get(g.lit_data_ptr).local_set(lit_offset);

        // Write clause DB entry: (lit_offset, len, 1=active)
        f.local_get(entry_addr)
            .local_get(lit_offset)
            .i32_store(mp, 0); // offset
        f.local_get(entry_addr).local_get(len).i32_store(mp, 4); // length
        f.local_get(entry_addr).i32_const(1).i32_store(mp, 8); // active

        // Copy literals and track max variable
        // for i = 0; i < len; i++
        f.i32_const(0).local_set(i);
        f.block(BlockType::Empty)
            .loop_(BlockType::Empty)
            .local_get(i)
            .local_get(len)
            .i32_ge_s()
            .br_if(1); // break if i >= len

        // lit_val = mem_problem[ptr + i*4]
        f.local_get(ptr)
            .local_get(i)
            .i32_const(4)
            .i32_mul()
            .i32_add()
            .i32_load(mp, 0)
            .local_set(lit_val);

        // Store lit at lit_data area
        f.local_get(lit_offset)
            .local_get(i)
            .i32_const(4)
            .i32_mul()
            .i32_add()
            .local_get(lit_val)
            .i32_store(mp, 0);

        // abs_val = abs(lit_val)
        // if lit_val < 0 then 0 - lit_val else lit_val
        f.local_get(lit_val)
            .i32_const(0)
            .i32_lt_s()
            .if_(BlockType::Result(ValType::I32))
            .i32_const(0)
            .local_get(lit_val)
            .i32_sub()
            .else_()
            .local_get(lit_val)
            .end()
            .local_set(abs_val);

        // ensure_var(abs_val)
        f.local_get(abs_val).call(ensure_var);

        // i++
        f.local_get(i).i32_const(1).i32_add().local_set(i);
        f.br(0); // continue
        f.end(); // loop
        f.end(); // block

        // Update pointers
        // g_clause_db_ptr += CLAUSE_ENTRY_SIZE
        f.global_get(g.clause_db_ptr)
            .i32_const(CLAUSE_ENTRY_SIZE)
            .i32_add()
            .global_set(g.clause_db_ptr);

        // g_lit_data_ptr += len * 4
        f.global_get(g.lit_data_ptr)
            .local_get(len)
            .i32_const(4)
            .i32_mul()
            .i32_add()
            .global_set(g.lit_data_ptr);

        // g_num_clauses++
        f.global_get(g.num_clauses)
            .i32_const(1)
            .i32_add()
            .global_set(g.num_clauses);

        // If len == 0, mark complete
        f.local_get(len)
            .i32_eqz()
            .if_(BlockType::Empty)
            .i32_const(1)
            .global_set(g.complete)
            .end();

        f.finish(b)
    };

    // -- lits_match(a_off: i32, a_len: i32, b_off: i32, b_len: i32) -> i32 --
    // Order-independent clause comparison.
    let lits_match = {
        let mut f = b.func(
            &[ValType::I32, ValType::I32, ValType::I32, ValType::I32],
            &[ValType::I32],
        );
        let a_off = 0u32;
        let a_len = 1u32;
        let b_off = 2u32;
        let b_len = 3u32;
        let i = f.local(ValType::I32);
        let j = f.local(ValType::I32);
        let a_lit = f.local(ValType::I32);
        let found = f.local(ValType::I32);

        // if a_len != b_len return 0
        f.local_get(a_len)
            .local_get(b_len)
            .i32_ne()
            .if_(BlockType::Empty)
            .i32_const(0)
            .return_()
            .end();

        // For each lit in a, check it exists in b
        f.i32_const(0).local_set(i);
        f.block(BlockType::Empty)
            .loop_(BlockType::Empty)
            .local_get(i)
            .local_get(a_len)
            .i32_ge_s()
            .br_if(1);

        // a_lit = mem_problem[a_off + i*4]
        f.local_get(a_off)
            .local_get(i)
            .i32_const(4)
            .i32_mul()
            .i32_add()
            .i32_load(mp, 0)
            .local_set(a_lit);

        // found = 0
        f.i32_const(0).local_set(found);

        // for j = 0; j < b_len; j++
        f.i32_const(0).local_set(j);
        f.block(BlockType::Empty)
            .loop_(BlockType::Empty)
            .local_get(j)
            .local_get(b_len)
            .i32_ge_s()
            .br_if(1);

        // if mem_problem[b_off + j*4] == a_lit: found = 1, break
        f.local_get(b_off)
            .local_get(j)
            .i32_const(4)
            .i32_mul()
            .i32_add()
            .i32_load(mp, 0)
            .local_get(a_lit)
            .i32_eq()
            .if_(BlockType::Empty)
            .i32_const(1)
            .local_set(found)
            .br(2) // break inner loop (block around it)
            .end();

        f.local_get(j).i32_const(1).i32_add().local_set(j);
        f.br(0);
        f.end(); // loop
        f.end(); // block

        // if !found return 0
        f.local_get(found)
            .i32_eqz()
            .if_(BlockType::Empty)
            .i32_const(0)
            .return_()
            .end();

        f.local_get(i).i32_const(1).i32_add().local_set(i);
        f.br(0);
        f.end(); // loop
        f.end(); // block

        f.i32_const(1);
        f.finish(b)
    };

    // -- unit_propagate() -> i32 --
    // Returns 1 if conflict found (AT holds), 0 otherwise.
    // Scans all active clauses, does unit propagation until fixpoint or conflict.
    let unit_propagate = {
        let mut f = b.func(&[], &[ValType::I32]);
        let ci = f.local(ValType::I32); // clause index
        let entry_addr = f.local(ValType::I32);
        let c_off = f.local(ValType::I32); // clause literal offset
        let c_len = f.local(ValType::I32); // clause literal count
        let li = f.local(ValType::I32); // literal index within clause
        let lit = f.local(ValType::I32); // current literal
        let var = f.local(ValType::I32); // abs(lit)
        let assign_val = f.local(ValType::I32); // assignment value
        let satisfied = f.local(ValType::I32);
        let unset_count = f.local(ValType::I32);
        let last_unset = f.local(ValType::I32);
        let progress = f.local(ValType::I32);
        let lit_decision = f.local(ValType::I32); // mapped decision for this lit

        // Outer propagation loop
        f.block(BlockType::Empty).loop_(BlockType::Empty);

        f.i32_const(0).local_set(progress);

        // for ci = 0; ci < g_num_clauses; ci++
        f.i32_const(0).local_set(ci);
        f.block(BlockType::Empty)
            .loop_(BlockType::Empty)
            .local_get(ci)
            .global_get(g.num_clauses)
            .i32_ge_s()
            .br_if(1);

        // entry_addr = CLAUSE_DB_BASE + ci * CLAUSE_ENTRY_SIZE
        f.local_get(ci)
            .i32_const(CLAUSE_ENTRY_SIZE)
            .i32_mul()
            .local_set(entry_addr);

        // Skip inactive clauses
        f.local_get(entry_addr)
            .i32_load(mp, 8) // active field
            .i32_eqz()
            .if_(BlockType::Empty)
            .local_get(ci)
            .i32_const(1)
            .i32_add()
            .local_set(ci)
            .br(2) // continue outer clause loop
            .end();

        // c_off = entry.offset, c_len = entry.length
        f.local_get(entry_addr).i32_load(mp, 0).local_set(c_off);
        f.local_get(entry_addr).i32_load(mp, 4).local_set(c_len);

        f.i32_const(0).local_set(satisfied);
        f.i32_const(0).local_set(unset_count);
        f.i32_const(0).local_set(last_unset);

        // for li = 0; li < c_len; li++
        f.i32_const(0).local_set(li);
        f.block(BlockType::Empty)
            .loop_(BlockType::Empty)
            .local_get(li)
            .local_get(c_len)
            .i32_ge_s()
            .br_if(1);

        // lit = mem_problem[c_off + li*4]
        f.local_get(c_off)
            .local_get(li)
            .i32_const(4)
            .i32_mul()
            .i32_add()
            .i32_load(mp, 0)
            .local_set(lit);

        // var = abs(lit)
        f.local_get(lit)
            .i32_const(0)
            .i32_lt_s()
            .if_(BlockType::Result(ValType::I32))
            .i32_const(0)
            .local_get(lit)
            .i32_sub()
            .else_()
            .local_get(lit)
            .end()
            .local_set(var);

        // assign_val = mem_state[ASSIGN_BASE + var] (0=unknown, 1=true, 2=false)
        f.local_get(var)
            .i32_load8_u(ms, ASSIGN_BASE as u32)
            .local_set(assign_val);

        // Compute lit_decision: for positive lit, decision = assign_val;
        // for negative lit, swap 1↔2 (true↔false).
        // lit_decision = assign_val (initially)
        // if lit < 0 && assign_val == 1: lit_decision = 2
        // if lit < 0 && assign_val == 2: lit_decision = 1
        f.local_get(assign_val).local_set(lit_decision);
        f.local_get(lit)
            .i32_const(0)
            .i32_lt_s()
            .if_(BlockType::Empty)
            // negative literal: swap sat/unsat
            .local_get(assign_val)
            .i32_const(1)
            .i32_eq()
            .if_(BlockType::Empty)
            .i32_const(2)
            .local_set(lit_decision)
            .end()
            .local_get(assign_val)
            .i32_const(2)
            .i32_eq()
            .if_(BlockType::Empty)
            .i32_const(1)
            .local_set(lit_decision)
            .end()
            .end();

        // if lit_decision == 1 (SAT): satisfied = 1, break
        f.local_get(lit_decision)
            .i32_const(1)
            .i32_eq()
            .if_(BlockType::Empty)
            .i32_const(1)
            .local_set(satisfied)
            .br(2) // break lit loop
            .end();

        // if lit_decision == 0 (UNKNOWN): unset_count++, last_unset = lit
        f.local_get(lit_decision)
            .i32_eqz()
            .if_(BlockType::Empty)
            .local_get(unset_count)
            .i32_const(1)
            .i32_add()
            .local_set(unset_count)
            .local_get(lit)
            .local_set(last_unset)
            .end();

        // lit_decision == 2 (UNSAT): do nothing

        f.local_get(li).i32_const(1).i32_add().local_set(li);
        f.br(0);
        f.end(); // loop (lits)
        f.end(); // block (lits)

        // After scanning clause:
        // if satisfied: continue to next clause
        f.local_get(satisfied)
            .if_(BlockType::Empty)
            .local_get(ci)
            .i32_const(1)
            .i32_add()
            .local_set(ci)
            .br(2) // continue clause loop
            .end();

        // if unset_count == 0: conflict! return 1
        f.local_get(unset_count)
            .i32_eqz()
            .if_(BlockType::Empty)
            .i32_const(1)
            .return_()
            .end();

        // if unset_count == 1: unit clause, assign last_unset true
        f.local_get(unset_count)
            .i32_const(1)
            .i32_eq()
            .if_(BlockType::Empty);

        // Assign last_unset true:
        // var = abs(last_unset)
        f.local_get(last_unset)
            .i32_const(0)
            .i32_lt_s()
            .if_(BlockType::Result(ValType::I32))
            .i32_const(0)
            .local_get(last_unset)
            .i32_sub()
            .else_()
            .local_get(last_unset)
            .end()
            .local_set(var);

        // assign_val = if last_unset > 0 then 1 else 2
        f.local_get(last_unset)
            .i32_const(0)
            .i32_gt_s()
            .if_(BlockType::Result(ValType::I32))
            .i32_const(1) // true
            .else_()
            .i32_const(2) // false
            .end()
            .local_set(assign_val);

        // mem_state[ASSIGN_BASE + var] = assign_val
        f.local_get(var)
            .local_get(assign_val)
            .i32_store8(ms, ASSIGN_BASE as u32);

        // trail[g_trail_len] = var
        f.global_get(g.trail_len)
            .i32_const(4)
            .i32_mul()
            .local_get(var)
            .i32_store(ms, TRAIL_BASE as u32);

        // g_trail_len++
        f.global_get(g.trail_len)
            .i32_const(1)
            .i32_add()
            .global_set(g.trail_len);

        f.i32_const(1).local_set(progress);

        // Restart scan from beginning
        f.i32_const(0).local_set(ci);
        f.br(2) // continue clause loop from start
            .end(); // if unset_count == 1

        // Otherwise (unset_count >= 2): move to next clause
        f.local_get(ci).i32_const(1).i32_add().local_set(ci);
        f.br(0);
        f.end(); // loop (clauses)
        f.end(); // block (clauses)

        // After full scan: if progress, restart; else return 0
        f.local_get(progress).br_if(0); // continue outer loop
        f.end(); // loop (propagation)
        f.end(); // block (propagation)

        f.i32_const(0); // no conflict
        f.finish(b)
    };

    // -- is_at(lits_off: i32, lits_len: i32) -> i32 --
    // Negate all candidate literals, then call unit_propagate.
    let is_at = {
        let mut f = b.func(&[ValType::I32, ValType::I32], &[ValType::I32]);
        let lits_off = 0u32;
        let lits_len = 1u32;
        let i = f.local(ValType::I32);
        let lit = f.local(ValType::I32);
        let var = f.local(ValType::I32);
        let cur_assign = f.local(ValType::I32);
        let neg_assign = f.local(ValType::I32);
        let result = f.local(ValType::I32);

        // For each literal in the candidate, assign its negation.
        f.i32_const(0).local_set(i);
        f.block(BlockType::Empty)
            .loop_(BlockType::Empty)
            .local_get(i)
            .local_get(lits_len)
            .i32_ge_s()
            .br_if(1);

        // lit = mem_problem[lits_off + i*4]
        f.local_get(lits_off)
            .local_get(i)
            .i32_const(4)
            .i32_mul()
            .i32_add()
            .i32_load(mp, 0)
            .local_set(lit);

        // var = abs(lit)
        f.local_get(lit)
            .i32_const(0)
            .i32_lt_s()
            .if_(BlockType::Result(ValType::I32))
            .i32_const(0)
            .local_get(lit)
            .i32_sub()
            .else_()
            .local_get(lit)
            .end()
            .local_set(var);

        // Check if complementary literals (lit is already satisfied → tautology)
        // cur_assign = mem_state[ASSIGN_BASE + var]
        f.local_get(var)
            .i32_load8_u(ms, ASSIGN_BASE as u32)
            .local_set(cur_assign);

        // For positive lit: if cur_assign == 1 (true) → lit is satisfied → tautology
        // For negative lit: if cur_assign == 2 (false) → ¬var is true → lit is satisfied
        // Compute "is lit satisfied?"
        f.local_get(lit)
            .i32_const(0)
            .i32_gt_s()
            .if_(BlockType::Empty)
            // positive lit: satisfied if assign == 1
            .local_get(cur_assign)
            .i32_const(1)
            .i32_eq()
            .if_(BlockType::Empty)
            .call(clear_trail)
            .i32_const(1)
            .return_()
            .end()
            .else_()
            // negative lit: satisfied if assign == 2
            .local_get(cur_assign)
            .i32_const(2)
            .i32_eq()
            .if_(BlockType::Empty)
            .call(clear_trail)
            .i32_const(1)
            .return_()
            .end()
            .end();

        // Negate lit: if lit > 0, assign false (2); if lit < 0, assign true (1)
        f.local_get(lit)
            .i32_const(0)
            .i32_gt_s()
            .if_(BlockType::Result(ValType::I32))
            .i32_const(2) // false
            .else_()
            .i32_const(1) // true
            .end()
            .local_set(neg_assign);

        // Only assign if currently unknown
        f.local_get(cur_assign)
            .i32_eqz() // unknown
            .if_(BlockType::Empty)
            // mem_state[ASSIGN_BASE + var] = neg_assign
            .local_get(var)
            .local_get(neg_assign)
            .i32_store8(ms, ASSIGN_BASE as u32)
            // trail[g_trail_len] = var
            .global_get(g.trail_len)
            .i32_const(4)
            .i32_mul()
            .local_get(var)
            .i32_store(ms, TRAIL_BASE as u32)
            // g_trail_len++
            .global_get(g.trail_len)
            .i32_const(1)
            .i32_add()
            .global_set(g.trail_len)
            .end();

        f.local_get(i).i32_const(1).i32_add().local_set(i);
        f.br(0);
        f.end(); // loop
        f.end(); // block

        // Now run unit propagation
        f.call(unit_propagate).local_set(result);
        f.call(clear_trail);
        f.local_get(result);
        f.finish(b)
    };

    // -- is_rat(cand_off: i32, cand_len: i32, pivot: i32) -> i32 --
    // For each active clause containing ¬pivot, check resolvent is AT.
    let is_rat = {
        let mut f = b.func(&[ValType::I32, ValType::I32, ValType::I32], &[ValType::I32]);
        let cand_off = 0u32;
        let cand_len = 1u32;
        let pivot = 2u32;
        let neg_pivot = f.local(ValType::I32);
        let ci = f.local(ValType::I32);
        let entry_addr = f.local(ValType::I32);
        let c_off = f.local(ValType::I32);
        let c_len = f.local(ValType::I32);
        let has_neg_pivot = f.local(ValType::I32);
        let li = f.local(ValType::I32);
        let lit = f.local(ValType::I32);
        // We'll build the resolvent in a scratch area at a fixed offset in mem_problem.
        // Use the area after the current lit_data_ptr.
        let resolvent_base = f.local(ValType::I32);
        let resolvent_len = f.local(ValType::I32);
        let j = f.local(ValType::I32);
        let dup = f.local(ValType::I32);
        let at_result = f.local(ValType::I32);

        // neg_pivot = -pivot
        f.i32_const(0)
            .local_get(pivot)
            .i32_sub()
            .local_set(neg_pivot);

        // resolvent_base = g_lit_data_ptr (scratch area after all clause data)
        f.global_get(g.lit_data_ptr).local_set(resolvent_base);

        // for ci = 0; ci < g_num_clauses; ci++
        f.i32_const(0).local_set(ci);
        f.block(BlockType::Empty)
            .loop_(BlockType::Empty)
            .local_get(ci)
            .global_get(g.num_clauses)
            .i32_ge_s()
            .br_if(1);

        // entry_addr = ci * CLAUSE_ENTRY_SIZE
        f.local_get(ci)
            .i32_const(CLAUSE_ENTRY_SIZE)
            .i32_mul()
            .local_set(entry_addr);

        // Skip inactive
        f.local_get(entry_addr)
            .i32_load(mp, 8)
            .i32_eqz()
            .if_(BlockType::Empty)
            .local_get(ci)
            .i32_const(1)
            .i32_add()
            .local_set(ci)
            .br(2)
            .end();

        f.local_get(entry_addr).i32_load(mp, 0).local_set(c_off);
        f.local_get(entry_addr).i32_load(mp, 4).local_set(c_len);

        // Check if clause contains neg_pivot
        f.i32_const(0).local_set(has_neg_pivot);
        f.i32_const(0).local_set(li);
        f.block(BlockType::Empty)
            .loop_(BlockType::Empty)
            .local_get(li)
            .local_get(c_len)
            .i32_ge_s()
            .br_if(1);

        f.local_get(c_off)
            .local_get(li)
            .i32_const(4)
            .i32_mul()
            .i32_add()
            .i32_load(mp, 0)
            .local_get(neg_pivot)
            .i32_eq()
            .if_(BlockType::Empty)
            .i32_const(1)
            .local_set(has_neg_pivot)
            .br(2) // break
            .end();

        f.local_get(li).i32_const(1).i32_add().local_set(li);
        f.br(0);
        f.end(); // loop
        f.end(); // block

        // If no neg_pivot, skip this clause
        f.local_get(has_neg_pivot)
            .i32_eqz()
            .if_(BlockType::Empty)
            .local_get(ci)
            .i32_const(1)
            .i32_add()
            .local_set(ci)
            .br(2)
            .end();

        // Build resolvent: (candidate ∪ clause) \ {pivot, ¬pivot}
        f.i32_const(0).local_set(resolvent_len);

        // Add candidate lits (excluding pivot and neg_pivot)
        f.i32_const(0).local_set(li);
        f.block(BlockType::Empty)
            .loop_(BlockType::Empty)
            .local_get(li)
            .local_get(cand_len)
            .i32_ge_s()
            .br_if(1);

        f.local_get(cand_off)
            .local_get(li)
            .i32_const(4)
            .i32_mul()
            .i32_add()
            .i32_load(mp, 0)
            .local_set(lit);

        // Skip pivot and neg_pivot
        f.local_get(lit)
            .local_get(pivot)
            .i32_eq()
            .local_get(lit)
            .local_get(neg_pivot)
            .i32_eq()
            .i32_or()
            .if_(BlockType::Empty)
            .local_get(li)
            .i32_const(1)
            .i32_add()
            .local_set(li)
            .br(2)
            .end();

        // Check for duplicates in resolvent
        f.i32_const(0).local_set(dup);
        f.i32_const(0).local_set(j);
        f.block(BlockType::Empty)
            .loop_(BlockType::Empty)
            .local_get(j)
            .local_get(resolvent_len)
            .i32_ge_s()
            .br_if(1);

        f.local_get(resolvent_base)
            .local_get(j)
            .i32_const(4)
            .i32_mul()
            .i32_add()
            .i32_load(mp, 0)
            .local_get(lit)
            .i32_eq()
            .if_(BlockType::Empty)
            .i32_const(1)
            .local_set(dup)
            .br(2)
            .end();

        f.local_get(j).i32_const(1).i32_add().local_set(j);
        f.br(0);
        f.end(); // loop
        f.end(); // block

        f.local_get(dup)
            .i32_eqz()
            .if_(BlockType::Empty)
            // Add lit to resolvent
            .local_get(resolvent_base)
            .local_get(resolvent_len)
            .i32_const(4)
            .i32_mul()
            .i32_add()
            .local_get(lit)
            .i32_store(mp, 0)
            .local_get(resolvent_len)
            .i32_const(1)
            .i32_add()
            .local_set(resolvent_len)
            .end();

        f.local_get(li).i32_const(1).i32_add().local_set(li);
        f.br(0);
        f.end(); // loop
        f.end(); // block

        // Add clause D lits (excluding pivot and neg_pivot, deduped)
        f.i32_const(0).local_set(li);
        f.block(BlockType::Empty)
            .loop_(BlockType::Empty)
            .local_get(li)
            .local_get(c_len)
            .i32_ge_s()
            .br_if(1);

        f.local_get(c_off)
            .local_get(li)
            .i32_const(4)
            .i32_mul()
            .i32_add()
            .i32_load(mp, 0)
            .local_set(lit);

        // Skip pivot and neg_pivot
        f.local_get(lit)
            .local_get(pivot)
            .i32_eq()
            .local_get(lit)
            .local_get(neg_pivot)
            .i32_eq()
            .i32_or()
            .if_(BlockType::Empty)
            .local_get(li)
            .i32_const(1)
            .i32_add()
            .local_set(li)
            .br(2)
            .end();

        // Dedup check
        f.i32_const(0).local_set(dup);
        f.i32_const(0).local_set(j);
        f.block(BlockType::Empty)
            .loop_(BlockType::Empty)
            .local_get(j)
            .local_get(resolvent_len)
            .i32_ge_s()
            .br_if(1);

        f.local_get(resolvent_base)
            .local_get(j)
            .i32_const(4)
            .i32_mul()
            .i32_add()
            .i32_load(mp, 0)
            .local_get(lit)
            .i32_eq()
            .if_(BlockType::Empty)
            .i32_const(1)
            .local_set(dup)
            .br(2)
            .end();

        f.local_get(j).i32_const(1).i32_add().local_set(j);
        f.br(0);
        f.end(); // loop
        f.end(); // block

        f.local_get(dup)
            .i32_eqz()
            .if_(BlockType::Empty)
            .local_get(resolvent_base)
            .local_get(resolvent_len)
            .i32_const(4)
            .i32_mul()
            .i32_add()
            .local_get(lit)
            .i32_store(mp, 0)
            .local_get(resolvent_len)
            .i32_const(1)
            .i32_add()
            .local_set(resolvent_len)
            .end();

        f.local_get(li).i32_const(1).i32_add().local_set(li);
        f.br(0);
        f.end(); // loop
        f.end(); // block

        // Check resolvent is AT
        f.local_get(resolvent_base)
            .local_get(resolvent_len)
            .call(is_at)
            .local_set(at_result);

        f.local_get(at_result)
            .i32_eqz()
            .if_(BlockType::Empty)
            .i32_const(0)
            .return_()
            .end();

        f.local_get(ci).i32_const(1).i32_add().local_set(ci);
        f.br(0);
        f.end(); // loop (clauses)
        f.end(); // block (clauses)

        f.i32_const(1); // all resolvents passed
        f.finish(b)
    };

    // -- reset() --
    let reset = {
        let mut f = b.func(&[], &[]);
        f.i32_const(0).global_set(g.state);
        f.i32_const(0).global_set(g.num_vars);
        f.i32_const(0).global_set(g.num_clauses);
        f.i32_const(0).global_set(g.problem_clauses);
        f.i32_const(0).global_set(g.complete);
        f.i32_const(1).global_set(g.valid);
        f.i32_const(CLAUSE_DB_BASE).global_set(g.clause_db_ptr);
        f.i32_const(LIT_DATA_BASE).global_set(g.lit_data_ptr);
        f.i32_const(0).global_set(g.trail_len);
        f.finish(b)
    };

    // -- add_clause(ptr: i32, len: i32) --
    let add_clause = {
        let mut f = b.func(&[ValType::I32, ValType::I32], &[]);
        // Trap if state != BUILDING (0)
        f.global_get(g.state)
            .if_(BlockType::Empty)
            .unreachable()
            .end();
        f.local_get(0).local_get(1).call(copy_lits_to_db);
        f.finish(b)
    };

    // -- set_problem() --
    let set_problem = {
        let mut f = b.func(&[], &[]);
        f.global_get(g.num_clauses).global_set(g.problem_clauses);
        f.i32_const(1).global_set(g.state); // PROVING
        f.finish(b)
    };

    // -- drat_add(ptr: i32, len: i32) -> i32 --
    let drat_add = {
        let mut f = b.func(&[ValType::I32, ValType::I32], &[ValType::I32]);
        let ptr = 0u32;
        let len = 1u32;
        let at_result = f.local(ValType::I32);
        let i = f.local(ValType::I32);
        let pivot = f.local(ValType::I32);
        let rat_result = f.local(ValType::I32);
        let var = f.local(ValType::I32);

        // Ensure variables are tracked
        f.i32_const(0).local_set(i);
        f.block(BlockType::Empty)
            .loop_(BlockType::Empty)
            .local_get(i)
            .local_get(len)
            .i32_ge_s()
            .br_if(1);

        f.local_get(ptr)
            .local_get(i)
            .i32_const(4)
            .i32_mul()
            .i32_add()
            .i32_load(mp, 0)
            .local_set(pivot); // reuse as temp

        // abs
        f.local_get(pivot)
            .i32_const(0)
            .i32_lt_s()
            .if_(BlockType::Result(ValType::I32))
            .i32_const(0)
            .local_get(pivot)
            .i32_sub()
            .else_()
            .local_get(pivot)
            .end()
            .local_set(var);
        f.local_get(var).call(ensure_var);

        f.local_get(i).i32_const(1).i32_add().local_set(i);
        f.br(0);
        f.end(); // loop
        f.end(); // block

        // AT check
        f.local_get(ptr)
            .local_get(len)
            .call(is_at)
            .local_set(at_result);

        f.local_get(at_result)
            .if_(BlockType::Empty)
            // AT passed — add clause
            .local_get(ptr)
            .local_get(len)
            .call(copy_lits_to_db)
            .i32_const(1)
            .return_()
            .end();

        // RAT check if len > 0
        f.local_get(len)
            .i32_eqz()
            .if_(BlockType::Empty)
            // Empty clause failed AT → invalid
            .i32_const(0)
            .global_set(g.valid)
            .i32_const(0)
            .return_()
            .end();

        // Try each literal as pivot
        f.i32_const(0).local_set(i);
        f.block(BlockType::Empty)
            .loop_(BlockType::Empty)
            .local_get(i)
            .local_get(len)
            .i32_ge_s()
            .br_if(1);

        f.local_get(ptr)
            .local_get(i)
            .i32_const(4)
            .i32_mul()
            .i32_add()
            .i32_load(mp, 0)
            .local_set(pivot);

        f.local_get(ptr)
            .local_get(len)
            .local_get(pivot)
            .call(is_rat)
            .local_set(rat_result);

        f.local_get(rat_result)
            .if_(BlockType::Empty)
            // RAT passed with this pivot — add clause
            .local_get(ptr)
            .local_get(len)
            .call(copy_lits_to_db)
            .i32_const(1)
            .return_()
            .end();

        f.local_get(i).i32_const(1).i32_add().local_set(i);
        f.br(0);
        f.end(); // loop
        f.end(); // block

        // No pivot worked → invalid
        f.i32_const(0).global_set(g.valid);
        f.i32_const(0);
        f.finish(b)
    };

    // -- drat_delete(ptr: i32, len: i32) --
    let drat_delete = {
        let mut f = b.func(&[ValType::I32, ValType::I32], &[]);
        let ptr = 0u32;
        let len = 1u32;
        let ci = f.local(ValType::I32);
        let entry_addr = f.local(ValType::I32);
        let c_off = f.local(ValType::I32);
        let c_len = f.local(ValType::I32);

        f.i32_const(0).local_set(ci);
        f.block(BlockType::Empty)
            .loop_(BlockType::Empty)
            .local_get(ci)
            .global_get(g.num_clauses)
            .i32_ge_s()
            .br_if(1);

        f.local_get(ci)
            .i32_const(CLAUSE_ENTRY_SIZE)
            .i32_mul()
            .local_set(entry_addr);

        // Skip inactive
        f.local_get(entry_addr)
            .i32_load(mp, 8)
            .i32_eqz()
            .if_(BlockType::Empty)
            .local_get(ci)
            .i32_const(1)
            .i32_add()
            .local_set(ci)
            .br(2)
            .end();

        f.local_get(entry_addr).i32_load(mp, 0).local_set(c_off);
        f.local_get(entry_addr).i32_load(mp, 4).local_set(c_len);

        // Check if lits match
        f.local_get(c_off)
            .local_get(c_len)
            .local_get(ptr)
            .local_get(len)
            .call(lits_match);

        f.if_(BlockType::Empty)
            // Set active = 0
            .local_get(entry_addr)
            .i32_const(0)
            .i32_store(mp, 8)
            .return_()
            .end();

        f.local_get(ci).i32_const(1).i32_add().local_set(ci);
        f.br(0);
        f.end(); // loop
        f.end(); // block

        f.finish(b)
    };

    // -- done() -> i32 --
    let done = {
        let mut f = b.func(&[], &[ValType::I32]);
        f.i32_const(2).global_set(g.state); // COMPLETE
        f.global_get(g.complete).global_get(g.valid).i32_and();
        f.finish(b)
    };

    Funcs {
        reset,
        add_clause,
        set_problem,
        drat_add,
        drat_delete,
        done,
        copy_lits_to_db,
        ensure_var,
        clear_trail,
        unit_propagate,
        is_at,
        is_rat,
        lits_match,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn module_compiles() {
        let bytes = drat_checker_module();
        let wat = decompile(&bytes);
        assert!(wat.contains("func"), "module should have functions");
    }

    #[test]
    fn module_has_expected_exports() {
        let bytes = drat_checker_module();
        let info = covalence_wasm::parse_module(&bytes).unwrap();
        let exports: Vec<&str> = info.exports.iter().map(|s| s.as_str()).collect();
        for name in [
            "reset",
            "add_clause",
            "set_problem",
            "drat_add",
            "drat_delete",
            "done",
        ] {
            assert!(exports.contains(&name), "missing export: {name}");
        }
        assert!(
            exports.contains(&"mem_problem"),
            "missing mem_problem export"
        );
        assert!(exports.contains(&"mem_state"), "missing mem_state export");
    }
}
