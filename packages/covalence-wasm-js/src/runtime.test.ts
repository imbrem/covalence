import { readFileSync } from "node:fs";
import { fileURLToPath } from "node:url";
import { dirname, join } from "node:path";
import { describe, it, expect } from "vitest";
import { Runtime, WasmRuntimeError } from "./index.js";

const __dirname = dirname(fileURLToPath(import.meta.url));
const ANSWER_WASM = readFileSync(join(__dirname, "__fixtures__", "answer.wasm"));
// Rust-built wasm32-unknown-unknown artifact that exposes
// covalence_wasm::build::ModuleBuilder via a C ABI. Rebuild with:
//   cargo build --target wasm32-unknown-unknown --release \
//                -p covalence-wasm-build-guest
//   cp target/wasm32-unknown-unknown/release/covalence_wasm_build_guest.wasm \
//      packages/covalence-wasm-js/src/__fixtures__/build_guest.wasm
const BUILD_GUEST_WASM = readFileSync(
  join(__dirname, "__fixtures__", "build_guest.wasm"),
);

describe("Runtime (JS host backend)", () => {
  it("compile → instantiate → call roundtrip", async () => {
    const rt = new Runtime();
    const comp = await rt.compile(ANSWER_WASM);
    const inst = await rt.instantiate(comp);
    const out = rt.callU32(inst, "answer", 41);
    expect(out).toBe(42);
  });

  it("missing export errors with a useful message", async () => {
    const rt = new Runtime();
    const comp = await rt.compile(ANSWER_WASM);
    const inst = await rt.instantiate(comp);
    expect(() => rt.callU32(inst, "nope", 0)).toThrow(/nope/);
  });

  it("rejects component bytes with a Phase 3 pointer", async () => {
    const rt = new Runtime();
    // Build a minimal component preamble: \0asm + component version.
    const fakeComponent = Uint8Array.of(0x00, 0x61, 0x73, 0x6d, 0x0d, 0x00, 0x01, 0x00);
    await expect(rt.compile(fakeComponent)).rejects.toThrow(WasmRuntimeError);
    await expect(rt.compile(fakeComponent)).rejects.toThrow(/jco/);
  });

  // Metacircular smoke test: load a Rust-built wasm32 artifact that
  // uses covalence_wasm::build::ModuleBuilder, drive it through the
  // Runtime, then feed its output back through the SAME Runtime. JS
  // contributes no build logic — only the executor.
  it("Rust-built guest produces wasm that runs in the same Runtime", async () => {
    const rt = new Runtime();

    // 1. Load the Rust ModuleBuilder-as-wasm and instantiate it.
    const builderComp = await rt.compile(BUILD_GUEST_WASM);
    const builderInst = await rt.instantiate(builderComp);
    const exports = builderInst.instance.exports as {
      memory: WebAssembly.Memory;
      build_plus: (delta: number) => number;
      output_ptr: () => number;
    };

    // 2. Call into Rust: build `(x: i32) -> i32 { x + 5 }`.
    const delta = 5;
    const len = exports.build_plus(delta);
    const ptr = exports.output_ptr();
    // Copy out of the guest's linear memory before doing anything else
    // with it. (The buffer is stable across reads but moves on the
    // next build_plus call.)
    const builtBytes = new Uint8Array(
      exports.memory.buffer.slice(ptr, ptr + len),
    );

    // 3. Feed the Rust-built bytes back through the executor.
    const builtComp = await rt.compile(builtBytes);
    const builtInst = await rt.instantiate(builtComp);
    expect(rt.callU32(builtInst, "answer", 37)).toBe(42);
  });

  // Re-use the same builder instance to produce two different modules
  // — exercises the static-buffer convention and proves no caching
  // surprises across calls.
  it("can drive the Rust builder twice from one instance", async () => {
    const rt = new Runtime();
    const builderInst = await rt.instantiate(
      await rt.compile(BUILD_GUEST_WASM),
    );
    const exports = builderInst.instance.exports as {
      memory: WebAssembly.Memory;
      build_plus: (delta: number) => number;
      output_ptr: () => number;
    };

    const buildAndRun = async (delta: number, input: number) => {
      const len = exports.build_plus(delta);
      const ptr = exports.output_ptr();
      const bytes = new Uint8Array(exports.memory.buffer.slice(ptr, ptr + len));
      const inst = await rt.instantiate(await rt.compile(bytes));
      return rt.callU32(inst, "answer", input);
    };

    expect(await buildAndRun(7, 35)).toBe(42);
    expect(await buildAndRun(-5, 50)).toBe(45);
  });
});
