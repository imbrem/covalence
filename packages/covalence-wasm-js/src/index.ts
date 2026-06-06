// JS host backend for the `cov:wasm/runtime@0.1.0` WIT interface.
//
// Mirrors the Rust impl in `crates/covalence-wasm/src/runtime.rs` —
// same conceptual surface (`compile` / `instantiate` / `callU32`)
// using the browser/Node `WebAssembly.*` APIs.
//
// MVP scope: **core WASM modules only.** Component bytes throw with a
// pointer at the deferred jco-based path (see
// `docs/design/proposals/wasm-runtime/`, Phase 3).

const WASM_MAGIC = Uint8Array.of(0x00, 0x61, 0x73, 0x6d); // "\0asm"

function isComponent(bytes: Uint8Array): boolean {
  // Both core modules and components start with "\0asm" + 4-byte
  // version. Core modules use version 0x01; components use higher
  // values (0x0a, 0x0d, …) with the "layer" bit set. Discriminator:
  // byte 5 == 0x01 → core module; anything else with the magic → component.
  if (bytes.length < 8) return false;
  for (let i = 0; i < 4; i++) if (bytes[i] !== WASM_MAGIC[i]) return false;
  return bytes[4] !== 0x01;
}

export class WasmRuntimeError extends Error {
  constructor(public readonly stage: "compile" | "instantiate" | "call", message: string) {
    super(`${stage}: ${message}`);
    this.name = "WasmRuntimeError";
  }
}

/** Opaque handle returned by `compile`. */
export class WasmComponent {
  constructor(public readonly module: WebAssembly.Module) {}
}

/** Opaque handle returned by `instantiate`. */
export class WasmInstance {
  constructor(public readonly instance: WebAssembly.Instance) {}
}

/** JS-side mirror of the `cov:wasm/runtime` host trait. */
export class Runtime {
  async compile(bytes: Uint8Array): Promise<WasmComponent> {
    if (isComponent(bytes)) {
      throw new WasmRuntimeError(
        "compile",
        "WASM component bytes are not supported in v0 (jco transpile path is Phase 3 follow-up)",
      );
    }
    try {
      // The TS lib types for WebAssembly.compile require ArrayBuffer-backed
      // buffer source; modern Uint8Array<ArrayBufferLike> doesn't satisfy
      // the constraint directly. Cast through `BufferSource`.
      const module = await WebAssembly.compile(bytes as BufferSource);
      return new WasmComponent(module);
    } catch (e) {
      throw new WasmRuntimeError("compile", (e as Error).message);
    }
  }

  async instantiate(component: WasmComponent): Promise<WasmInstance> {
    // MVP: stub all imports as throwing functions, mirroring the
    // wasmtime backend's `define_unknown_imports_as_traps`.
    const imports: WebAssembly.Imports = {};
    for (const imp of WebAssembly.Module.imports(component.module)) {
      const mod = (imports[imp.module] ??= {});
      mod[imp.name] = () => {
        throw new WasmRuntimeError(
          "instantiate",
          `unsatisfied import ${imp.module}.${imp.name} trapped`,
        );
      };
    }
    try {
      const instance = await WebAssembly.instantiate(component.module, imports);
      return new WasmInstance(instance);
    } catch (e) {
      throw new WasmRuntimeError("instantiate", (e as Error).message);
    }
  }

  callU32(instance: WasmInstance, name: string, arg: number): number {
    const exp = instance.instance.exports[name];
    if (typeof exp !== "function") {
      throw new WasmRuntimeError("call", `export not found or not a function: ${name}`);
    }
    try {
      // JS WebAssembly funcs accept/return number for i32; u32 is interpreted
      // by the caller via `>>> 0`.
      const out = (exp as (a: number) => number)(arg);
      return out >>> 0;
    } catch (e) {
      throw new WasmRuntimeError("call", (e as Error).message);
    }
  }
}

// NOTE: there is intentionally no `buildAddModule` here. Building WASM
// from JS would mean hand-rolling byte emission in TypeScript — that
// belongs in Rust. The Rust crate `covalence-wasm-build-guest` compiles
// `covalence_wasm::build::ModuleBuilder` to wasm32-unknown-unknown; load
// the resulting `.wasm` through this `Runtime`, call into it, and feed
// its output back through `Runtime.compile` for the metacircular loop.
// See `src/__fixtures__/build_guest.wasm` and `runtime.test.ts`.
