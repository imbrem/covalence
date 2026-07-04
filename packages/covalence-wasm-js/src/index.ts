// JS host backend for the `cov:wasm/runtime@0.1.0` WIT interface.
//
// Mirrors the Rust impl in `crates/lib/wasm/core/src/runtime.rs` —
// same conceptual surface (`compile` / `instantiate` / `callU32`)
// using the browser/Node `WebAssembly.*` APIs.
//
// Core WASM modules: native `WebAssembly.*`.
// WASM components: `@bytecodealliance/jco` transpiles to self-contained
// JS at runtime; we load it via a `data:` URL and call its
// `instantiate(getCoreModule, imports)` entry. Both code paths converge
// on a single `WasmInstance` shape with a uniform `callU32` interface.

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

/**
 * Opaque handle returned by `compile`. Internally either a core module
 * (run via `WebAssembly.instantiate`) or a jco-transpiled component
 * (run via its generated `instantiate` function).
 */
export class WasmComponent {
  constructor(
    readonly kind: "module" | "component",
    /** Set when kind === "module". */
    readonly module?: WebAssembly.Module,
    /** Set when kind === "component". */
    readonly componentInstantiate?: ComponentInstantiateFn,
    /** Set when kind === "component". Compiled `<name>.core.wasm`. */
    readonly componentCoreModules?: Record<string, WebAssembly.Module>,
  ) {}
}

/**
 * Opaque handle returned by `instantiate`. Exposes the underlying
 * exports namespace so callers can poke at memory / call arbitrary
 * exports beyond `callU32`.
 */
export class WasmInstance {
  constructor(
    /**
     * For core-module instances, the native `WebAssembly.Instance`.
     * For component instances, the bag of exports jco gave us — a
     * plain object whose keys are export names. Both have functions
     * callable as `(...args)` and (for core modules) a `memory` key.
     */
    public readonly instance: WebAssembly.Instance | ComponentExports,
  ) {}
}

/** jco-generated component `instantiate` signature (sync mode). */
type ComponentInstantiateFn = (
  getCoreModule: (name: string) => WebAssembly.Module,
  imports: Record<string, unknown>,
  instantiateCore?: (
    module: WebAssembly.Module,
    importObject?: WebAssembly.Imports,
  ) => WebAssembly.Instance,
) => ComponentExports;

type ComponentExports = Record<string, unknown>;

/** JS-side mirror of the `cov:wasm/runtime` host trait. */
export class Runtime {
  async compile(bytes: Uint8Array): Promise<WasmComponent> {
    if (isComponent(bytes)) {
      return compileComponent(bytes);
    }
    try {
      // TS-lib types want ArrayBuffer-backed source; cast through BufferSource.
      const module = await WebAssembly.compile(bytes as BufferSource);
      return new WasmComponent("module", module);
    } catch (e) {
      throw new WasmRuntimeError("compile", (e as Error).message);
    }
  }

  async instantiate(component: WasmComponent): Promise<WasmInstance> {
    if (component.kind === "component") {
      return instantiateComponent(component);
    }
    // Core module — stub unknown imports as traps (mirrors wasmtime's
    // `define_unknown_imports_as_traps`).
    const imports: WebAssembly.Imports = {};
    for (const imp of WebAssembly.Module.imports(component.module!)) {
      const mod = (imports[imp.module] ??= {});
      mod[imp.name] = () => {
        throw new WasmRuntimeError(
          "instantiate",
          `unsatisfied import ${imp.module}.${imp.name} trapped`,
        );
      };
    }
    try {
      const instance = await WebAssembly.instantiate(component.module!, imports);
      return new WasmInstance(instance);
    } catch (e) {
      throw new WasmRuntimeError("instantiate", (e as Error).message);
    }
  }

  callU32(instance: WasmInstance, name: string, arg: number): number {
    // Both `WebAssembly.Instance.exports` and component export bags
    // present functions under string keys — uniform lookup.
    const exports = (instance.instance as { exports?: Record<string, unknown> })
      .exports ?? (instance.instance as Record<string, unknown>);
    const exp = exports[name];
    if (typeof exp !== "function") {
      throw new WasmRuntimeError("call", `export not found or not a function: ${name}`);
    }
    try {
      const out = (exp as (a: number) => number)(arg);
      return out >>> 0;
    } catch (e) {
      throw new WasmRuntimeError("call", (e as Error).message);
    }
  }
}

// ---------------------------------------------------------------------------
// Component-mode compile/instantiate via jco.
// ---------------------------------------------------------------------------

async function compileComponent(bytes: Uint8Array): Promise<WasmComponent> {
  let transpiled;
  try {
    // jco is heavy (~MB); dynamic import keeps it out of the
    // core-modules-only hot path.
    const { transpile } = await import("@bytecodealliance/jco");
    transpiled = await transpile(bytes, {
      name: "component",
      instantiation: "sync",
    });
  } catch (e) {
    throw new WasmRuntimeError(
      "compile",
      `jco transpile failed: ${(e as Error).message}`,
    );
  }

  const jsBytes = transpiled.files["component.js"];
  if (!jsBytes) {
    throw new WasmRuntimeError("compile", "jco produced no component.js");
  }

  // Compile every `*.core.wasm` upfront so instantiation is synchronous.
  const coreModules: Record<string, WebAssembly.Module> = {};
  for (const [name, content] of Object.entries(transpiled.files)) {
    if (name.endsWith(".core.wasm")) {
      try {
        coreModules[name] = await WebAssembly.compile(content as BufferSource);
      } catch (e) {
        throw new WasmRuntimeError(
          "compile",
          `failed to compile ${name}: ${(e as Error).message}`,
        );
      }
    }
  }

  // Load the jco-generated module via a data: URL so we don't touch the
  // filesystem (and don't fight Vite's static analysis).
  let mod: { instantiate: ComponentInstantiateFn };
  try {
    const dataUrl =
      "data:text/javascript;base64," +
      Buffer.from(jsBytes).toString("base64");
    mod = await import(/* @vite-ignore */ dataUrl);
  } catch (e) {
    throw new WasmRuntimeError(
      "compile",
      `loading transpiled component js failed: ${(e as Error).message}`,
    );
  }
  if (typeof mod.instantiate !== "function") {
    throw new WasmRuntimeError(
      "compile",
      "transpiled component js has no `instantiate` export",
    );
  }
  return new WasmComponent("component", undefined, mod.instantiate, coreModules);
}

function instantiateComponent(component: WasmComponent): WasmInstance {
  if (!component.componentInstantiate || !component.componentCoreModules) {
    throw new WasmRuntimeError(
      "instantiate",
      "component handle missing transpiled artifacts",
    );
  }
  const getCoreModule = (name: string): WebAssembly.Module => {
    const m = component.componentCoreModules![name];
    if (!m) {
      throw new WasmRuntimeError(
        "instantiate",
        `jco asked for unknown core module: ${name}`,
      );
    }
    return m;
  };
  try {
    // No host imports yet — the deferred-import side of the WIT plan
    // (and the kernel's eventual `cov:wasm/host` interface) come later.
    const exports = component.componentInstantiate(getCoreModule, {});
    return new WasmInstance(exports);
  } catch (e) {
    throw new WasmRuntimeError("instantiate", (e as Error).message);
  }
}

// NOTE: there is intentionally no `buildAddModule` here. Building WASM
// from JS would mean hand-rolling byte emission in TypeScript — that
// belongs in Rust. The Rust crate `covalence-wasm-build-guest` compiles
// `covalence_wasm::build::ModuleBuilder` to wasm32-unknown-unknown; load
// the resulting `.wasm` through this `Runtime`, call into it, and feed
// its output back through `Runtime.compile` for the metacircular loop.
// See `src/__fixtures__/build_guest.wasm` and `runtime.test.ts`.
