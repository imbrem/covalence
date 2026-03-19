import { $ } from "bun";
import * as esbuild from "esbuild";
import { cpSync, mkdirSync } from "fs";
import { resolve } from "path";
import { createRequire } from "module";

const extDir = resolve(import.meta.dirname, "..");
const rootDir = resolve(extDir, "../..");
const require = createRequire(import.meta.url);

// WASM memory: 160 pages × 64 KB = 10 MB
// Must match createProcess({ initial: 160, maximum: 160 }) in extension.ts
const WASM_MEMORY_BYTES = 160 * 65536; // 10485760

// 1. Build WASM (WASI target with threads)
console.log("Building WASM...");
await $`cargo rustc -p covalence-lsp --target wasm32-wasip1-threads --release --bin covalence-lsp -- -Clink-arg=--initial-memory=${WASM_MEMORY_BYTES} -Clink-arg=--max-memory=${WASM_MEMORY_BYTES}`;

// 2. Copy WASM binary to dist
console.log("Copying WASM binary...");
mkdirSync(resolve(extDir, "dist"), { recursive: true });
cpSync(
  resolve(rootDir, "target/wasm32-wasip1-threads/release/covalence-lsp.wasm"),
  resolve(extDir, "dist/covalence-lsp.wasm"),
);

// Shared esbuild options
const shared: esbuild.BuildOptions = {
  entryPoints: [resolve(extDir, "src/extension.ts")],
  bundle: true,
  external: ["vscode"],
  target: "es2022",
  sourcemap: true,
  format: "cjs",
};

// 3. Bundle for desktop (Node)
console.log("Bundling desktop...");
await esbuild.build({
  ...shared,
  outfile: resolve(extDir, "dist/desktop/extension.js"),
  platform: "node",
});

// 4. Bundle for web (browser — alias vscode-languageclient/node to /browser)
console.log("Bundling web...");
const langClientDir = resolve(
  require.resolve("vscode-languageclient/package.json"),
  "..",
);
await esbuild.build({
  ...shared,
  outfile: resolve(extDir, "dist/web/extension.js"),
  platform: "browser",
  alias: {
    "vscode-languageclient/node": resolve(
      langClientDir,
      "lib/browser/main.js",
    ),
  },
});

console.log("Build complete.");
