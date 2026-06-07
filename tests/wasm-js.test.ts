import { test, expect, beforeAll } from "bun:test";
import { existsSync } from "fs";

beforeAll(async () => {
  // Same install-on-cold-checkout dance as ui.test.ts.
  if (!existsSync("packages/covalence-wasm-js/node_modules/.bin/vitest")) {
    const install = Bun.spawn(["bun", "install"], {
      stdout: "inherit",
      stderr: "inherit",
    });
    const code = await install.exited;
    if (code !== 0) throw new Error(`bun install failed with code ${code}`);
  }
}, 300_000);

test("covalence-wasm-js vitest", async () => {
  const proc = Bun.spawn(["bun", "run", "test"], {
    cwd: "packages/covalence-wasm-js",
    stdout: "inherit",
    stderr: "inherit",
  });
  const code = await proc.exited;
  expect(code).toBe(0);
}, 300_000);
