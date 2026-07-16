import { test, expect, beforeAll } from "bun:test";
import { existsSync } from "fs";

beforeAll(async () => {
  // Ensure JS dependencies are installed (mirrors the venv activation that
  // python.test.ts gets from activate.sh). Without this, fresh worktrees fail
  // with `vitest: command not found`.
  if (!existsSync("apps/covalence-web/node_modules/.bin/vitest")) {
    const install = Bun.spawn(["bun", "install"], {
      stdout: "inherit",
      stderr: "inherit",
    });
    const code = await install.exited;
    if (code !== 0) throw new Error(`bun install failed with code ${code}`);
  }
}, 300_000);

test("covalence-web vitest", async () => {
  const proc = Bun.spawn(["bun", "run", "test"], {
    cwd: "apps/covalence-web",
    stdout: "inherit",
    stderr: "inherit",
  });
  const code = await proc.exited;
  expect(code).toBe(0);
}, 300_000);
