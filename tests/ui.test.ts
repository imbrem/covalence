import { test, expect } from "bun:test";

test("covalence-ui vitest", async () => {
  const proc = Bun.spawn(["bun", "run", "test"], {
    cwd: "packages/covalence-ui",
    stdout: "inherit",
    stderr: "inherit",
  });
  const code = await proc.exited;
  expect(code).toBe(0);
}, 300_000);
