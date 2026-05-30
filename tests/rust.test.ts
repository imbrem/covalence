import { test, expect } from "bun:test";

test("cargo test", async () => {
  const proc = Bun.spawn(["cargo", "test"], {
    stdout: "inherit",
    stderr: "inherit",
  });
  const code = await proc.exited;
  expect(code).toBe(0);
}, 300_000);
