import { test, expect } from "bun:test";

test("python tests", async () => {
  const proc = Bun.spawn(
    ["bash", "-c", "source activate.sh && pytest tests/ -v"],
    {
      cwd: "crates/covalence-python",
      stdout: "inherit",
      stderr: "inherit",
    },
  );
  const code = await proc.exited;
  expect(code).toBe(0);
}, 300_000);
