/**
 * E2E integration tests for the web frontend + API.
 *
 * These tests verify that the built web app serves correctly alongside the API,
 * and that key routes and API interactions work end-to-end.
 *
 * Prerequisites: `cargo build -p covalence` and `bun run build:web`
 */
import { test, expect, beforeAll, afterAll } from "bun:test";
import * as fs from "fs";
import * as path from "path";
import * as os from "os";

let serverProc: ReturnType<typeof Bun.spawn> | null = null;
let baseUrl = "";
let port = 0;

beforeAll(async () => {
  const tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), "cov-e2e-test-"));
  const runtime = path.join(tmpDir, "runtime");
  const data = path.join(tmpDir, "data");
  const config = path.join(tmpDir, "config");
  const home = path.join(tmpDir, "home");
  for (const d of [runtime, data, config, home]) fs.mkdirSync(d, { recursive: true });

  // Find a free port
  const listener = Bun.listen({ hostname: "127.0.0.1", port: 0, socket: {
    data() {},
    open() {},
    close() {},
    error() {},
  }});
  port = listener.port;
  listener.stop();

  const covBin = path.resolve("target/debug/cov");
  serverProc = Bun.spawn([covBin, "serve", "--port", String(port)], {
    env: {
      ...process.env,
      XDG_RUNTIME_DIR: runtime,
      XDG_DATA_HOME: data,
      XDG_CONFIG_HOME: config,
      HOME: home,
    },
    stdout: "pipe",
    stderr: "pipe",
  });

  baseUrl = `http://127.0.0.1:${port}`;

  // Wait for server to be ready
  const deadline = Date.now() + 10_000;
  while (Date.now() < deadline) {
    try {
      const res = await fetch(`${baseUrl}/api/health`);
      if (res.ok) break;
    } catch { /* not ready yet */ }
    await Bun.sleep(100);
  }
});

afterAll(() => {
  if (serverProc) serverProc.kill();
});

test("server responds to health check", async () => {
  const res = await fetch(`${baseUrl}/api/health`);
  expect(res.ok).toBe(true);
  const json = await res.json();
  expect(json.status).toBe("ok");
}, 15_000);

test("index page is served (SPA fallback)", async () => {
  const res = await fetch(`${baseUrl}/`);
  // If static files are embedded, we get the SPA; otherwise a plain fallback
  expect(res.status).toBeLessThan(500);
  const text = await res.text();
  // Either the full SPA or the fallback message
  expect(text.length).toBeGreaterThan(0);
}, 15_000);

test("/view/{hash} route returns SPA page", async () => {
  const fakeHash = "a".repeat(64);
  const res = await fetch(`${baseUrl}/view/${fakeHash}`);
  // SPA: all routes serve index.html (200)
  expect(res.status).toBeLessThan(500);
}, 15_000);

test("full object workflow: store blob → info → view", async () => {
  // Store a blob via the object store
  const data = new TextEncoder().encode("e2e test content");
  const storeRes = await fetch(`${baseUrl}/api/objects/blob`, {
    method: "POST",
    body: data,
  });
  expect(storeRes.ok).toBe(true);
  const { hash } = (await storeRes.json()) as { hash: string };

  // Get object info
  const infoRes = await fetch(`${baseUrl}/api/objects/info/${hash}`);
  expect(infoRes.ok).toBe(true);
  const info = await infoRes.json();
  expect(info.kind).toBe("blob");
  expect(info.size).toBe(data.length);

  // Get object blob
  const blobRes = await fetch(`${baseUrl}/api/objects/blob/${hash}`);
  expect(blobRes.ok).toBe(true);
  const blobData = new Uint8Array(await blobRes.arrayBuffer());
  expect(new TextDecoder().decode(blobData)).toBe("e2e test content");
}, 15_000);

test("full tree workflow: store tree → info → ls", async () => {
  // Store a child blob via the object store
  const childRes = await fetch(`${baseUrl}/api/objects/blob`, {
    method: "POST",
    body: new TextEncoder().encode("child data"),
  });
  const { hash: childHash } = (await childRes.json()) as { hash: string };

  // Store a tree
  const treeBody = JSON.stringify([
    { name: "readme.md", mode: "regular", hash: childHash },
    { name: "src", mode: "dir", hash: childHash },
  ]);
  const treeRes = await fetch(`${baseUrl}/api/objects/tree/json`, {
    method: "POST",
    headers: { "Content-Type": "application/json" },
    body: treeBody,
  });
  expect(treeRes.ok).toBe(true);
  const { hash: treeHash } = (await treeRes.json()) as { hash: string };

  // Info
  const infoRes = await fetch(`${baseUrl}/api/objects/info/${treeHash}`);
  expect(infoRes.ok).toBe(true);
  const info = await infoRes.json();
  expect(info.kind).toBe("tree");

  // List entries
  const lsRes = await fetch(`${baseUrl}/api/objects/tree/${treeHash}/ls`);
  expect(lsRes.ok).toBe(true);
  const entries = await lsRes.json();
  expect(entries).toHaveLength(2);
  const names = entries.map((e: any) => e.name).sort();
  expect(names).toEqual(["readme.md", "src"]);
}, 15_000);

test("info returns 404 for missing object", async () => {
  const missingHash = "0".repeat(64);
  const res = await fetch(`${baseUrl}/api/objects/info/${missingHash}`);
  expect(res.status).toBe(404);
}, 15_000);
