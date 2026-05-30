import { test, expect, beforeAll, afterAll } from "bun:test";
import { CovalenceClient } from "covalence-client";
import * as fs from "fs";
import * as path from "path";
import * as os from "os";

// ---------------------------------------------------------------------------
// Test harness: spawn `cov serve --socket-only` with isolated XDG dirs
// ---------------------------------------------------------------------------

let serverProc: ReturnType<typeof Bun.spawn> | null = null;
let socketPath = "";
let client: CovalenceClient;

function findSocket(dir: string, deadline: number): string {
  const socketsDir = path.join(dir, "covalence", "sockets");
  while (Date.now() < deadline) {
    try {
      for (const entry of fs.readdirSync(socketsDir)) {
        if (entry.endsWith(".sock")) {
          return path.join(socketsDir, entry);
        }
      }
    } catch { /* dir doesn't exist yet */ }
    Bun.sleepSync(50);
  }
  throw new Error(`Timed out waiting for socket in ${socketsDir}`);
}

beforeAll(() => {
  const tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), "cov-api-test-"));
  const runtime = path.join(tmpDir, "runtime");
  const data = path.join(tmpDir, "data");
  const config = path.join(tmpDir, "config");
  const home = path.join(tmpDir, "home");
  for (const d of [runtime, data, config, home]) fs.mkdirSync(d, { recursive: true });

  const covBin = path.resolve("target/debug/cov");
  serverProc = Bun.spawn([covBin, "serve", "--socket-only"], {
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

  socketPath = findSocket(runtime, Date.now() + 10_000);

  // The TS client uses fetch over HTTP, not Unix sockets. We need a TCP server.
  // Instead, test using raw fetch over Unix socket via Bun's unix socket support.
  // For simplicity, we'll test using direct fetch to the socket.
  client = new CovalenceClient({
    baseUrl: "",
    fetch: (input: string | URL | Request, init?: RequestInit) => {
      const url = typeof input === "string" ? input : input instanceof URL ? input.href : input.url;
      return fetch(`unix://${socketPath}${url}`, init);
    },
  });
});

afterAll(() => {
  if (serverProc) {
    serverProc.kill();
  }
});

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/** Store blob via the object store endpoint (not the kernel blob store). */
async function storeObjectBlob(data: Uint8Array): Promise<string> {
  const res = await fetch(`unix://${socketPath}/api/objects/blob`, {
    method: "POST",
    body: data,
  });
  if (!res.ok) throw new Error(`store object blob: ${res.status}`);
  const json = (await res.json()) as { hash: string };
  return json.hash;
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

test("health endpoint responds", async () => {
  const health = await client.health();
  expect(health.status).toBe("ok");
}, 15_000);

test("store blob and get object info", async () => {
  const data = new TextEncoder().encode("api test blob");
  const hash = await storeObjectBlob(data);
  expect(hash).toHaveLength(64);

  const info = await client.objectInfo(hash);
  expect(info).not.toBeNull();
  expect(info!.kind).toBe("blob");
  expect(info!.size).toBe(data.length);
}, 15_000);

test("object info returns null for missing hash", async () => {
  const missing = "0".repeat(64);
  const info = await client.objectInfo(missing);
  expect(info).toBeNull();
}, 15_000);

test("get object blob returns data", async () => {
  const text = "blob content test";
  const data = new TextEncoder().encode(text);
  const hash = await storeObjectBlob(data);

  const blob = await client.getObjectBlob(hash);
  expect(blob).not.toBeNull();
  expect(new TextDecoder().decode(blob!)).toBe(text);
}, 15_000);

test("store tree via JSON and list entries", async () => {
  // Store a blob first via the object store
  const blobData = new TextEncoder().encode("tree child");
  const blobHash = await storeObjectBlob(blobData);

  // Store a tree via the JSON API
  const treeBody = JSON.stringify([
    { name: "hello.txt", mode: "regular", hash: blobHash },
  ]);
  const res = await fetch(`unix://${socketPath}/api/objects/tree/json`, {
    method: "POST",
    headers: { "Content-Type": "application/json" },
    body: treeBody,
  });
  expect(res.ok).toBe(true);
  const { hash: treeHash } = (await res.json()) as { hash: string };

  // Verify info
  const info = await client.objectInfo(treeHash);
  expect(info).not.toBeNull();
  expect(info!.kind).toBe("tree");

  // List entries
  const entries = await client.treeLs(treeHash);
  expect(entries).toHaveLength(1);
  expect(entries[0].name).toBe("hello.txt");
  expect(entries[0].mode).toBe("regular");
  expect(entries[0].hash).toBe(blobHash);
}, 15_000);
