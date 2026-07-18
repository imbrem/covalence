#!/usr/bin/env bun
/**
 * Build and query Covalence's source-local open-work database.
 *
 * Authored markers live beside the code:
 *
 *   // TODO(cov:hol-script-spans, severe): Thread source spans through errors.
 *   // FIXME(cov:wasm-listn, major): Preserve parametric ListN lengths.
 *   // SKELETON(cov:sat-lrat-replay, severe): Replay LRAT into resolution.
 *
 * Stable markers require a unique lowercase ID. Unstructured comments are not
 * authoritative: convert real work to a `cov:` marker so IDs survive moves.
 *
 * Usage:
 *   bun run todos                         regenerate JSON + SQLite, print summary
 *   bun run todos -- --list              print matching items
 *   bun run todos -- --list --crate covalence-init --severity severe
 *   bun run todos -- --list --search "source spans" --format json
 *   bun run todos:check                   verify the checked-in JSON is current
 */

import { Database } from "bun:sqlite";
import { execFileSync } from "node:child_process";
import {
  existsSync,
  mkdirSync,
  readFileSync,
  rmSync,
  writeFileSync,
} from "node:fs";
import { dirname, relative, resolve, sep } from "node:path";

const ROOT = resolve(import.meta.dir, "..");
const JSON_OUT = "docs/todos/todos.json";
const DB_OUT = "target/covalence-todos.sqlite";
const args = process.argv.slice(2);
const CHECK = args.includes("--check");
const LIST = args.includes("--list");
const FORMAT = valueAfter("--format") ?? "table";
const FILTER_CRATE = valueAfter("--crate");
const FILTER_SEVERITY = valueAfter("--severity");
const FILTER_KIND = valueAfter("--kind");
const SEARCH = valueAfter("--search")?.toLowerCase();

function valueAfter(flag) {
  const i = args.indexOf(flag);
  return i >= 0 ? args[i + 1] : undefined;
}

const SOURCE_EXTENSIONS = new Set([
  ".c",
  ".cc",
  ".cov",
  ".cpp",
  ".css",
  ".h",
  ".hpp",
  ".html",
  ".js",
  ".json",
  ".jsx",
  ".k",
  ".md",
  ".mjs",
  ".py",
  ".rs",
  ".sh",
  ".svelte",
  ".toml",
  ".ts",
  ".tsx",
  ".wat",
  ".wit",
  ".yaml",
  ".yml",
]);
const EXCLUDED_PREFIXES = [
  ".claude/worktrees/",
  ".git/",
  ".worktrees/",
  ".agents/",
  ".claude/",
  "assets/",
  "docs/",
  "notes/",
  "notes/vibes/backup/",
  "target/",
];
const EXCLUDED_FILES = new Set([
  "Cargo.lock",
  "AGENTS.md",
  "CLAUDE.md",
  "README.md",
  "bun.lock",
  "SKELETONS.md",
  "todos.mjs",
]);

function extension(path) {
  const i = path.lastIndexOf(".");
  return i < 0 ? "" : path.slice(i);
}

function files() {
  const out = execFileSync("rg", ["--files", "--hidden"], {
    cwd: ROOT,
    maxBuffer: 1 << 28,
  }).toString();
  return out
    .split("\n")
    .filter(Boolean)
    .filter((p) => SOURCE_EXTENSIONS.has(extension(p)))
    .filter((p) => !EXCLUDED_FILES.has(p.split("/").at(-1)))
    .filter((p) => !EXCLUDED_PREFIXES.some((prefix) => p.startsWith(prefix)))
    .sort();
}

const metadata = JSON.parse(
  execFileSync("cargo", ["metadata", "--format-version", "1", "--no-deps"], {
    cwd: ROOT,
    maxBuffer: 1 << 28,
  }).toString(),
);
const crateDirs = metadata.packages
  .map((p) => [
    relative(ROOT, dirname(p.manifest_path)).split(sep).join("/"),
    p.name,
  ])
  .sort((a, b) => b[0].length - a[0].length);

function crateOf(path) {
  for (const [dir, name] of crateDirs) {
    if (path === dir || path.startsWith(`${dir}/`)) return name;
  }
  return null;
}

const structured =
  /\b(TODO|FIXME|SKELETON|PERF)\(cov:([a-z0-9][a-z0-9.-]*)(?:,\s*(severe|major|minor))?\):\s*(.+?)\s*(?:\*\/)?$/;
const items = [];
const seenIds = new Map();

for (const path of files()) {
  const lines = readFileSync(resolve(ROOT, path), "utf8").split("\n");
  lines.forEach((line, index) => {
    let match = line.match(structured);
    let item;
    if (match) {
      const [, kind, id, severity = "major", summary] = match;
      item = {
        id,
        kind,
        severity,
        summary: cleanSummary(summary),
        structured: true,
        path,
        line: index + 1,
        crate: crateOf(path),
      };
    } else return;
    if (!item.summary || item.summary.includes("TODO(cov:")) return;
    if (seenIds.has(item.id)) {
      const first = seenIds.get(item.id);
      throw new Error(
        `duplicate TODO id ${item.id}: ${first.path}:${first.line} and ${path}:${index + 1}`,
      );
    }
    seenIds.set(item.id, item);
    items.push(item);
  });
}

function cleanSummary(summary) {
  return summary
    .replace(/\s+\*\/\s*$/, "")
    .replace(/[`*_]+/g, "")
    .trim();
}

items.sort(
  (a, b) =>
    a.id.localeCompare(b.id) ||
    a.path.localeCompare(b.path) ||
    a.line - b.line,
);

const artifact =
  JSON.stringify(
    {
      generatedBy: "scripts/todos.mjs",
      note: "Generated from source-local TODO/FIXME/SKELETON/HACK/XXX markers. Edit the source marker, then run `bun run todos`.",
      count: items.length,
      structured: items.length,
      items,
    },
    null,
    2,
  ) + "\n";

if (CHECK) {
  if (!existsSync(resolve(ROOT, JSON_OUT))) {
    console.error(`todos: missing ${JSON_OUT}; run \`bun run todos\``);
    process.exit(1);
  }
  if (readFileSync(resolve(ROOT, JSON_OUT), "utf8") !== artifact) {
    console.error(`todos: ${JSON_OUT} is stale; run \`bun run todos\``);
    process.exit(1);
  }
  console.error(`todos: up to date (${items.length} items)`);
  process.exit(0);
}

mkdirSync(resolve(ROOT, dirname(JSON_OUT)), { recursive: true });
writeFileSync(resolve(ROOT, JSON_OUT), artifact);
writeDatabase(items);

const filtered = items.filter(
  (item) =>
    (!FILTER_CRATE || item.crate === FILTER_CRATE) &&
    (!FILTER_SEVERITY || item.severity === FILTER_SEVERITY) &&
    (!FILTER_KIND || item.kind.toLowerCase() === FILTER_KIND.toLowerCase()) &&
    (!SEARCH ||
      item.id.toLowerCase().includes(SEARCH) ||
      item.summary.toLowerCase().includes(SEARCH) ||
      item.path.toLowerCase().includes(SEARCH)),
);

if (LIST) {
  if (FORMAT === "json") {
    console.log(JSON.stringify(filtered, null, 2));
  } else {
    for (const item of filtered) {
      const owner = item.crate ?? "-";
      console.log(
        `${item.severity.padEnd(6)} ${item.kind.padEnd(8)} ${item.id.padEnd(45)} ${owner}`,
      );
      console.log(`  ${item.path}:${item.line}  ${item.summary}`);
    }
  }
} else {
  const counts = Object.groupBy(items, (item) => item.severity);
  console.error(
    `todos: wrote ${JSON_OUT} + ${DB_OUT} (${items.length} items: ` +
      `severe=${counts.severe?.length ?? 0}, major=${counts.major?.length ?? 0}, ` +
      `minor=${counts.minor?.length ?? 0})`,
  );
}

function writeDatabase(rows) {
  const path = resolve(ROOT, DB_OUT);
  mkdirSync(dirname(path), { recursive: true });
  rmSync(path, { force: true });
  const db = new Database(path, { create: true, strict: true });
  db.exec(`
    PRAGMA journal_mode = WAL;
    CREATE TABLE items (
      id         TEXT PRIMARY KEY,
      kind       TEXT NOT NULL,
      severity   TEXT NOT NULL,
      summary    TEXT NOT NULL,
      structured INTEGER NOT NULL CHECK (structured IN (0, 1)),
      path       TEXT NOT NULL,
      line       INTEGER NOT NULL,
      crate      TEXT
    ) STRICT;
    CREATE INDEX items_by_crate ON items(crate, severity);
    CREATE INDEX items_by_path ON items(path, line);
  `);
  const insert = db.prepare(`
    INSERT INTO items (id, kind, severity, summary, structured, path, line, crate)
    VALUES ($id, $kind, $severity, $summary, $structured, $path, $line, $crate)
  `);
  const transaction = db.transaction((all) => {
    for (const item of all) {
      insert.run({ ...item, structured: item.structured ? 1 : 0 });
    }
  });
  transaction(rows);
  db.close();
}
