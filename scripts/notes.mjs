#!/usr/bin/env bun
/**
 * Build/query the notes and task knowledge graph.
 *
 * The schema is deliberately narrow: typed nodes and labelled edges.
 *
 *   bun run notes
 *   bun run notes -- --stale 30
 *   bun run notes -- --task api-foundations
 *   bun run notes -- --sql "select * from edges where predicate='depends-on'"
 *   bun run notes -- --graph
 */

import { Database } from "bun:sqlite";
import { execFileSync } from "node:child_process";
import {
  existsSync,
  mkdirSync,
  readFileSync,
  readdirSync,
  rmSync,
  statSync,
  writeFileSync,
} from "node:fs";
import { dirname, extname, join, normalize, relative, resolve, sep } from "node:path";

const ROOT = resolve(import.meta.dir, "..");
const DB = resolve(ROOT, "target/covalence-notes.sqlite");
const GRAPH = resolve(ROOT, "target/covalence-map.mmd");
const JSON_PATH = "docs/deps/covalence-map.json";
const MAP_STATIC_PATH = "apps/covalence-map/static/covalence-map.json";
const args = process.argv.slice(2);
const valueAfter = (flag) => {
  const index = args.indexOf(flag);
  return index < 0 ? undefined : args[index + 1];
};
const slash = (path) => path.split(sep).join("/");

function walk(dir) {
  if (!existsSync(dir)) return [];
  return readdirSync(dir, { withFileTypes: true }).flatMap((entry) => {
    const path = join(dir, entry.name);
    return entry.isDirectory() ? walk(path) : [path];
  });
}

const notePaths = walk(resolve(ROOT, "notes"))
  .filter((path) => extname(path) === ".md")
  .map((path) => slash(relative(ROOT, path)))
  .sort();
const noteSet = new Set(notePaths);
const todoItems = JSON.parse(
  readFileSync(resolve(ROOT, "docs/todos/todos.json"), "utf8"),
).items;
const todoSet = new Set(todoItems.map((item) => item.id));

// One git walk gives every note's latest committed timestamp.
const gitDates = new Map();
let timestamp = 0;
for (const line of execFileSync(
  "git",
  ["log", "--format=@@%ct", "--name-only", "--", "notes"],
  { cwd: ROOT, maxBuffer: 1 << 27 },
)
  .toString()
  .split("\n")) {
  if (line.startsWith("@@")) timestamp = Number(line.slice(2));
  else if (line.startsWith("notes/") && !gitDates.has(line)) gitDates.set(line, timestamp);
}

const nodes = [];
const edges = [];
const node = (id, kind, title, status, path, words, updated) =>
  nodes.push({ id, kind, title, status, path, words, updated });
const edge = (source, predicate, target, detail = null) =>
  edges.push({ source, predicate, target, detail });

for (const item of todoItems) {
  node(`todo:${item.id}`, "todo", item.summary, item.severity, item.path, 0, 0);
}

for (const path of notePaths) {
  const text = readFileSync(resolve(ROOT, path), "utf8");
  const id = `note:${path}`;
  const title = text.match(/^#\s+(.+)$/m)?.[1].trim() ?? path;
  const status = text.match(/^- \*\*Status:\*\*\s*(.+)$/im)?.[1].trim() ?? null;
  const words = text.trim() ? text.trim().split(/\s+/).length : 0;
  const updated =
    gitDates.get(path) ?? Math.floor(statSync(resolve(ROOT, path)).mtimeMs / 1000);
  node(id, "note", title, status, path, words, updated);

  for (const match of text.matchAll(/\[[^\]]*]\(([^)#]+)(?:#[^)]+)?\)/g)) {
    if (/^[a-z]+:/i.test(match[1])) continue;
    let target = slash(normalize(join(dirname(path), decodeURIComponent(match[1]))));
    if (existsSync(resolve(ROOT, target)) && statSync(resolve(ROOT, target)).isDirectory()) {
      target = `${target.replace(/\/$/, "")}/README.md`;
    }
    const kind = noteSet.has(target) ? "note" : "file";
    edge(id, "links-to", `${kind}:${target}`, existsSync(resolve(ROOT, target)) ? null : "missing");
  }
  for (const match of text.matchAll(
    /\b(?:TODO|FIXME|SKELETON|PERF)\(cov:([a-z0-9][a-z0-9.-]*)/g,
  )) {
    edge(id, "mentions", `todo:${match[1]}`, todoSet.has(match[1]) ? null : "missing");
  }
  for (const match of text.matchAll(
    /`((?:crates|scripts|docs|notes|apps|packages|extensions)\/[^`\s:]+)(?::(\d+))?`/g,
  )) {
    const target = match[1];
    const pattern = /[*?{}[\]]/.test(target);
    edge(
      id,
      "documents",
      `file:${target}`,
      pattern ? "pattern" : existsSync(resolve(ROOT, target)) ? match[2] : "missing",
    );
  }
}

for (const path of walk(resolve(ROOT, "notes/projects")).filter(
  (path) => extname(path) === ".toml",
)) {
  const project = Bun.TOML.parse(readFileSync(path, "utf8"));
  const id = `task:${project.id}`;
  node(id, "task", project.title, project.status, slash(relative(ROOT, path)), 0, 0);
  for (const dependency of project.depends_on ?? [])
    edge(id, "depends-on", `task:${dependency}`);
  for (const todo of project.todos ?? []) edge(id, "contains", `todo:${todo}`);
  for (const notePath of project.notes ?? []) edge(id, "described-by", `note:${notePath}`);
  for (const file of project.files ?? []) edge(id, "touches", `file:${file}`);
}

// References are nodes too, even when their current target is missing. This
// keeps queries total and makes broken/stale references visible in the graph.
const knownNodes = new Set(nodes.map((item) => item.id));
for (const item of edges) {
  if (knownNodes.has(item.target)) continue;
  const split = item.target.indexOf(":");
  const kind = item.target.slice(0, split);
  const title = item.target.slice(split + 1);
  node(item.target, kind, title, item.detail === "missing" ? "missing" : null, title, 0, 0);
  knownNodes.add(item.target);
}

nodes.sort((left, right) => left.id.localeCompare(right.id));
edges.sort(
  (left, right) =>
    left.source.localeCompare(right.source) ||
    left.predicate.localeCompare(right.predicate) ||
    left.target.localeCompare(right.target),
);
const artifact =
  JSON.stringify(
    {
      generatedBy: "scripts/notes.mjs",
      nodes,
      edges,
    },
    null,
    2,
  ) + "\n";
if (args.includes("--check")) {
  for (const path of [JSON_PATH, MAP_STATIC_PATH]) {
    const current = existsSync(resolve(ROOT, path))
      ? readFileSync(resolve(ROOT, path), "utf8")
      : "";
    if (current !== artifact) {
      console.error(`notes: ${path} is stale; run \`bun run notes\``);
      process.exit(1);
    }
  }
  console.error(`notes: up to date (${nodes.length} nodes, ${edges.length} edges)`);
  process.exit(0);
}
mkdirSync(dirname(resolve(ROOT, JSON_PATH)), { recursive: true });
writeFileSync(resolve(ROOT, JSON_PATH), artifact);
mkdirSync(dirname(resolve(ROOT, MAP_STATIC_PATH)), { recursive: true });
writeFileSync(resolve(ROOT, MAP_STATIC_PATH), artifact);

mkdirSync(dirname(DB), { recursive: true });
rmSync(DB, { force: true });
const db = new Database(DB, { create: true, strict: true });
db.exec(`
  CREATE TABLE nodes (
    id TEXT PRIMARY KEY, kind TEXT NOT NULL, title TEXT NOT NULL,
    status TEXT, path TEXT, words INTEGER NOT NULL, updated INTEGER NOT NULL
  ) STRICT;
  CREATE TABLE edges (
    source TEXT NOT NULL, predicate TEXT NOT NULL, target TEXT NOT NULL,
    detail TEXT, PRIMARY KEY (source, predicate, target)
  ) STRICT;
  CREATE INDEX edges_by_target ON edges(target, predicate);
`);
const putNode = db.prepare(`INSERT OR REPLACE INTO nodes VALUES (?,?,?,?,?,?,?)`);
const putEdge = db.prepare(`INSERT OR REPLACE INTO edges VALUES (?,?,?,?)`);
db.transaction(() => {
  for (const item of nodes) putNode.run(...Object.values(item));
  for (const item of edges) putEdge.run(...Object.values(item));
})();

const show = (rows) => (rows.length ? console.table(rows) : console.log("(none)"));
const sql = valueAfter("--sql");
const stale = valueAfter("--stale");
const task = valueAfter("--task");
if (sql) {
  show(db.query(sql).all());
} else if (stale) {
  show(
    db
      .query(
        `SELECT path,title,status,words,
          CAST((unixepoch()-updated)/86400 AS INTEGER) age_days
         FROM nodes WHERE kind='note' AND unixepoch()-updated >= ?*86400
         ORDER BY age_days DESC,words DESC`,
      )
      .all(Number(stale)),
  );
} else if (task) {
  show(
    db
      .query(
        `SELECT e.predicate,n.kind,n.id,n.title,n.status,e.detail
         FROM edges e LEFT JOIN nodes n ON n.id=e.target
         WHERE e.source=? ORDER BY e.predicate,n.id`,
      )
      .all(`task:${task}`),
  );
} else {
  const counts = Object.fromEntries(
    db.query(`SELECT kind,count(*) n FROM nodes GROUP BY kind`).all().map((r) => [r.kind, r.n]),
  );
  const missing = db.query(`SELECT count(*) n FROM edges WHERE detail='missing'`).get().n;
  console.log(
    `notes: notes=${counts.note ?? 0}, tasks=${counts.task ?? 0}, ` +
      `todos=${counts.todo ?? 0}, edges=${edges.length}, missing-targets=${missing}`,
  );
}

if (args.includes("--graph")) {
  const lines = ["flowchart LR"];
  for (const taskNode of nodes.filter((item) => item.kind === "task")) {
    lines.push(`  ${safe(taskNode.id)}["${escape(taskNode.title)}"]`);
  }
  for (const item of edges.filter((item) => item.predicate === "depends-on")) {
    lines.push(`  ${safe(item.target)} --> ${safe(item.source)}`);
  }
  for (const item of edges.filter((item) => item.predicate === "described-by")) {
    lines.push(`  ${safe(item.source)} -.-> ${safe(item.target)}["${escape(item.target.slice(5))}"]`);
  }
  writeFileSync(GRAPH, `${lines.join("\n")}\n`);
  console.log(`notes: wrote ${slash(relative(ROOT, GRAPH))}`);
}
db.close();

function safe(value) {
  return value.replace(/[^a-zA-Z0-9_]/g, "_");
}
function escape(value) {
  return value.replaceAll('"', "&quot;");
}
