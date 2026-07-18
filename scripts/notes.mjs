#!/usr/bin/env bun
/**
 * Build/query the notes and task knowledge graph.
 *
 * The schema is deliberately narrow: typed nodes and labelled edges.
 *
 *   bun run notes
 *   bun run notes -- --stale 30
 *   bun run notes -- --task api-foundations
 *   bun run notes -- --term T0001
 *   bun run notes -- --note N0001
 *   bun run notes -- --actor agent:forester-provenance-research
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
const TODO_DB = resolve(ROOT, "target/covalence-todos.sqlite");
if (!existsSync(TODO_DB)) {
  throw new Error("missing derived TODO index; run `bun run todos` before `bun run notes`");
}
const todoDb = new Database(TODO_DB, { readonly: true, strict: true });
const todoItems = todoDb
  .query(
    `SELECT id,kind,severity,summary,structured,path,line,crate
     FROM items ORDER BY id,path,line`,
  )
  .all();
todoDb.close();
const todoSet = new Set(todoItems.map((item) => item.id));

// One git walk gives every note's latest committed timestamp.
const gitRevisions = new Map();
let timestamp = 0;
let commit = null;
for (const line of execFileSync(
  "git",
  ["log", "--format=@@%H%x09%ct", "--name-only", "--", "notes"],
  { cwd: ROOT, maxBuffer: 1 << 27 },
)
  .toString()
  .split("\n")) {
  if (line.startsWith("@@")) {
    [commit, timestamp] = line.slice(2).split("\t");
    timestamp = Number(timestamp);
  } else if (line.startsWith("notes/") && !gitRevisions.has(line)) {
    gitRevisions.set(line, { commit, committedAt: timestamp });
  }
}

const nodes = [];
const edges = [];
const noteMetadata = [];
const actors = new Map();
const contributions = [];
const sources = new Map();
const citations = [];
const reviews = [];
const revisions = [];
const node = (id, kind, title, status, path, words, updated) =>
  nodes.push({ id, kind, title, status, path, words, updated });
const edge = (source, predicate, target, detail = null) =>
  edges.push({ source, predicate, target, detail });
const normalizeNoteStatus = (status) => {
  const known = ["draft", "in-review", "accepted", "superseded", "parked"];
  return typeof status === "string" && known.includes(status.toLowerCase())
    ? status.toLowerCase()
    : "unparsed legacy";
};
const REVIEW_STATES = new Set(["unreviewed", "checked", "accepted", "superseded"]);

function parseMetadata(path, text) {
  if (!text.startsWith("+++\n")) return null;
  const end = text.indexOf("\n+++\n", 4);
  if (end < 0) throw new Error(`${path}: unterminated TOML note frontmatter`);
  let value;
  try {
    value = Bun.TOML.parse(text.slice(4, end));
  } catch (error) {
    throw new Error(`${path}: invalid TOML note frontmatter: ${error.message}`);
  }
  for (const field of ["id", "status", "review"]) {
    if (typeof value[field] !== "string" || !value[field])
      throw new Error(`${path}: note frontmatter requires string ${field}`);
  }
  if (!/^N[0-9A-Z]{4,}$/.test(value.id))
    throw new Error(`${path}: note id must be an opaque base-36 address such as N0001`);
  if (!REVIEW_STATES.has(value.review))
    throw new Error(`${path}: unknown review state ${JSON.stringify(value.review)}`);
  if (normalizeNoteStatus(value.status) === "unparsed legacy")
    throw new Error(`${path}: unknown note status ${JSON.stringify(value.status)}`);
  return value;
}

function registerActor(actor, path) {
  if (typeof actor !== "string" || !/^(human|agent):[a-z0-9][a-z0-9._/-]*$/i.test(actor))
    throw new Error(`${path}: actor must be a stable human:… or agent:… identifier`);
  const kind = actor.slice(0, actor.indexOf(":")).toLowerCase();
  actors.set(actor, { id: actor, kind, displayName: actor.slice(actor.indexOf(":") + 1) });
}

for (const item of todoItems) {
  node(`todo:${item.id}`, "todo", item.summary, item.severity, item.path, 0, 0);
}

const termDefinitions = new Map();
for (const path of notePaths) {
  const text = readFileSync(resolve(ROOT, path), "utf8");
  const termId = text.match(/^- \*\*Term ID:\*\*\s*(T\d{4,})\s*$/im)?.[1];
  if (!termId) continue;
  if (termDefinitions.has(termId)) {
    throw new Error(`duplicate term definition ${termId}: ${termDefinitions.get(termId)} and ${path}`);
  }
  const title = text.match(/^#\s+(.+)$/m)?.[1].trim() ?? termId;
  termDefinitions.set(termId, path);
  node(`term:${termId}`, "term", title, "defined", path, 0, 0);
  edge(`term:${termId}`, "defined-by", `note:${path}`);
}

for (const path of notePaths) {
  const text = readFileSync(resolve(ROOT, path), "utf8");
  const id = `note:${path}`;
  const metadata = parseMetadata(path, text);
  if (!metadata)
    throw new Error(`${path}: every note requires TOML metadata; run the metadata migration`);
  const title = text.match(/^#\s+(.+)$/m)?.[1].trim() ?? path;
  const status = normalizeNoteStatus(metadata?.status);
  const words = text.trim() ? text.trim().split(/\s+/).length : 0;
  const revision = gitRevisions.get(path);
  const updated = revision?.committedAt ?? Math.floor(statSync(resolve(ROOT, path)).mtimeMs / 1000);
  node(id, "note", title, status, path, words, updated);

  if (metadata) {
    if (noteMetadata.some((item) => item.stableId === metadata.id))
      throw new Error(`${path}: duplicate stable note ID ${metadata.id}`);
    noteMetadata.push({
      noteId: id,
      stableId: metadata.id,
      review: metadata.review,
      format: "covalence-toml-v1",
    });
    for (const [ordinal, contribution] of (metadata.contributions ?? []).entries()) {
      for (const field of ["role", "actor", "at", "source", "agent", "harness"]) {
        if (typeof contribution[field] !== "string" || !contribution[field])
          throw new Error(`${path}: contribution ${ordinal + 1} requires string ${field}`);
      }
      registerActor(contribution.actor, path);
      contributions.push({
        noteId: id,
        actorId: contribution.actor,
        role: contribution.role,
        contributedAt: contribution.at,
        source: contribution.source,
        agent: contribution.agent,
        harness: contribution.harness,
        ordinal,
      });
      edge(id, "contributed-by", `actor:${contribution.actor}`, contribution.role);
    }
    for (const source of metadata.sources ?? []) {
      for (const field of ["id", "kind", "target"]) {
        if (typeof source[field] !== "string" || !source[field])
          throw new Error(`${path}: each source requires string ${field}`);
      }
      const normalized = {
        id: source.id,
        kind: source.kind,
        target: source.target,
        version: source.version ?? null,
        accessedAt: source.accessed ?? null,
      };
      const previous = sources.get(source.id);
      if (previous && JSON.stringify(previous) !== JSON.stringify(normalized))
        throw new Error(`${path}: source ${source.id} conflicts with an earlier definition`);
      sources.set(source.id, normalized);
      citations.push({
        noteId: id,
        sourceId: source.id,
        locator: source.locator ?? null,
        purpose: source.purpose ?? null,
        ordinal: citations.filter((item) => item.noteId === id).length,
      });
      edge(id, "cites", `source:${source.id}`);
    }
    for (const [ordinal, review] of (metadata.reviews ?? []).entries()) {
      for (const field of ["actor", "verdict", "at"]) {
        if (typeof review[field] !== "string" || !review[field])
          throw new Error(`${path}: review ${ordinal + 1} requires string ${field}`);
      }
      if (!REVIEW_STATES.has(review.verdict))
        throw new Error(`${path}: unknown review verdict ${JSON.stringify(review.verdict)}`);
      registerActor(review.actor, path);
      reviews.push({
        noteId: id,
        actorId: review.actor,
        verdict: review.verdict,
        reviewedAt: review.at,
        comment: review.comment ?? null,
        ordinal,
      });
      edge(id, "reviewed-by", `actor:${review.actor}`, review.verdict);
    }
  }
  if (revision) revisions.push({ noteId: id, commit: revision.commit, committedAt: revision.committedAt });

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
  for (const match of text.matchAll(/\[\[term:(T\d{4,})\]\]/g)) {
    edge(
      id,
      "uses-term",
      `term:${match[1]}`,
      termDefinitions.has(match[1]) ? null : "missing",
    );
  }
}

for (const actor of actors.values())
  node(`actor:${actor.id}`, "actor", actor.displayName, actor.kind, null, 0, 0);
for (const source of sources.values())
  node(`source:${source.id}`, "source", source.target, source.kind, source.target, 0, 0);

for (const path of walk(resolve(ROOT, "notes/projects")).filter(
  (path) => extname(path) === ".toml",
)) {
  const project = Bun.TOML.parse(readFileSync(path, "utf8"));
  const id = `task:${project.id}`;
  node(id, "task", project.title, project.status, slash(relative(ROOT, path)), 0, 0);
  if (project.parent) edge(id, "part-of", `task:${project.parent}`);
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
  CREATE TABLE note_metadata (
    note_id TEXT PRIMARY KEY REFERENCES nodes(id), stable_id TEXT NOT NULL UNIQUE,
    review TEXT NOT NULL, format TEXT NOT NULL
  ) STRICT;
  CREATE TABLE actors (
    id TEXT PRIMARY KEY, kind TEXT NOT NULL, display_name TEXT NOT NULL
  ) STRICT;
  CREATE TABLE contributions (
    note_id TEXT NOT NULL REFERENCES nodes(id), actor_id TEXT NOT NULL REFERENCES actors(id),
    role TEXT NOT NULL, contributed_at TEXT NOT NULL,
    source TEXT NOT NULL, agent TEXT NOT NULL, harness TEXT NOT NULL,
    ordinal INTEGER NOT NULL,
    PRIMARY KEY (note_id, ordinal)
  ) STRICT;
  CREATE TABLE sources (
    id TEXT PRIMARY KEY, kind TEXT NOT NULL, target TEXT NOT NULL,
    version TEXT, accessed_at TEXT
  ) STRICT;
  CREATE TABLE citations (
    note_id TEXT NOT NULL REFERENCES nodes(id), source_id TEXT NOT NULL REFERENCES sources(id),
    locator TEXT, purpose TEXT, ordinal INTEGER NOT NULL,
    PRIMARY KEY (note_id, ordinal)
  ) STRICT;
  CREATE TABLE reviews (
    note_id TEXT NOT NULL REFERENCES nodes(id), actor_id TEXT NOT NULL REFERENCES actors(id),
    verdict TEXT NOT NULL, reviewed_at TEXT NOT NULL, comment TEXT, ordinal INTEGER NOT NULL,
    PRIMARY KEY (note_id, ordinal)
  ) STRICT;
  CREATE TABLE revisions (
    note_id TEXT NOT NULL REFERENCES nodes(id), commit_hash TEXT NOT NULL,
    committed_at INTEGER NOT NULL, PRIMARY KEY (note_id, commit_hash)
  ) STRICT;
`);
const putNode = db.prepare(`INSERT OR REPLACE INTO nodes VALUES (?,?,?,?,?,?,?)`);
const putEdge = db.prepare(`INSERT OR REPLACE INTO edges VALUES (?,?,?,?)`);
const putMetadata = db.prepare(`INSERT INTO note_metadata VALUES (?,?,?,?)`);
const putActor = db.prepare(`INSERT INTO actors VALUES (?,?,?)`);
const putContribution = db.prepare(`INSERT INTO contributions VALUES (?,?,?,?,?,?,?,?)`);
const putSource = db.prepare(`INSERT INTO sources VALUES (?,?,?,?,?)`);
const putCitation = db.prepare(`INSERT INTO citations VALUES (?,?,?,?,?)`);
const putReview = db.prepare(`INSERT INTO reviews VALUES (?,?,?,?,?,?)`);
const putRevision = db.prepare(`INSERT INTO revisions VALUES (?,?,?)`);
db.transaction(() => {
  for (const item of nodes) putNode.run(...Object.values(item));
  for (const item of edges) putEdge.run(...Object.values(item));
  for (const item of noteMetadata) putMetadata.run(...Object.values(item));
  for (const item of actors.values()) putActor.run(...Object.values(item));
  for (const item of contributions) putContribution.run(...Object.values(item));
  for (const item of sources.values()) putSource.run(...Object.values(item));
  for (const item of citations) putCitation.run(...Object.values(item));
  for (const item of reviews) putReview.run(...Object.values(item));
  for (const item of revisions) putRevision.run(...Object.values(item));
})();

// SQLite is the sole normalized projection. JSON consumers receive ordered
// query results rather than a second interpretation of authored plaintext.
const artifact =
  JSON.stringify(
    {
      generatedBy: "scripts/notes.mjs",
      nodes: db.query(`SELECT id,kind,title,status,path,words,updated FROM nodes ORDER BY id`).all(),
      edges: db
        .query(`SELECT source,predicate,target,detail FROM edges ORDER BY source,predicate,target`)
        .all(),
      noteMetadata: db
        .query(
          `SELECT note_id noteId,stable_id stableId,review,format
           FROM note_metadata ORDER BY stable_id`,
        )
        .all(),
      actors: db
        .query(`SELECT id,kind,display_name displayName FROM actors ORDER BY id`)
        .all(),
      contributions: db
        .query(
          `SELECT note_id noteId,actor_id actorId,role,contributed_at contributedAt,
                  source,agent,harness,ordinal
           FROM contributions ORDER BY note_id,ordinal`,
        )
        .all(),
      sources: db
        .query(
          `SELECT id,kind,target,version,accessed_at accessedAt FROM sources ORDER BY id`,
        )
        .all(),
      citations: db
        .query(
          `SELECT note_id noteId,source_id sourceId,locator,purpose,ordinal
           FROM citations ORDER BY note_id,ordinal`,
        )
        .all(),
      reviews: db
        .query(
          `SELECT note_id noteId,actor_id actorId,verdict,reviewed_at reviewedAt,comment,ordinal
           FROM reviews ORDER BY note_id,ordinal`,
        )
        .all(),
      revisions: db
        .query(
          `SELECT note_id noteId,commit_hash AS "commit",committed_at committedAt
           FROM revisions ORDER BY note_id,commit_hash`,
        )
        .all(),
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

const show = (rows) => (rows.length ? console.table(rows) : console.log("(none)"));
const sql = valueAfter("--sql");
const stale = valueAfter("--stale");
const task = valueAfter("--task");
const term = valueAfter("--term");
const noteId = valueAfter("--note");
const actorId = valueAfter("--actor");
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
} else if (term) {
  show(
    db
      .query(
        `SELECT e.predicate,n.kind,n.id,n.title,n.path,e.detail
         FROM edges e
         JOIN nodes n ON n.id=CASE WHEN e.source=? THEN e.target ELSE e.source END
         WHERE (e.source=? AND e.predicate='defined-by')
            OR (e.target=? AND e.predicate='uses-term')
         ORDER BY e.predicate,n.path`,
      )
      .all(`term:${term}`, `term:${term}`, `term:${term}`),
  );
} else if (noteId) {
  show(
    db
      .query(
        `SELECT m.stable_id stableId,n.title,n.path,n.status,m.review,
                c.role,c.actor_id actor,c.contributed_at contributedAt
         FROM note_metadata m JOIN nodes n ON n.id=m.note_id
         LEFT JOIN contributions c ON c.note_id=m.note_id
         WHERE m.stable_id=? ORDER BY c.ordinal`,
      )
      .all(noteId),
  );
} else if (actorId) {
  show(
    db
      .query(
        `SELECT m.stable_id stableId,n.title,n.path,c.role,c.contributed_at contributedAt
         FROM contributions c JOIN note_metadata m ON m.note_id=c.note_id
         JOIN nodes n ON n.id=c.note_id WHERE c.actor_id=?
         ORDER BY c.contributed_at,n.path`,
      )
      .all(actorId),
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
