#!/usr/bin/env bun
/**
 * Idempotently fill stable IDs and author provenance on Markdown notes.
 * Existing stable IDs and non-contribution frontmatter are preserved.
 */
import { execFileSync } from "node:child_process";
import { readFileSync, writeFileSync } from "node:fs";
import { resolve } from "node:path";

const ROOT = resolve(import.meta.dir, "..");
const BASELINE = "a1b24078";
const paths = execFileSync("rg", ["--files", "notes", "-g", "*.md"], { cwd: ROOT })
  .toString()
  .trim()
  .split("\n")
  .filter(Boolean)
  .sort();
const codexAuthored = new Set(
  execFileSync(
    "git",
    ["diff", "--name-only", "--diff-filter=A", `${BASELINE}..HEAD`, "--", "notes"],
    { cwd: ROOT },
  )
    .toString()
    .trim()
    .split("\n")
    .filter((path) => path.endsWith(".md")),
);

const existing = new Map();
for (const path of paths) {
  const text = readFileSync(resolve(ROOT, path), "utf8");
  const id = text.match(/^id\s*=\s*"(N[0-9A-Z]{4,})"\s*$/m)?.[1];
  if (!id) continue;
  if (existing.has(id)) throw new Error(`duplicate note id ${id}: ${existing.get(id)} and ${path}`);
  existing.set(id, path);
}

let next = 1;
function allocate() {
  while (true) {
    const id = `N${(next++).toString(36).toUpperCase().padStart(4, "0")}`;
    if (!existing.has(id)) return id;
  }
}

function firstCommittedAt(path) {
  const dates = execFileSync(
    "git",
    ["log", "--follow", "--format=%aI", "--reverse", "--", path],
    { cwd: ROOT },
  )
    .toString()
    .trim()
    .split("\n")
    .filter(Boolean);
  return dates[0] ?? "2026-07-19T00:00:00+01:00";
}

for (const path of paths) {
  let text = readFileSync(resolve(ROOT, path), "utf8");
  const currentId = text.match(/^id\s*=\s*"(N[0-9A-Z]{4,})"\s*$/m)?.[1];
  const id = currentId ?? allocate();
  existing.set(id, path);
  const isCodex = codexAuthored.has(path);
  const author = isCodex ? "gpt-5.6-sol" : "claude";
  const contribution = [
    "[[contributions]]",
    'role = "author"',
    `actor = "agent:${author}"`,
    `at = "${firstCommittedAt(path)}"`,
    `source = "${isCodex ? "codex-development-wave" : "legacy"}"`,
    `agent = "${author}"`,
    `harness = "${isCodex ? "codex" : "claude"}"`,
  ].join("\n");

  if (!text.startsWith("+++\n")) {
    text = `+++\nid = "${id}"\nstatus = "draft"\nreview = "unreviewed"\n\n${contribution}\n+++\n\n${text}`;
  } else {
    const end = text.indexOf("\n+++\n", 4);
    if (end < 0) throw new Error(`${path}: unterminated TOML frontmatter`);
    let header = text.slice(4, end);
    header = header
      .replace(/\n?\[\[contributions\]\]\n[\s\S]*?(?=\n\[\[|\s*$)/g, "")
      .trimEnd();
    if (!currentId) header = `id = "${id}"\n${header}`;
    header = `${header}\n\n${contribution}`;
    text = `+++\n${header}\n+++\n${text.slice(end + 5).replace(/^\n*/, "\n")}`;
  }
  writeFileSync(resolve(ROOT, path), text);
}

console.error(
  `note metadata: ${paths.length} notes; ${codexAuthored.size} codex-authored, ` +
    `${paths.length - codexAuthored.size} legacy`,
);
