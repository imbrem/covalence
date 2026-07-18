import { expect, test } from "bun:test";
import { Database } from "bun:sqlite";

test("note provenance is normalized through SQLite", () => {
  const todos = Bun.spawnSync(["bun", "scripts/todos.mjs"], {
    stdout: "ignore",
    stderr: "pipe",
  });
  expect(todos.exitCode, todos.stderr.toString()).toBe(0);

  const notes = Bun.spawnSync(["bun", "scripts/notes.mjs"], {
    stdout: "ignore",
    stderr: "pipe",
  });
  expect(notes.exitCode, notes.stderr.toString()).toBe(0);

  const db = new Database("target/covalence-notes.sqlite", {
    readonly: true,
    strict: true,
  });
  const metadata = db
    .query(
      `SELECT m.stable_id stableId,n.status,m.review,c.actor_id actor,
              c.source,c.agent,c.harness
       FROM note_metadata m JOIN nodes n ON n.id=m.note_id
       JOIN contributions c ON c.note_id=m.note_id
       WHERE m.stable_id='N0001'`,
    )
    .get();
  expect(metadata).toEqual({
    stableId: "N0001",
    status: "draft",
    review: "unreviewed",
    actor: "agent:gpt-5.6-sol",
    source: "codex-development-wave",
    agent: "gpt-5.6-sol",
    harness: "codex",
  });
  expect(
    db
      .query(`SELECT count(*) count FROM nodes WHERE kind='note' AND status='unparsed legacy'`)
      .get().count,
  ).toBe(0);
  expect(
    db
      .query(
        `SELECT count(*) count FROM citations c
         JOIN note_metadata m ON m.note_id=c.note_id WHERE m.stable_id='N0001'`,
      )
      .get().count,
  ).toBe(3);
  db.close();
});
