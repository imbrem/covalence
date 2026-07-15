#!/usr/bin/env bun
// e2e driver for the /lisp demo: boots `cov serve --api` on a free port, then
// drives EVERY example from apps/covalence-web/src/lib/lispExamples.json — in
// order, through POST /api/lisp in one fresh session — asserting `ok: true`
// for each (plus exact outputs for a few stable cells). Dialect handling
// mirrors the /lisp page: when an example's `lang` differs from the session's
// current dialect, a `#lang <name>` cell is issued (and asserted) first; any
// explicit `#lang` example cells are honored too.
//
//   bun run e2e:lisp                 # spawns target/release/cov
//   COV_BIN=target/debug/cov …       # a different binary
//   COV_PORT=3123 …                  # a fixed port instead of a free one
//   COV_URL=http://host:port …       # drive an ALREADY-RUNNING server
//
// Exits nonzero on any failure. Outputs are intentionally NOT pinned beyond
// the stable few — dialect behaviour is evolving; this asserts ok-ness.

import { spawn } from 'node:child_process';
import { readFileSync } from 'node:fs';
import net from 'node:net';
import path from 'node:path';
import process from 'node:process';
import { fileURLToPath } from 'node:url';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const examples = JSON.parse(
	readFileSync(path.join(root, 'apps/covalence-web/src/lib/lispExamples.json'), 'utf8')
);

// Cells whose exact output is stable across the ongoing dialect work.
const STABLE = new Map([['(+ 2 2)', '4']]);

const freePort = () =>
	new Promise((resolve, reject) => {
		const srv = net.createServer();
		srv.once('error', reject);
		srv.listen(0, '127.0.0.1', () => {
			const { port } = srv.address();
			srv.close(() => resolve(port));
		});
	});

async function waitForHealth(base, child, timeoutMs = 60_000) {
	const deadline = Date.now() + timeoutMs;
	while (Date.now() < deadline) {
		if (child && child.exitCode !== null) {
			throw new Error(`server exited early (code ${child.exitCode})`);
		}
		try {
			const res = await fetch(`${base}/api/health`);
			if (res.ok) return;
		} catch {
			// not up yet
		}
		await new Promise((r) => setTimeout(r, 250));
	}
	throw new Error(`server not healthy at ${base} within ${timeoutMs}ms`);
}

function truncate(s, n) {
	const one = s.replace(/\s+/g, ' ').trim();
	return one.length > n ? `${one.slice(0, n - 1)}…` : one;
}

async function main() {
	let child = null;
	let base = process.env.COV_URL || null;

	if (!base) {
		const bin = process.env.COV_BIN || path.join(root, 'target/release/cov');
		const port = process.env.COV_PORT ? Number(process.env.COV_PORT) : await freePort();
		base = `http://127.0.0.1:${port}`;
		console.log(`starting: ${bin} serve --api --port ${port}`);
		child = spawn(bin, ['serve', '--api', '--port', String(port)], {
			stdio: ['ignore', 'ignore', 'inherit']
		});
		child.on('error', (e) => {
			console.error(`failed to start server: ${e.message}`);
			process.exit(1);
		});
	}

	const kill = () => {
		if (child && child.exitCode === null) child.kill();
	};
	process.on('exit', kill);
	process.on('SIGINT', () => process.exit(130));
	process.on('SIGTERM', () => process.exit(143));

	await waitForHealth(base, child);

	// One fresh session for the whole run (defuns accumulate, like a tab).
	const session = `e2e-lisp-${Date.now()}-${Math.random().toString(36).slice(2)}`;
	const post = async (src) => {
		const res = await fetch(`${base}/api/lisp`, {
			method: 'POST',
			headers: { 'content-type': 'application/json' },
			body: JSON.stringify({ session, src })
		});
		return res.json();
	};

	const rows = [];
	let failures = 0;
	let lang = 'lisp'; // the server session's default dialect

	const run = async (tag, name, src, expected) => {
		const t0 = Date.now();
		let r;
		try {
			r = await post(src);
		} catch (e) {
			r = { ok: false, error: String(e) };
		}
		const ms = Date.now() - t0;
		let ok = !!r.ok;
		let out = ok ? (r.result ?? '') : (r.error ?? '');
		if (ok && expected !== undefined && out !== expected) {
			ok = false;
			out = `expected ${JSON.stringify(expected)}, got ${JSON.stringify(out)}`;
		}
		if (!ok) failures++;
		rows.push({ tag, name, ok, ms, out });
		// Track dialect switches exactly like the web client does.
		const m = src.trim().match(/^#lang\s+(\S+)$/);
		if (m && r.ok) {
			const echoed = String(r.result ?? '').match(/^#lang\s+([\w-]+)/);
			lang = echoed ? echoed[1] : m[1];
		}
		return ok;
	};

	for (const ex of examples) {
		const isSwitch = /^#lang\s+\S+$/.test(ex.src.trim());
		if (!isSwitch && ex.lang && ex.lang !== lang) {
			await run(ex.lang, `→ #lang ${ex.lang}`, `#lang ${ex.lang}`);
		}
		await run(ex.lang ?? lang, ex.title, ex.src, STABLE.get(ex.src));
	}

	// The table.
	const w = {
		n: 3,
		lang: Math.max(4, ...rows.map((r) => r.tag.length)),
		name: Math.max(4, ...rows.map((r) => r.name.length)),
		ok: 4,
		ms: 6
	};
	const line = (n, tag, name, ok, ms, out) =>
		`${String(n).padStart(w.n)}  ${tag.padEnd(w.lang)}  ${name.padEnd(w.name)}  ${ok.padEnd(w.ok)}  ${String(ms).padStart(w.ms)}  ${out}`;
	console.log(`\n${line('#', 'lang', 'cell', 'ok', 'ms', 'output')}`);
	rows.forEach((r, i) =>
		console.log(line(i + 1, r.tag, r.name, r.ok ? 'ok' : 'FAIL', r.ms, truncate(r.out, 60)))
	);
	console.log(
		`\n${rows.length - failures}/${rows.length} cells ok` + (failures ? ` — ${failures} FAILED` : '')
	);

	kill();
	process.exit(failures ? 1 : 0);
}

main().catch((e) => {
	console.error(e);
	process.exit(1);
});
