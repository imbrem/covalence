#!/usr/bin/env bun
// Run the native API server (`cov serve --api` on :3100) and the SvelteKit dev
// server (Vite, hot-reloading) together, so the live site is served with
// instant Svelte updates and a real kernel backend. `bun run serve` builds the
// `cov` binary first, then launches both via this script; Ctrl-C tears down both.
//
// The Vite dev server proxies `/api` (REST + WebSocket) to the API server, so
// the `/metamath` import demo and the REPL work against the native kernel while
// the frontend hot-reloads. The API server is static (Rust is not hot-reloaded);
// re-run `bun run serve` after backend changes.

import { spawn, spawnSync } from 'node:child_process';
import { existsSync } from 'node:fs';

// Use the release binary when asked (`--release` or COV_RELEASE=1) — the
// `/metamath` import is term-heavy and runs *much* faster in release.
const release = process.argv.includes('--release') || process.env.COV_RELEASE === '1';
const COV = release ? 'target/release/cov' : 'target/debug/cov';
const how = release ? 'bun run release:native' : 'bun run build:native';
if (!existsSync(COV)) {
	console.error(
		`error: ${COV} not found — run \`${how}\` first (or use \`bun run serve${release ? ':release' : ''}\`).`,
	);
	process.exit(1);
}
// Guard against a CORRUPT/partial binary — e.g. a crash mid-link leaves a
// truncated file that `existsSync` accepts but exec rejects ("Exec format
// error"). cargo's fingerprint then still reads valid, so it won't relink over
// it. Probe it once and, if it can't run, give the actionable fix instead of
// silently spawning a dead process.
const probe = spawnSync(COV, ['--version'], { stdio: 'ignore' });
if (probe.error) {
	console.error(
		`error: ${COV} exists but is not runnable (${probe.error.code ?? probe.error.message}).\n` +
			`  It is likely corrupt (a crash during linking). cargo won't relink over it — force a clean rebuild:\n` +
			`    cargo clean --release && ${how}   (drop --release for the debug binary)`,
	);
	process.exit(1);
}

const procs = [];
let shuttingDown = false;

function cleanup() {
	if (shuttingDown) return;
	shuttingDown = true;
	for (const p of procs) {
		try {
			p.kill('SIGTERM');
		} catch {
			/* already gone */
		}
	}
}

for (const sig of ['SIGINT', 'SIGTERM']) {
	process.on(sig, () => {
		cleanup();
		process.exit(0);
	});
}
process.on('exit', cleanup);

// 1. The native API server (kernel) on :3100.
console.error('● starting API server: cov serve --api (:3100)');
const server = spawn(COV, ['serve', '--api'], { stdio: 'inherit' });
procs.push(server);
server.on('exit', (code) => {
	if (!shuttingDown) {
		console.error(`cov serve exited (code ${code ?? '?'})`);
		cleanup();
		process.exit(code ?? 1);
	}
});

// 2. The SvelteKit dev server (hot reload), after a short delay so the API
//    server is listening before the Vite proxy first connects.
setTimeout(() => {
	if (shuttingDown) return;
	console.error('● starting Svelte dev server (hot reload) — proxies /api → :3100');
	const web = spawn('bun', ['run', '--filter', 'covalence-web', 'dev'], { stdio: 'inherit' });
	procs.push(web);
	web.on('exit', (code) => {
		cleanup();
		process.exit(code ?? 0);
	});
}, 1500);
