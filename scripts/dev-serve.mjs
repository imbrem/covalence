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

import { spawn } from 'node:child_process';
import { existsSync } from 'node:fs';

const COV = 'target/debug/cov';
if (!existsSync(COV)) {
	console.error(`error: ${COV} not found — run \`bun run build:native\` first (or use \`bun run serve\`).`);
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
