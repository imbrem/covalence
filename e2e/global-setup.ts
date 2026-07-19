/**
 * Spawns the server the whole Playwright run talks to.
 *
 * Mirrors tests/e2e.test.ts: a prebuilt `target/debug/cov serve` on a free
 * port, with XDG_* and HOME pointed at a throwaway temp dir so the run can
 * never touch the developer's real store. The chosen URL is published two
 * ways — `process.env.COV_E2E_URL` (inherited by the worker processes, which
 * re-evaluate playwright.config.ts and pick it up as `baseURL`) and a state
 * file that global-teardown reads to kill what we started.
 *
 * If COV_E2E_URL is already set we spawn nothing and write no state file, so
 * teardown leaves the externally-owned server alone.
 */
import { spawn } from 'node:child_process';
import * as fs from 'node:fs';
import * as net from 'node:net';
import * as os from 'node:os';
import * as path from 'node:path';

export const STATE_FILE = path.join(__dirname, '.server-state.json');

export type ServerState = { pid: number; url: string; tmpDir: string; logFile: string };

/** Ask the OS for an unused port by binding to 0 and reading it back. */
function freePort(): Promise<number> {
	return new Promise((resolve, reject) => {
		const srv = net.createServer();
		srv.on('error', reject);
		srv.listen(0, '127.0.0.1', () => {
			const addr = srv.address();
			if (addr === null || typeof addr === 'string') {
				srv.close(() => reject(new Error('could not determine a free port')));
				return;
			}
			const { port } = addr;
			srv.close(() => resolve(port));
		});
	});
}

async function waitForHealth(url: string, timeoutMs: number, alive: () => boolean, log: () => string) {
	const deadline = Date.now() + timeoutMs;
	while (Date.now() < deadline) {
		if (!alive()) throw new Error(`cov serve exited during startup:\n${log()}`);
		try {
			const res = await fetch(`${url}/api/health`);
			if (res.ok) {
				const body = (await res.json()) as { status?: string };
				if (body.status === 'ok') return;
			}
		} catch {
			/* not listening yet */
		}
		await new Promise((r) => setTimeout(r, 100));
	}
	throw new Error(`cov serve did not become healthy at ${url} within ${timeoutMs}ms:\n${log()}`);
}

export default async function globalSetup() {
	if (process.env.COV_E2E_URL) {
		const url = process.env.COV_E2E_URL.replace(/\/$/, '');
		process.env.COV_E2E_URL = url;
		// Still gate on health so a spec failure means a spec bug, not a
		// half-started dev server.
		await waitForHealth(url, 30_000, () => true, () => '(external server; no log captured)');
		console.log(`[e2e] using external server at ${url}`);
		return;
	}

	const repoRoot = path.resolve(__dirname, '..');
	const covBin = path.join(repoRoot, 'target', 'debug', 'cov');
	if (!fs.existsSync(covBin)) {
		throw new Error(
			`${covBin} not found — run \`bun run build:serve\` first, or set COV_E2E_URL to an already-running server.`
		);
	}

	const tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), 'cov-e2e-pw-'));
	const runtime = path.join(tmpDir, 'runtime');
	const data = path.join(tmpDir, 'data');
	const config = path.join(tmpDir, 'config');
	const home = path.join(tmpDir, 'home');
	for (const d of [runtime, data, config, home]) fs.mkdirSync(d, { recursive: true });

	const logFile = path.join(tmpDir, 'cov-serve.log');
	const logFd = fs.openSync(logFile, 'a');
	const port = await freePort();
	const url = `http://127.0.0.1:${port}`;

	const proc = spawn(covBin, ['serve', '--port', String(port)], {
		env: {
			...process.env,
			XDG_RUNTIME_DIR: runtime,
			XDG_DATA_HOME: data,
			XDG_CONFIG_HOME: config,
			HOME: home
		},
		stdio: ['ignore', logFd, logFd],
		// Own process group: teardown can signal the whole tree even if the
		// server ever grows children.
		detached: true
	});
	proc.unref();

	let exited = false;
	proc.on('exit', () => {
		exited = true;
	});

	const readLog = () => {
		try {
			return fs.readFileSync(logFile, 'utf8').slice(-4000);
		} catch {
			return '(no log)';
		}
	};

	try {
		await waitForHealth(url, 30_000, () => !exited, readLog);
	} catch (e) {
		if (proc.pid && !exited) process.kill(-proc.pid, 'SIGKILL');
		throw e;
	}

	const state: ServerState = { pid: proc.pid!, url, tmpDir, logFile };
	fs.writeFileSync(STATE_FILE, JSON.stringify(state, null, 2));
	process.env.COV_E2E_URL = url;
	console.log(`[e2e] cov serve ready at ${url} (pid ${proc.pid}, state ${tmpDir})`);
}
