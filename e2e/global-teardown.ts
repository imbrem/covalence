/**
 * Kills whatever global-setup spawned and removes its throwaway state dir.
 *
 * Absence of the state file means global-setup used an externally-provided
 * COV_E2E_URL (or died before spawning) — in both cases there is nothing of
 * ours to clean up.
 */
import * as fs from 'node:fs';

import { STATE_FILE, type ServerState } from './global-setup';

export default async function globalTeardown() {
	if (!fs.existsSync(STATE_FILE)) return;

	let state: ServerState;
	try {
		state = JSON.parse(fs.readFileSync(STATE_FILE, 'utf8')) as ServerState;
	} catch {
		fs.rmSync(STATE_FILE, { force: true });
		return;
	}

	try {
		// Negative pid: the whole detached process group from global-setup.
		process.kill(-state.pid, 'SIGTERM');
		await new Promise((r) => setTimeout(r, 300));
		try {
			process.kill(-state.pid, 'SIGKILL');
		} catch {
			/* already gone — the SIGTERM took */
		}
	} catch {
		/* already gone */
	}

	fs.rmSync(STATE_FILE, { force: true });
	fs.rmSync(state.tmpDir, { recursive: true, force: true });
}
