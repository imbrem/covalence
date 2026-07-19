// Health polling for the fetch-backed REPL pages (/lisp, /forsp).
//
// The WebSocket REPL at `/` polls from `repl.svelte.ts` because its state is
// tab-global; these pages just want a status dot while they're mounted, so this
// is per-instance and stops on unmount.
import { client } from '$lib/api';
import type { HealthResponse } from 'covalence-client';

export class HealthPoll {
	healthy = $state(false);
	last = $state<HealthResponse | null>(null);
	#timer: ReturnType<typeof setTimeout> | null = null;
	#stopped = false;

	async poll() {
		try {
			this.last = await client.health();
			this.healthy = true;
		} catch {
			this.healthy = false;
		}
		// A poll in flight when `stop()` lands must not schedule another one.
		if (!this.#stopped) this.#timer = setTimeout(() => this.poll(), 5000);
	}

	start() {
		this.#stopped = false;
		this.poll();
	}

	stop() {
		this.#stopped = true;
		if (this.#timer != null) clearTimeout(this.#timer);
		this.#timer = null;
	}
}
