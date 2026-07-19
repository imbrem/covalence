// Reactive glue over `kernelApi.ts`: a mount-once kernel handle, and a
// debounced/cached "recheck as you type" driver for heavy kernel calls.

import { browser } from '$app/environment';
import { loadKernel, type KernelExports } from './kernelApi';

// `$effect`, not `onMount` — either works now, but the reason to prefer this
// one is worth keeping. Svelte's exports map lists `"worker"`
// (→ src/index-server.js) BEFORE `"browser"` (→ src/index-client.js), and this
// app bundles a worker, so the `worker` condition once pulled the SERVER entry
// into the client graph: `onMount` was exported as `noop` and never fired
// anywhere, silently. `vite.config.ts` now pins `resolve.conditions` to put
// `browser` first, which is what keeps lifecycle hooks real — if that ever
// regresses, `onMount` goes quiet again while `$state`/`$effect` keep working
// (the compiler emits those into `svelte/internal/client` directly).

/** A kernel that is loading, loaded, or failed. Exactly one of these holds. */
export interface KernelHandle {
	/** The kernel exports once instantiated, else `null`. */
	readonly kernel: KernelExports | null;
	/** The load failure, verbatim, else `''`. */
	readonly error: string;
	/** Still instantiating (neither loaded nor failed). */
	readonly loading: boolean;
}

/**
 * Start loading the kernel on mount and expose its state reactively.
 * Call during component initialization (it installs an `$effect`).
 */
export function useKernel(): KernelHandle {
	let kernel = $state<KernelExports | null>(null);
	let error = $state('');

	// Guarded by a plain (non-reactive) flag so re-runs of the effect cannot
	// kick off a second load; `loadKernel` memoizes too, this is belt-and-braces.
	let started = false;
	$effect(() => {
		if (!browser || started) return;
		started = true;
		loadKernel().then(
			(k) => (kernel = k),
			(e) => (error = e instanceof Error ? e.message : String(e))
		);
	});

	return {
		get kernel() {
			return kernel;
		},
		get error() {
			return error;
		},
		get loading() {
			return kernel === null && error === '';
		}
	};
}

/** How a `liveCheck` driver reports itself to the page. */
export interface LiveCheck<I, R> {
	/** Latest settled result, or `null` before the first check lands. */
	readonly result: R | null;
	/** A check is scheduled or in flight. */
	readonly busy: boolean;
	/** Debounce, then check (no-op if `input` is `null`). */
	schedule(input: I | null): void;
	/** Skip the debounce and check right now. */
	now(input: I | null): void;
}

export interface LiveCheckOpts<I, R> {
	/** Cache/staleness key. MUST capture every part of `input` that affects `run`. */
	key(input: I): string;
	/** The actual (potentially expensive) check. */
	run(input: I): R | Promise<R>;
	/** Debounce window; 300ms matches what `/article` needed to stay usable. */
	delayMs?: number;
}

/**
 * Drive an expensive check from a live-editing surface: debounce keystrokes,
 * memoize by key, and drop stale replies.
 *
 * INVARIANT (stale guard): a check that resolves after the user has moved on
 * NEVER overwrites the view. Each run takes a sequence number and only the
 * most recent one may publish — otherwise a slow `nat/unary` check landing
 * late would clobber the result the user is actually looking at.
 *
 * INVARIANT (cache key): results are keyed by `key(input)`, so callers must
 * fold *everything* the check depends on into it. The same article source at a
 * different model is a different result.
 */
export function liveCheck<I, R>(opts: LiveCheckOpts<I, R>): LiveCheck<I, R> {
	const delayMs = opts.delayMs ?? 300;
	let result = $state<R | null>(null);
	let busy = $state(false);

	const cache = new Map<string, R>();
	let seq = 0;
	let timer: ReturnType<typeof setTimeout> | undefined;

	async function run(input: I) {
		const k = opts.key(input);
		const hit = cache.get(k);
		if (hit !== undefined) {
			result = hit;
			busy = false;
			return;
		}
		const mine = ++seq;
		busy = true;
		const r = await opts.run(input);
		cache.set(k, r);
		if (mine === seq) {
			result = r;
			busy = false;
		}
	}

	return {
		get result() {
			return result;
		},
		get busy() {
			return busy;
		},
		schedule(input: I | null) {
			if (input === null) return;
			clearTimeout(timer);
			// A cached key can be reflected immediately — debouncing a map
			// lookup would only add flicker.
			if (cache.has(opts.key(input))) {
				void run(input);
				return;
			}
			busy = true;
			timer = setTimeout(() => void run(input), delayMs);
		},
		now(input: I | null) {
			if (input === null) return;
			clearTimeout(timer);
			void run(input);
		}
	};
}
