// Module-level transcript storage, keyed by REPL endpoint.
//
// SvelteKit is an SPA here: navigating /lisp → /forsp → /lisp tears the page
// component down and back up. The server session survives (see `serverRepl`,
// which memoizes per endpoint), so the transcript has to survive with it — a
// live session whose history vanished is worse than no history at all.

/** One transcript cell: the submitted source and everything learned about it. */
export interface Entry {
	input: string;
	// The prompt this cell was SUBMITTED under, captured at submit time. On
	// /lisp the prompt tracks the live dialect, so rendering the current one
	// against every cell would retroactively relabel history — a `(+ 2 2)` run
	// in `lisp` would read as `acl2>` after a later `#lang acl2`, claiming a
	// dialect it never ran in.
	prompt: string;
	output: string;
	ok: boolean;
	directive: boolean;
	pending: boolean;
	widget: boolean;
	hol: string | null;
	holTried: boolean;
	// `#show` failed (or returned nothing) for this cell — e.g. a defun/defthm
	// ack, which is not a reducible expression. No popover: a turnstile with no
	// theorem behind it would be a false claim.
	holFailed: boolean;
}

export interface Transcript {
	entries: Entry[];
	history: string[];
}

const transcripts = new Map<string, Transcript>();

function newTranscript(): Transcript {
	// Declared with the rune so the arrays are deep-reactive proxies — cells
	// mutated in place (pending → result) still fire signals in every consumer.
	const t = $state<Transcript>({ entries: [], history: [] });
	return t;
}

/**
 * The (stable, reactive) transcript for `key`. The same object comes back for
 * the life of the tab, so mutations made before a navigation are still there
 * after it.
 */
export function transcriptFor(key: string): Transcript {
	let t = transcripts.get(key);
	if (!t) {
		t = newTranscript();
		transcripts.set(key, t);
	}
	return t;
}

/** Drop a transcript's contents in place (keeps the identity `transcriptFor` handed out). */
export function clearTranscript(t: Transcript) {
	t.entries.length = 0;
}
