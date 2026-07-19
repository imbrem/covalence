// Page-local support for the ACL2 demo at `/acl2`.
//
// There is no ACL2 endpoint: the slice is reached through POST /api/lisp with a
// `#lang acl2` cell, and that cell RESETS the server session. So the dialect is
// never opened behind the user's back — `openAcl2Session` puts the real
// `#lang acl2` cell in the transcript with the server's real answer, exactly as
// if it had been typed.

import type { Entry, Transcript } from '$lib/repl/transcripts.svelte';
import { LISP_KEYWORDS } from '$lib/repl/sexpr';

/** The cell that opens (and, re-run, resets) the ACL2 session. */
export const OPEN_CELL = '#lang acl2';

/**
 * ACL2 spellings on top of the shared Lisp vocabulary: `equal`, ternary `if`
 * (no `cond`), `consp`/`atom`/`endp`, `zp`/`natp`, plus the event heads a book
 * can contain — `implies` included, because free-variable goals are a thing the
 * page deliberately shows being REJECTED, and it should read as a keyword when
 * it does.
 */
export const ACL2_KEYWORDS: ReadonlySet<string> = new Set([
	...LISP_KEYWORDS,
	'implies',
	'in-package',
	'include-book',
	'local',
	'defmacro',
	'encapsulate',
	'mutual-recursion',
]);

/** Special forms whose bodies indent by 2 (see `calcIndent`). */
export const ACL2_SPECIAL_FORMS: ReadonlySet<string> = new Set([
	'defun', 'defthm', 'if', 'let', 'quote', 'local', 'encapsulate', 'implies',
]);

/** One clickable tour example: a SEQUENCE of cells, each run through the transcript. */
export interface Acl2Example {
	title: string;
	/** Run in order; prerequisites (a `defun` a later cell needs) are cells too. */
	cells: string[];
	/** What the user should look for in the output. */
	note?: string;
}

/** A tour step: prose lead-in plus its examples. */
export interface Acl2Group {
	id: string;
	title: string;
	lead: string;
	examples: Acl2Example[];
}

// Module-level, like the transcript itself: a remount must not fire a second
// opening cell (which would silently reset a session the transcript above it
// still describes).
let opening = false;

function pendingEntry(src: string, prompt: string): Entry {
	return {
		input: src,
		prompt,
		output: '',
		ok: true,
		directive: src.startsWith('#'),
		pending: true,
		widget: false,
		hol: null,
		holTried: false,
		holFailed: false
	};
}

/**
 * Open the ACL2 dialect as a real, visible first cell — a no-op if the
 * transcript already has cells (an SPA remount lands on a live session).
 *
 * The cell is pushed straight into the shared transcript store because `<Repl>`
 * exposes its evaluator only to the `help` snippet; the output written here is
 * the server's genuine response, never a canned string.
 */
// TODO(cov:web.repl-autorun-prop, minor): Give `<Repl>` an `autoRun` prop so a page can open its dialect through the component's own evaluator instead of the transcript store.
export async function openAcl2Session(
	t: Transcript,
	evalCell: (src: string) => Promise<{ ok: boolean; result: string; error: string }>,
	prompt: string
): Promise<void> {
	if (opening || t.entries.length > 0) return;
	opening = true;
	t.entries.push(pendingEntry(OPEN_CELL, prompt));
	t.history.push(OPEN_CELL);
	// Mutate through the array proxy (Svelte 5 deep reactivity) — a captured raw
	// reference updates the data without firing the signal.
	const cell = t.entries[t.entries.length - 1];
	try {
		const r = await evalCell(OPEN_CELL);
		cell.output = r.ok ? r.result : r.error;
		cell.ok = r.ok;
	} catch (err) {
		cell.output = String(err);
		cell.ok = false;
	}
	cell.pending = false;
	opening = false;
}
