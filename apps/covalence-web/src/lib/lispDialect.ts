// Client-side dialect tracking for the /lisp REPL.
//
// The server's Lisp session switches dialect on a `#lang NAME` cell (and
// RESETS its state); the page mirrors that here by *observing* evaluated
// cells, so the example buttons can follow the current dialect. Kept out of
// `Repl.svelte` on purpose — the component stays dialect-agnostic.

/** The server session's default dialect. */
export const DEFAULT_LANG = 'lisp';

/** Client mirror of the server's `Lang::parse` aliases (case-insensitive). */
const ALIASES: Record<string, string> = {
	lisp: 'lisp',
	'lisp-int': 'lisp',
	int: 'lisp',
	scheme: 'scheme',
	value: 'scheme',
	sector: 'sector',
	acl2: 'acl2'
};

/** Canonicalize a dialect name through the alias table (`null` if unknown). */
export function canonicalLang(name: string): string | null {
	return ALIASES[name.toLowerCase()] ?? null;
}

/**
 * If `src` is a `#lang NAME` cell, the raw NAME; else `null`. A bare `#lang`
 * only *reports* the current dialect (it never switches), so it returns `null`.
 */
export function langDirective(src: string): string | null {
	const m = src.trim().match(/^#lang\s+(\S+)$/);
	return m ? m[1] : null;
}

/**
 * The dialect in effect after a cell evaluates: a `#lang X` cell that returned
 * `ok` switches (anything else — errors included — leaves it unchanged, so
 * `null`). Prefers the canonical name echoed by the server
 * (`"#lang scheme (session reset)"`), falling back to the client alias table,
 * then to the raw argument (lowercased) so an unknown-to-us but
 * server-accepted name still tracks.
 */
export function dialectAfter(src: string, ok: boolean, result: string): string | null {
	const arg = langDirective(src);
	if (!arg || !ok) return null;
	const echoed = result.match(/^#lang\s+([\w-]+)/);
	if (echoed) return canonicalLang(echoed[1]) ?? echoed[1];
	return canonicalLang(arg) ?? arg.toLowerCase();
}

/** The distinct `lang` tags of an example list, in first-appearance order. */
export function dialectsOf(examples: { lang: string }[]): string[] {
	const out: string[] = [];
	for (const e of examples) if (!out.includes(e.lang)) out.push(e.lang);
	return out;
}
