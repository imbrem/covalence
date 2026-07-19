// S-expression editing + highlighting primitives shared by every REPL surface
// (the WAT/component REPL at `/`, the Lisp REPL at `/lisp`, Forsp at `/forsp`).
//
// Everything here is pure and keyword-set-parameterized: the *shapes* (strings,
// `;` comments, `|bar atoms|`, parens, hashes) are common to all our surface
// syntaxes, only the keyword/special-form vocabulary differs per language.

/** HTML-escape a string. Every path that emits `{@html …}` goes through this. */
export function escHtml(s: string): string {
	return s
		.replace(/&/g, '&amp;')
		.replace(/</g, '&lt;')
		.replace(/>/g, '&gt;')
		.replace(/"/g, '&quot;')
		.replace(/'/g, '&#39;');
}

export interface HighlightOpts {
	/** Render 64-char hex atoms as `/view/<hash>` links (default: true). */
	hashLinks?: boolean;
}

/**
 * Tokenize `text` into highlighted HTML. The output is always escaped — the
 * only markup produced is the `<span>`/`<a>` wrappers this function emits.
 */
export function highlight(
	text: string,
	keywords: ReadonlySet<string>,
	opts: HighlightOpts = {}
): string {
	const hashLinks = opts.hashLinks ?? true;
	let out = '';
	let i = 0;
	while (i < text.length) {
		const ch = text[i];
		if (ch === ';') {
			let end = text.indexOf('\n', i);
			if (end === -1) end = text.length;
			out += `<span class="hl-comment">${escHtml(text.slice(i, end))}</span>`;
			i = end;
		} else if (ch === '|') {
			let end = text.indexOf('|', i + 1);
			if (end === -1) end = text.length;
			else end++;
			out += `<span class="hl-atom">${escHtml(text.slice(i, end))}</span>`;
			i = end;
		} else if (ch === '"') {
			let end = i + 1;
			while (end < text.length && text[end] !== '"') {
				if (text[end] === '\\') end++;
				end++;
			}
			if (end < text.length) end++;
			out += `<span class="hl-string">${escHtml(text.slice(i, end))}</span>`;
			i = end;
		} else if (ch === '(' || ch === ')') {
			out += `<span class="hl-paren">${ch}</span>`;
			i++;
		} else if (/\s/.test(ch)) {
			out += ch;
			i++;
		} else {
			let end = i;
			while (end < text.length && !/[\s()";|]/.test(text[end])) end++;
			const atom = text.slice(i, end);
			if (hashLinks && /^[a-f0-9]{64}$/.test(atom)) {
				out += `<a class="hl-hash" href="/view/${atom}" data-hash="${atom}">${escHtml(atom)}</a>`;
			} else {
				let cls: string;
				if (keywords.has(atom)) cls = 'hl-keyword';
				else if (/^-?[0-9]/.test(atom) || /^0x[0-9a-fA-F]+$/.test(atom)) cls = 'hl-number';
				else if (atom.startsWith('$')) cls = 'hl-var';
				else cls = 'hl-atom';
				out += `<span class="${cls}">${escHtml(atom)}</span>`;
			}
			i = end;
		}
	}
	return out;
}

/** Heuristic: is this output structured code (S-expression or hashes) vs. prose (help, status)? */
export function isCodeOutput(text: string): boolean {
	const trimmed = text.trim();
	if (!trimmed) return false;
	const lines = trimmed.split('\n');
	// All lines are 64-char hex hashes
	if (lines.every((l) => /^[a-f0-9]{64}$/.test(l.trim()))) return true;
	// Looks like an S-expression block: starts with ( and last line ends with )
	const first = lines[0].trimStart();
	const last = lines[lines.length - 1].trimEnd();
	if (first.startsWith('(') && last.endsWith(')')) {
		let depth = 0,
			inStr = false,
			escaped = false;
		for (let i = 0; i < first.length; i++) {
			const ch = first[i];
			if (escaped) {
				escaped = false;
				continue;
			}
			if (inStr) {
				if (ch === '\\') escaped = true;
				else if (ch === '"') inStr = false;
				continue;
			}
			if (ch === '"') inStr = true;
			else if (ch === '(') depth++;
			else if (ch === ')') {
				depth--;
				if (depth === 0 && i < first.length - 1) {
					const rest = first.slice(i + 1).trim();
					if (rest && !rest.startsWith('(') && !rest.startsWith(';')) return false;
				}
			}
		}
		return true;
	}
	return false;
}

/**
 * Are the parens balanced (ignoring parens inside strings)? Enter submits when
 * this holds and inserts an indented newline when it doesn't, which is what
 * makes a one-line prompt usable for multi-line forms.
 */
export function parensBalanced(text: string): boolean {
	let depth = 0;
	let inStr = false;
	let escaped = false;
	for (const ch of text) {
		if (escaped) {
			escaped = false;
			continue;
		}
		if (inStr) {
			if (ch === '\\') escaped = true;
			else if (ch === '"') inStr = false;
			continue;
		}
		if (ch === '"') inStr = true;
		else if (ch === '(') depth++;
		else if (ch === ')') depth--;
	}
	return depth === 0;
}

/**
 * The column a newline inserted at `cursor` should indent to: under the head's
 * first argument for a call, or head-column + 2 for a special form (and for a
 * bare `(`). Mirrors the usual Lisp convention.
 */
export function calcIndent(
	text: string,
	cursor: number,
	specialForms: ReadonlySet<string>
): number {
	const before = text.slice(0, cursor);
	const stack: { col: number; argCol: number }[] = [];
	let col = 0;
	let i = 0;
	let inStr = false;
	let escaped = false;

	while (i < before.length) {
		const ch = before[i];
		if (escaped) {
			escaped = false;
			col++;
			i++;
			continue;
		}
		if (inStr) {
			if (ch === '\\') escaped = true;
			else if (ch === '"') inStr = false;
			if (ch === '\n') col = 0;
			else col++;
			i++;
			continue;
		}
		if (ch === '\n') {
			col = 0;
			i++;
			continue;
		}
		if (ch === '"') {
			inStr = true;
			col++;
			i++;
			continue;
		}
		if (ch === '(') {
			const parenCol = col;
			col++;
			i++;
			while (i < before.length && before[i] === ' ') {
				col++;
				i++;
			}
			const headStart = i;
			while (i < before.length && !/[\s()";|]/.test(before[i])) {
				col++;
				i++;
			}
			const head = before.slice(headStart, i);

			let argCol: number;
			if (!head || specialForms.has(head)) {
				argCol = parenCol + 2;
			} else {
				argCol = i < before.length && before[i] === ' ' ? col + 1 : col;
			}
			stack.push({ col: parenCol, argCol });
			continue;
		}
		if (ch === ')') {
			stack.pop();
			col++;
			i++;
			continue;
		}
		col++;
		i++;
	}

	if (stack.length === 0) return 0;
	return stack[stack.length - 1].argCol;
}

/** WAT / component-model vocabulary — the `/` REPL. */
export const WAT_KEYWORDS: ReadonlySet<string> = new Set([
	// WAT component-model structural keywords
	'module', 'component', 'import', 'export', 'func', 'param', 'result',
	'type', 'instance', 'core', 'canon', 'lift', 'lower',
	'memory', 'table', 'global', 'elem', 'data', 'start', 'local', 'alias',
	// REPL commands
	'store', 'read', 'read-wat', 'store-url', 'store-file',
	'compile-wat', 'hash', 'print', 'status', 'help',
]);

/** WAT special forms — bodies indent by 2 from the head paren. */
export const WAT_SPECIAL_FORMS: ReadonlySet<string> = new Set([
	'module', 'component', 'func', 'block', 'loop', 'if', 'type',
	'import', 'export', 'instance', 'core', 'memory', 'table', 'global',
	'elem', 'data', 'canon', 'alias', 'local',
]);

/** Lisp-family vocabulary — `/lisp` (all dialects) plus the `#` directives. */
export const LISP_KEYWORDS: ReadonlySet<string> = new Set([
	'defun', 'define', 'lambda', 'cond', 'if', 'quote', 'let', 'equal',
	'car', 'cdr', 'cons', 'consp', 'atom', 'endp', 'zp', 'natp', 'defthm',
	'atom?', 'null?', 'eq?', 't', 'nil',
	'#lang', '#show', '#help', '#book', '#reset',
]);

/** Lisp special forms — bodies indent by 2 from the head paren. */
export const LISP_SPECIAL_FORMS: ReadonlySet<string> = new Set([
	'defun', 'define', 'lambda', 'cond', 'if', 'let', 'let*', 'defthm',
	'quote', 'progn',
]);
