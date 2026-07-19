import { expect, test } from 'vitest';
import {
	LISP_KEYWORDS,
	LISP_SPECIAL_FORMS,
	WAT_SPECIAL_FORMS,
	calcIndent,
	escHtml,
	highlight,
	isCodeOutput,
	parensBalanced
} from './sexpr';

test('escHtml escapes every character that could break out of a text node', () => {
	expect(escHtml(`<a href="x">&'`)).toBe('&lt;a href=&quot;x&quot;&gt;&amp;&#39;');
});

test('parensBalanced counts only parens outside strings', () => {
	expect(parensBalanced('')).toBe(true);
	expect(parensBalanced('(+ 2 2)')).toBe(true);
	expect(parensBalanced('(+ 2 (2)')).toBe(false);
	// Parens inside a string are text, not structure.
	expect(parensBalanced('(print "((((")')).toBe(true);
	// An escaped quote does not end the string.
	expect(parensBalanced('(print "a\\"(")')).toBe(true);
	// Over-closing is "unbalanced" too (depth goes negative).
	expect(parensBalanced('(a))')).toBe(false);
});

test('highlight escapes its input and never emits raw markup', () => {
	const html = highlight('<script>', new Set());
	expect(html).toContain('&lt;script&gt;');
	expect(html).not.toContain('<script>');
	// String contents are escaped inside the string span too.
	expect(highlight('"<b>"', new Set())).toBe('<span class="hl-string">&quot;&lt;b&gt;&quot;</span>');
});

test('highlight classifies comments, strings, bar atoms, parens, numbers and vars', () => {
	expect(highlight('; note', new Set())).toBe('<span class="hl-comment">; note</span>');
	expect(highlight('|a b|', new Set())).toBe('<span class="hl-atom">|a b|</span>');
	expect(highlight('(', new Set())).toBe('<span class="hl-paren">(</span>');
	expect(highlight('42', new Set())).toBe('<span class="hl-number">42</span>');
	expect(highlight('-7', new Set())).toBe('<span class="hl-number">-7</span>');
	expect(highlight('0xff', new Set())).toBe('<span class="hl-number">0xff</span>');
	expect(highlight('$x', new Set())).toBe('<span class="hl-var">$x</span>');
	// An unterminated comment/string runs to end of input rather than looping.
	expect(highlight('"abc', new Set())).toBe('<span class="hl-string">&quot;abc</span>');
});

test('highlight marks keywords from the supplied set only', () => {
	expect(highlight('defun', LISP_KEYWORDS)).toContain('hl-keyword');
	expect(highlight('#lang', LISP_KEYWORDS)).toContain('hl-keyword');
	// The same atom is a plain atom under an empty vocabulary.
	expect(highlight('defun', new Set())).toBe('<span class="hl-atom">defun</span>');
});

test('highlight links 64-char hex hashes unless hashLinks is off', () => {
	const hash = 'a'.repeat(64);
	expect(highlight(hash, new Set())).toBe(
		`<a class="hl-hash" href="/view/${hash}" data-hash="${hash}">${hash}</a>`
	);
	expect(highlight(hash, new Set(), { hashLinks: false })).toBe(
		`<span class="hl-atom">${hash}</span>`
	);
});

test('isCodeOutput separates S-expression/hash output from prose', () => {
	expect(isCodeOutput('(a b c)')).toBe(true);
	expect(isCodeOutput('(module\n  (func))')).toBe(true);
	expect(isCodeOutput('b'.repeat(64))).toBe(true);
	expect(isCodeOutput('')).toBe(false);
	expect(isCodeOutput('usage: help — list commands')).toBe(false);
	// A sequence of forms is code …
	expect(isCodeOutput('(a) (b)')).toBe(true);
	// … but a closed form followed by prose on the same line is not.
	expect(isCodeOutput('(a) stored as (b)')).toBe(false);
});

test('calcIndent aligns arguments under the head of a call', () => {
	// `(foo ` → arguments line up after the head plus its space.
	expect(calcIndent('(foo bar', '(foo bar'.length, LISP_SPECIAL_FORMS)).toBe(5);
	// Top level: no open paren, no indent.
	expect(calcIndent('(foo)', 5, LISP_SPECIAL_FORMS)).toBe(0);
	expect(calcIndent('', 0, LISP_SPECIAL_FORMS)).toBe(0);
});

test('calcIndent gives special forms and bare parens a two-column body indent', () => {
	expect(calcIndent('(defun f (x)', '(defun f (x)'.length, LISP_SPECIAL_FORMS)).toBe(2);
	expect(calcIndent('(module', '(module'.length, WAT_SPECIAL_FORMS)).toBe(2);
	// A bare `(` with nothing after it also indents by 2.
	expect(calcIndent('(', 1, LISP_SPECIAL_FORMS)).toBe(2);
});

test('calcIndent tracks nesting and columns across lines', () => {
	const src = '(defun f (x)\n  (cond ';
	// Innermost open form is `(cond ` at column 2 — a special form → 2 + 2.
	expect(calcIndent(src, src.length, LISP_SPECIAL_FORMS)).toBe(4);
	// A closed inner form pops back to the outer one.
	const closed = '(defun f (x)\n  (cond) ';
	expect(calcIndent(closed, closed.length, LISP_SPECIAL_FORMS)).toBe(2);
});

test('calcIndent ignores parens inside strings and only indents to the cursor', () => {
	const src = '(print "(((" ';
	expect(calcIndent(src, src.length, LISP_SPECIAL_FORMS)).toBe(7);
	// Text after the cursor is irrelevant.
	expect(calcIndent('(foo bar)', 5, LISP_SPECIAL_FORMS)).toBe(5);
});
