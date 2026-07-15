import { expect, test } from 'vitest';
import {
	DEFAULT_LANG,
	canonicalLang,
	dialectAfter,
	dialectsOf,
	langDirective
} from './lispDialect';
import examples from './lispExamples.json';

test('canonicalLang resolves server aliases, case-insensitively', () => {
	expect(canonicalLang('lisp')).toBe('lisp');
	expect(canonicalLang('lisp-int')).toBe('lisp');
	expect(canonicalLang('INT')).toBe('lisp');
	expect(canonicalLang('value')).toBe('scheme');
	expect(canonicalLang('Scheme')).toBe('scheme');
	expect(canonicalLang('sector')).toBe('sector');
	expect(canonicalLang('nope')).toBeNull();
});

test('langDirective picks out `#lang NAME` cells only', () => {
	expect(langDirective('#lang scheme')).toBe('scheme');
	expect(langDirective('  #lang sector  ')).toBe('sector');
	// A bare `#lang` reports the current dialect — it never switches.
	expect(langDirective('#lang')).toBeNull();
	expect(langDirective('(+ 2 2)')).toBeNull();
	expect(langDirective('#show (+ 2 2)')).toBeNull();
});

test('dialectAfter switches on an ok #lang cell, preferring the server echo', () => {
	// The server echoes the canonical name — trust it (covers future dialects).
	expect(dialectAfter('#lang scheme', true, '#lang scheme (session reset)')).toBe('scheme');
	// Alias in, canonical echoed out.
	expect(dialectAfter('#lang int', true, '#lang lisp (session reset)')).toBe('lisp');
	// No recognizable echo → fall back to the (canonicalized) argument.
	expect(dialectAfter('#lang VALUE', true, 'ok')).toBe('scheme');
	// Unknown-to-the-client but server-accepted name still tracks (lowercased).
	expect(dialectAfter('#lang acl2', true, 'switched')).toBe('acl2');
});

test('dialectAfter leaves the dialect unchanged otherwise', () => {
	// Errors (e.g. unknown dialect) do not switch.
	expect(dialectAfter('#lang nope', false, '')).toBeNull();
	// Ordinary cells and other directives do not switch.
	expect(dialectAfter('(+ 2 2)', true, '4')).toBeNull();
	expect(dialectAfter('#show (+ 2 2)', true, '…')).toBeNull();
	// A bare `#lang` (a report) does not switch.
	expect(dialectAfter('#lang', true, 'current #lang: lisp\navailable: …')).toBeNull();
});

test('dialectsOf lists distinct dialects in first-appearance order', () => {
	expect(dialectsOf([{ lang: 'a' }, { lang: 'b' }, { lang: 'a' }])).toEqual(['a', 'b']);
});

test('the shipped examples are grouped by known dialects, default first', () => {
	const dialects = dialectsOf(examples);
	expect(dialects[0]).toBe(DEFAULT_LANG);
	for (const d of dialects) expect(canonicalLang(d)).toBe(d);
	// Example cells are plain forms/directives — dialect switches are the page's
	// tabs, not example entries.
	for (const e of examples) expect(langDirective(e.src)).toBeNull();
});
