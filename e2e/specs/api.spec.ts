/**
 * API-level e2e: the HTTP surface the web app is built on, exercised with no
 * browser involved. These specs depend only on the server and must pass on
 * any build — a failure here is a backend regression, not a UI drift.
 */
import { test, expect } from '@playwright/test';

import { evalCell, resetSession, serverUrl, sessionId } from '../helpers';

test('GET /api/health reports ok', async () => {
	const res = await fetch(`${serverUrl()}/api/health`);
	expect(res.ok).toBe(true);
	const body = (await res.json()) as { status: string; version: string };
	expect(body.status).toBe('ok');
	expect(typeof body.version).toBe('string');
});

test('lisp: (+ 2 2) evaluates to 4', async () => {
	const out = await evalCell('lisp', sessionId('lisp-add'), '(+ 2 2)');
	expect(out).toEqual({ ok: true, result: '4' });
});

test('lisp: a #lang scheme defun persists across cells in one session', async () => {
	const session = sessionId('lisp-defun');
	// `#lang` must be its own cell and RESETS the session, so it goes first.
	expect(await evalCell('lisp', session, '#lang scheme')).toMatchObject({ ok: true });
	expect(await evalCell('lisp', session, '(defun ident (x) x)')).toEqual({
		ok: true,
		result: 'ident'
	});
	// The defun rides the next cell's theorem as a hypothesis — this is the
	// cross-cell session state the /lisp page depends on.
	expect(await evalCell('lisp', session, '(ident (quote hello))')).toEqual({
		ok: true,
		result: 'hello'
	});
});

test('lisp: a stuck term comes back as { ok: false, error }', async () => {
	const out = await evalCell('lisp', sessionId('lisp-err'), '(no-such-op 1)');
	expect(out.ok).toBe(false);
	if (out.ok) throw new Error('unreachable');
	expect(out.error).toContain('no-such-op');
});

test('lisp: reset drops accumulated defuns', async () => {
	const session = sessionId('lisp-reset');
	await evalCell('lisp', session, '#lang scheme');
	await evalCell('lisp', session, '(defun ident (x) x)');
	expect(await evalCell('lisp', session, '(ident (quote hi))')).toEqual({
		ok: true,
		result: 'hi'
	});

	await resetSession('lisp', session);

	// Post-reset the session is a fresh default-dialect one: `ident` is gone.
	const after = await evalCell('lisp', session, '(ident (quote hi))');
	expect(after.ok).toBe(false);
});

test('forsp: 2 2 + evaluates to 4', async () => {
	const out = await evalCell('forsp', sessionId('forsp-add'), '2 2 +');
	expect(out).toEqual({ ok: true, result: '4' });
});

test('GET /api/metamath/sessions returns a list', async () => {
	const res = await fetch(`${serverUrl()}/api/metamath/sessions`);
	expect(res.ok).toBe(true);
	expect(Array.isArray(await res.json())).toBe(true);
});
