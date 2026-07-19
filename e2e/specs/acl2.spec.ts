/**
 * UI e2e for the /acl2 page.
 *
 * The page rides POST /api/lisp with a `#lang acl2` cell, so every assertion
 * here is against the REAL server: the expected strings below are the server's
 * actual output (curl'd, not guessed), including the two rejection messages
 * that carry the slice's honesty story.
 */
import { test, expect, type Page } from '@playwright/test';

/**
 * Wait for every cell to have settled.
 *
 * `<Repl>` IGNORES a submit while a cell is in flight (its textarea is never
 * disabled — see the ReplShell invariant), so a test that types into a busy
 * REPL loses the cell silently. Gating on the "proving…" placeholder is what
 * makes a multi-cell test deterministic.
 */
async function settle(page: Page) {
	await expect(page.getByTestId('repl-output')).not.toContainText('proving…', {
		timeout: 20_000
	});
}

/** Submit one cell into the page's REPL input, and wait for its result. */
async function runCell(page: Page, src: string) {
	await settle(page);
	const input = page.getByTestId('repl-input');
	await input.click();
	await input.fill(src);
	await input.press('Enter');
	await settle(page);
}

/**
 * Land on /acl2 with the dialect already open. The page opens `#lang acl2` as
 * a real cell on mount; typing before it lands would interleave with it, so
 * every test waits for it first.
 */
async function openPage(page: Page) {
	await page.goto('/acl2');
	await expect(page.getByTestId('repl-cell').first()).toContainText('#lang acl2 (session reset)', {
		timeout: 15_000
	});
}

test('the page opens the acl2 dialect as a visible first cell', async ({ page }) => {
	await page.goto('/acl2');

	// Visible, not hidden: the opening cell RESETS the server session, so it
	// belongs in the transcript exactly as if it had been typed.
	const first = page.getByTestId('repl-cell').first();
	await expect(first).toContainText('#lang acl2', { timeout: 15_000 });
	await expect(first).toContainText('#lang acl2 (session reset)');
	await expect(page.getByTestId('status-bar')).toContainText('#lang acl2');
});

test('a ground defthm proves, and #show reveals the transported theorem', async ({ page }) => {
	await openPage(page);

	await runCell(page, '(defthm four (equal (+ 2 2) 4))');
	const output = page.getByTestId('repl-output');
	await expect(output).toContainText('four', { timeout: 15_000 });

	// What is STORED is the base-HOL model equation, and `#show` says by which
	// route it was obtained.
	await runCell(page, '#show four');
	await expect(output).toContainText(
		'proved via a reified Derivable_ACL2 certificate + the machine-checked soundness metatheorem, transported to the base-HOL model',
		{ timeout: 15_000 }
	);
	await expect(output).toContainText('⊢');
});

test('a free-variable defthm is rejected — induction is not implemented', async ({ page }) => {
	await openPage(page);

	await runCell(page, '(defun app (x y) (if (consp x) (cons (car x) (app (cdr x) y)) y))');
	await expect(page.getByTestId('repl-output')).toContainText('app', { timeout: 15_000 });

	await runCell(page, '(defthm app-assoc (equal (app (app x y) z) (app x (app y z))))');
	// The server's verbatim rejection — the page must not soften or rewrite it.
	await expect(page.getByTestId('repl-output')).toContainText(
		'defthm `app-assoc` rejected: the goal has free variables (x, y, z) — a universally quantified claim needs induction, which this slice does not implement; only ground decidable goals are accepted',
		{ timeout: 15_000 }
	);
});

test('an inadmissible defun is rejected by the structural-recursion check', async ({ page }) => {
	await openPage(page);

	await runCell(page, '(defun bad (x) (bad x))');
	await expect(page.getByTestId('repl-output')).toContainText(
		'defun `bad` not admitted: not structurally recursive: no formal position decreases',
		{ timeout: 15_000 }
	);
});

test('#help renders the guided tour and a tour example grows the transcript', async ({ page }) => {
	await openPage(page);
	await runCell(page, '#help');

	const help = page.getByTestId('help-widget');
	await expect(help).toBeVisible({ timeout: 15_000 });

	const buttons = help.getByTestId('example-button');
	await expect(buttons.first()).toBeVisible();
	// One button per tour example across all five groups.
	expect(await buttons.count()).toBeGreaterThan(5);

	const before = await page.getByTestId('repl-cell').count();
	await buttons.first().click();
	await expect
		.poll(() => page.getByTestId('repl-cell').count(), { timeout: 15_000 })
		.toBeGreaterThan(before);
});

test('a multi-cell tour example runs its cells in order', async ({ page }) => {
	await openPage(page);
	await runCell(page, '#help');

	const help = page.getByTestId('help-widget');
	await expect(help).toBeVisible({ timeout: 15_000 });

	// "(app '(a b) '(c))" is a two-cell example: the defun, then the call. The
	// call only evaluates if the defun was admitted FIRST.
	const before = await page.getByTestId('repl-cell').count();
	await help.getByTestId('example-button').filter({ hasText: "(app '(a b) '(c))" }).click();
	await expect
		.poll(() => page.getByTestId('repl-cell').count(), { timeout: 20_000 })
		.toBe(before + 2);
	await expect(page.getByTestId('repl-output')).toContainText('(a b c)');
});
