/**
 * UI e2e for the /metamath page: the import dashboard plus the proof surface
 * (step-by-step replay, substitution panel, backward proof builder).
 *
 * The spec uploads `demo0.mm` itself rather than relying on a session someone
 * left on the server. Sessions are keyed by content hash, so the upload is
 * idempotent — re-running the suite reattaches to the same session instead of
 * accumulating copies.
 *
 * demo0 is deliberately tiny (one theorem `th1`, 34 proof steps, axioms
 * a1/a2/mp and the syntax formers), which makes the expected numbers below
 * exact rather than approximate.
 */
import { test, expect, type Page } from '@playwright/test';
import * as fs from 'node:fs';
import * as path from 'node:path';

import { serverUrl } from '../helpers';

const FIXTURES = path.join(__dirname, '../../crates/proof/metamath/tests/fixtures');

/** Upload a fixture `.mm` and return its session hash. */
async function upload(file: string, from: string): Promise<string> {
	const source = fs.readFileSync(path.join(FIXTURES, file), 'utf8');
	const res = await fetch(`${serverUrl()}/api/metamath/upload?from=${from}`, {
		method: 'POST',
		headers: { 'Content-Type': 'text/plain' },
		body: source
	});
	if (!res.ok) throw new Error(`upload ${file} → HTTP ${res.status}`);
	const json = (await res.json()) as { file: string };
	return json.file;
}

/** Open a session view and wait for the theorem list to populate. */
async function openSession(page: Page, hash: string) {
	await page.goto(`/metamath?file=${hash}`);
	await expect(page.locator('.item').first()).toBeVisible({ timeout: 20_000 });
}

/** Open demo0's `th1` with its proof trace rendered. */
async function openTh1(page: Page) {
	await openSession(page, await upload('demo0.mm', 'e2e-demo0'));
	await page.locator('.item', { hasText: 'th1' }).first().click();
	await expect(page.getByTestId('proof-step').first()).toBeVisible({ timeout: 15_000 });
}

/** Open the builder on `goal` and apply `label` to the root. */
async function startBuilder(page: Page, goal: string, label: string) {
	await openSession(page, await upload('demo0.mm', 'e2e-demo0'));
	await page.getByTestId('mode-build').click();
	await page.getByTestId('builder-goal-input').fill(goal);
	await page.getByRole('button', { name: 'Start', exact: true }).click();
	// The search is debounced, so wait on the result rather than a timeout.
	await page.getByTestId('assertion-search-input').fill(label);
	await expect(page.getByTestId('assertion-result').first()).toBeVisible({ timeout: 10_000 });
	await page.getByTestId('assertion-result').first().click();
}

test('the metamath landing page renders', async ({ page }) => {
	await page.goto('/metamath');
	await expect(page.getByRole('heading', { name: /metamath/i }).first()).toBeVisible({
		timeout: 15_000
	});
	// The landing view is the source picker, not a session view.
	await expect(page.getByRole('button', { name: /Download & Import/i })).toBeVisible();
});

test('the sessions list loads', async ({ page }) => {
	const [response] = await Promise.all([
		page.waitForResponse((r) => r.url().includes('/api/metamath/sessions') && r.status() === 200, {
			timeout: 15_000
		}),
		page.goto('/metamath')
	]);
	expect(Array.isArray(await response.json())).toBe(true);
});

test('opening the demo0 session lists th1', async ({ page }) => {
	await openSession(page, await upload('demo0.mm', 'e2e-demo0'));
	await expect(page.locator('.item', { hasText: 'th1' })).toBeVisible();
});

test('selecting th1 shows its 34-step verifying replay', async ({ page }) => {
	await openTh1(page);
	const steps = page.getByTestId('proof-step');
	await expect(steps).toHaveCount(34);
	// Step 0 is th1's first floating hypothesis, pushed onto an empty stack.
	await expect(steps.nth(0)).toContainText('tt');
	await expect(steps.nth(0)).toContainText('term t');
});

test('clicking an assertion step shows the checker-derived substitution', async ({ page }) => {
	await openTh1(page);
	// Step 2 applies `tpl` (term addition) to `term t` and `term 0`.
	await page.getByTestId('proof-step').nth(2).click();
	await expect(page.getByTestId('subst-panel')).toBeVisible();
	await expect(page.getByTestId('subst-label')).toHaveText('tpl');

	// Hypotheses before → after: `tr`'s declared `term r` arrives as `term 0`.
	const hyps = page.getByTestId('subst-hyps');
	await expect(hyps).toContainText('term r');
	await expect(hyps).toContainText('term 0');
	// And the substitution the checker derived, r ↦ 0.
	await expect(page.getByTestId('subst-vars')).toContainText('0');
});

test('proof steps are keyboard navigable', async ({ page }) => {
	await openTh1(page);
	await page.getByTestId('proof-step').nth(0).click();
	await page.locator('.ps-list').focus();
	await page.keyboard.press('j');
	await page.keyboard.press('j');
	await expect(page.locator('.ps-row.sel .idx')).toHaveText('2');
	await page.keyboard.press('k');
	await expect(page.locator('.ps-row.sel .idx')).toHaveText('1');
});

test('the builder searches, applies, and surfaces unsolved variables', async ({ page }) => {
	await startBuilder(page, '|- t = t', 'mp');
	// mp's P occurs only in its hypotheses, so the goal cannot determine it.
	// That is normal and must show as work-to-do, not as an error.
	await expect(page.getByTestId('goal-tree')).toContainText('unsolved');
	await expect(page.getByTestId('goal-node')).toHaveCount(5);
	// Bookkeeping only — the checker has not seen anything yet.
	await expect(page.getByTestId('builder-status')).toContainText('open goal');
});

test('an unmatchable assertion shows the server error verbatim', async ({ page }) => {
	await startBuilder(page, '|- t = t', 'a1');
	await expect(page.getByTestId('apply-error')).toContainText('does not match the goal');
});

test('a closed tree is not "proved" until /verify says so', async ({ page }) => {
	// `|- ( t + 0 ) = t` is a2 with its one float closed by citing `tt`.
	await startBuilder(page, '|- ( t + 0 ) = t', 'a2');
	await page.getByTestId('goal-node').nth(1).click();
	await page.getByTestId('cite-input').fill('tt');
	await page.getByRole('button', { name: 'Cite', exact: true }).click();

	// Every leaf is closed — and the UI still refuses to call it proved.
	await expect(page.getByTestId('builder-status')).toContainText('closed, not yet checked');
	await expect(page.getByTestId('rpn-steps')).toHaveText('tt a2');

	await page.getByTestId('verify-button').click();
	await expect(page.getByTestId('verify-result')).toContainText(
		/verified by the metamath checker/i,
		{ timeout: 15_000 }
	);
	// Only the conclusion /verify actually returned.
	await expect(page.getByTestId('verify-conclusion')).toContainText('= t');
	// The Metamath replay is only half of it: the kernel must independently
	// RE-DERIVE the result, and the page must show that theorem verbatim. This
	// is the construct-don't-trust guarantee, so assert on the real theorem the
	// kernel returned rather than on any prose around it.
	await expect(page.getByTestId('hol-result')).toContainText(/re-derived in the HOL kernel/i);
	await expect(page.getByTestId('hol-thm')).toContainText('Derivable');
	await expect(page.getByTestId('hol-thm')).toContainText('( t + 0 ) = t');
});

test('a bogus proof renders the real checker error', async ({ page }) => {
	await startBuilder(page, '|- ( t + 0 ) = t', 'a2');
	// Cite `tze` (which proves `term 0`) where `term t` is required: well-formed
	// RPN, wrong proof. The checker must be the one that says so.
	await page.getByTestId('goal-node').nth(1).click();
	await page.getByTestId('cite-input').fill('tze');
	await page.getByRole('button', { name: 'Cite', exact: true }).click();
	await page.getByTestId('verify-button').click();

	const result = page.getByTestId('verify-result');
	await expect(result).toBeVisible({ timeout: 15_000 });
	await expect(result).toContainText('but the claimed statement is');
	await expect(result).not.toContainText(/verified/i);
});

test('compressed proofs render their save and heapRef steps', async ({ page }) => {
	// hol.mm's proofs use the compressed format; the sharing must stay visible
	// rather than being silently expanded.
	await openSession(page, await upload('hol.mm', 'e2e-hol'));
	await page.locator('input.search').first().fill('syldan');
	await page.locator('.item', { hasText: 'syldan' }).first().click();
	await expect(page.getByTestId('proof-step').first()).toBeVisible({ timeout: 20_000 });

	// syldan's replay has two save/heapRef pairs; those steps cite no label.
	await expect(page.getByTestId('step-no-label').first()).toBeVisible();
	await expect(page.getByTestId('proof-step').nth(4)).toContainText('save');
	await expect(page.getByTestId('proof-step').nth(12)).toContainText('heap');

	// Clicking the heapRef explains the sharing instead of inlining it.
	await page.getByTestId('proof-step').nth(12).click();
	await expect(page.getByTestId('step-note')).toContainText('heap index');
});
