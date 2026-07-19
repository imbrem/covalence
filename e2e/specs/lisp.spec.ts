/**
 * UI e2e for the /lisp page.
 *
 * LANE-A DEPENDENT: targets the `repl-input` / `repl-cell` / `help-widget` /
 * `example-button` testids being introduced by the frontend rewrite. Failures
 * against an older embedded bundle mean the new page has not landed yet.
 */
import { test, expect } from '@playwright/test';

/** Submit one cell into the page's REPL input. */
async function runCell(page: import('@playwright/test').Page, src: string) {
	const input = page.getByTestId('repl-input');
	await input.click();
	await input.fill(src);
	await input.press('Enter');
}

test('(+ 2 2) evaluates to 4 in the page transcript', async ({ page }) => {
	await page.goto('/lisp');
	await runCell(page, '(+ 2 2)');
	// Scope to the transcript so the echoed input can't satisfy the match.
	await expect(page.getByTestId('repl-output')).toContainText('4', { timeout: 15_000 });
});

test('#help renders the help widget with clickable examples', async ({ page }) => {
	await page.goto('/lisp');
	await runCell(page, '#help');

	const help = page.getByTestId('help-widget');
	await expect(help).toBeVisible({ timeout: 15_000 });
	await expect(help.getByTestId('example-button').first()).toBeVisible();
});

test('clicking an example button grows the transcript', async ({ page }) => {
	await page.goto('/lisp');
	await runCell(page, '#help');

	const help = page.getByTestId('help-widget');
	await expect(help).toBeVisible({ timeout: 15_000 });

	const before = await page.getByTestId('repl-cell').count();
	await help.getByTestId('example-button').first().click();
	await expect
		.poll(() => page.getByTestId('repl-cell').count(), { timeout: 15_000 })
		.toBeGreaterThan(before);
});
