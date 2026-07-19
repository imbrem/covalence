/**
 * UI e2e for the main page's WebSocket REPL (`/api/repl`).
 *
 * LANE-A DEPENDENT: targets the `repl-input` / `repl-output` / `status-bar`
 * testids being introduced by the frontend rewrite. Against an older embedded
 * bundle these fail on selector timeout — that is drift, not a backend fault;
 * api.spec.ts is the bundle-independent signal.
 */
import { test, expect } from '@playwright/test';

test('main page loads and the REPL input is reachable', async ({ page }) => {
	await page.goto('/');
	await expect(page.getByTestId('repl-input')).toBeVisible();
});

test('status bar reports a healthy backend', async ({ page }) => {
	await page.goto('/');
	const status = page.getByTestId('status-bar');
	await expect(status).toBeVisible();
	// The health poll is periodic; give it a beat to land.
	await expect(status).toContainText(/ok|healthy|connected/i, { timeout: 15_000 });
});

test('typing help over the WS REPL produces output', async ({ page }) => {
	await page.goto('/');
	const input = page.getByTestId('repl-input');
	await input.click();
	await input.fill('help');
	await input.press('Enter');

	const output = page.getByTestId('repl-output');
	// `help` echoes the command list; any of these words means the socket
	// round-tripped, which is what this spec is actually about.
	await expect(output).toContainText(/help|store|status/i, { timeout: 15_000 });
});
