/**
 * Playwright e2e config for the covalence web app.
 *
 * Two projects:
 *   - `chromium` — the functional specs under e2e/specs/.
 *   - `bench`    — e2e/bench.spec.ts, latency measurements only.
 *
 * Bare `playwright test` runs every project, so both entry points select one:
 * `bun run test:e2e` passes `--project chromium`, `bun run bench:web` passes
 * `--project bench`. Keep that flag on the scripts — without it a plain run
 * would drag the benchmarks into the functional suite.
 *
 * Server lifecycle: global-setup spawns a prebuilt `target/debug/cov serve`
 * on a free port with isolated XDG dirs (same pattern as tests/e2e.test.ts)
 * and exports COV_E2E_URL; global-teardown kills it. Setting COV_E2E_URL in
 * the environment beforehand skips the spawn entirely — use that to point the
 * suite at `bun run dev:web` or any already-running server.
 */
import { defineConfig, devices, chromium } from '@playwright/test';
import { execFileSync } from 'node:child_process';
import * as fs from 'node:fs';
import * as path from 'node:path';

// Playwright's downloaded chromium is a stock Linux build; on NixOS its ELF
// interpreter is absent and it cannot exec. Probe the bundled binary once and
// fall back to a system chromium when it can't run. COV_E2E_CHROMIUM
// overrides the whole dance. `undefined` means "let Playwright use its own".
function chromiumExecutable(): string | undefined {
	if (process.env.COV_E2E_CHROMIUM) return process.env.COV_E2E_CHROMIUM;
	try {
		execFileSync(chromium.executablePath(), ['--version'], { stdio: 'ignore' });
		return undefined;
	} catch {
		for (const p of [
			'/run/current-system/sw/bin/chromium',
			'/usr/bin/chromium',
			'/usr/bin/chromium-browser',
			'/usr/bin/google-chrome'
		]) {
			if (fs.existsSync(p)) return p;
		}
		return undefined;
	}
}

const executablePath = chromiumExecutable();

export default defineConfig({
	testDir: __dirname,
	globalSetup: path.join(__dirname, 'global-setup.ts'),
	globalTeardown: path.join(__dirname, 'global-teardown.ts'),
	outputDir: path.join(__dirname, 'test-results'),
	reporter: [
		['list'],
		['html', { open: 'never', outputFolder: path.join(__dirname, 'playwright-report') }]
	],
	// The server is a single shared process with per-session state keyed by
	// client-chosen ids, so parallel workers are safe — but keep it modest.
	workers: 2,
	use: {
		// Set at config load when provided externally; otherwise global-setup
		// exports it before the workers (which re-evaluate this config) start.
		baseURL: process.env.COV_E2E_URL,
		trace: 'retain-on-failure',
		screenshot: 'only-on-failure',
		launchOptions: executablePath ? { executablePath } : {}
	},
	projects: [
		{
			name: 'chromium',
			testDir: path.join(__dirname, 'specs'),
			use: { ...devices['Desktop Chrome'] }
		},
		{
			name: 'bench',
			testMatch: /bench\.spec\.ts$/,
			// Latency numbers: sequential, one worker, no parallelism.
			fullyParallel: false,
			use: { ...devices['Desktop Chrome'] }
		}
	]
});
