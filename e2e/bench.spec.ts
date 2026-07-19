/**
 * Latency measurements, not tests. Run with `bun run bench:web`; the default
 * `chromium` project does not pick this file up.
 *
 * Numbers are console-logged. The only assertions are sanity ones (the work
 * actually happened) — a benchmark that fails a threshold on a loaded laptop
 * would be noise, not signal.
 */
import { test, expect } from '@playwright/test';

import { evalCell, sessionId } from './helpers';

const ITERATIONS = 20;

function percentile(sorted: number[], p: number): number {
	// Nearest-rank on an ascending array.
	const idx = Math.min(sorted.length - 1, Math.ceil((p / 100) * sorted.length) - 1);
	return sorted[idx];
}

function report(label: string, samples: number[]) {
	const sorted = [...samples].sort((a, b) => a - b);
	const mean = samples.reduce((a, b) => a + b, 0) / samples.length;
	console.log(
		`[bench] ${label}: n=${samples.length} ` +
			`p50=${percentile(sorted, 50).toFixed(1)}ms ` +
			`p95=${percentile(sorted, 95).toFixed(1)}ms ` +
			`mean=${mean.toFixed(1)}ms ` +
			`min=${sorted[0].toFixed(1)}ms max=${sorted[sorted.length - 1].toFixed(1)}ms`
	);
}

for (const dialect of ['lisp', 'scheme'] as const) {
	test(`/api/lisp (+ 2 2) latency — ${dialect}`, async () => {
		test.setTimeout(120_000);
		const session = sessionId(`bench-${dialect}`);
		if (dialect === 'scheme') {
			// `#lang` resets the session, so switch once up front.
			expect(await evalCell('lisp', session, '#lang scheme')).toMatchObject({ ok: true });
		}

		// One warm-up outside the sample set: the first cell in a session pays
		// for kernel session construction.
		await evalCell('lisp', session, '(+ 2 2)');

		const samples: number[] = [];
		for (let i = 0; i < ITERATIONS; i++) {
			const t0 = performance.now();
			const out = await evalCell('lisp', session, '(+ 2 2)');
			samples.push(performance.now() - t0);
			expect(out).toEqual({ ok: true, result: '4' });
		}
		report(`lisp eval (+ 2 2) [${dialect}]`, samples);
	});
}

test('main page load-to-interactive', async ({ page }) => {
	test.setTimeout(120_000);
	const t0 = performance.now();
	await page.goto('/', { waitUntil: 'load' });
	const loaded = performance.now() - t0;

	// "Interactive" = the SPA has hydrated far enough to paint its body text.
	await page.locator('body').waitFor({ state: 'visible' });
	const interactive = performance.now() - t0;

	console.log(
		`[bench] main page: load=${loaded.toFixed(1)}ms interactive=${interactive.toFixed(1)}ms`
	);
	expect(interactive).toBeGreaterThan(0);
});
