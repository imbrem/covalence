<script lang="ts">
	import { browser } from '$app/environment';

	// The kernel runs *in the browser*: this page loads the wasm-bindgen build of
	// `covalence-web-kernel` (over `covalence-kernel::service`) and checks a `.cov`
	// article client-side — no server round-trip. See docs/web-kernel.md.

	type Diagnostic = { severity: 'error' | 'warning' | 'info'; message: string; span: null | { start: number; end: number } };
	type TheoremInfo = { name: string; statement: string };
	type CheckReport = { ok: boolean; theorems: TheoremInfo[]; diagnostics: Diagnostic[] };

	const SAMPLE = `;; A self-contained .cov article. The kernel re-derives every theorem.
(#import core)
(#open core)

(#thm truth
  (#concl true)
  (#proof (eq-mp (reduce-prim (= true true)) (refl true))))
`;

	let src = $state(SAMPLE);
	let report = $state<CheckReport | null>(null);
	let kernelCheck = $state<((src: string) => string) | null>(null);
	let status = $state<'loading' | 'ready' | 'error'>('loading');
	let loadError = $state('');
	let checking = $state(false);

	// Cache check results by exact source string so re-checking unchanged text
	// (e.g. after an edit-then-undo) is instant.
	const cache = new Map<string, CheckReport>();

	// --- Kernel load ---
	// NOTE: this used to live in `onMount`, but `onMount` callbacks were never
	// firing for this route (only `$effect`/`setTimeout` ran). `$effect` is the
	// reliable Svelte 5 mount hook here (it's what the REPL route uses too), so
	// the kernel load now runs from an effect that fires exactly once.
	let loadStarted = false;
	$effect(() => {
		if (!browser || loadStarted) return;
		loadStarted = true;
		loadKernel();
	});

	async function loadKernel() {
		// Guard: never leave the badge stuck on "loading" forever.
		const timeout = setTimeout(() => {
			if (status === 'loading') {
				status = 'error';
				loadError = 'Timed out loading the wasm kernel (no response after 20s).';
			}
		}, 20000);
		try {
			const mod = await import('$lib/kernel/covalence_web_kernel.js');
			const wasmUrl = (await import('$lib/kernel/covalence_web_kernel_bg.wasm?url')).default;
			// Modern wasm-bindgen init form (object), avoids the deprecated
			// string-URL path.
			await mod.default({ module_or_path: wasmUrl });
			kernelCheck = mod.check;
			status = 'ready';
			runCheck(src);
		} catch (e) {
			status = 'error';
			loadError = e instanceof Error ? e.message : String(e);
		} finally {
			clearTimeout(timeout);
		}
	}

	// --- Checking ---
	function runCheck(source: string) {
		if (!kernelCheck) return;
		const cached = cache.get(source);
		if (cached) {
			report = cached;
			checking = false;
			return;
		}
		let result: CheckReport;
		try {
			result = JSON.parse(kernelCheck(source)) as CheckReport;
		} catch (e) {
			result = { ok: false, theorems: [], diagnostics: [{ severity: 'error', message: String(e), span: null }] };
		}
		cache.set(source, result);
		report = result;
		checking = false;
	}

	let debounceTimer: ReturnType<typeof setTimeout> | undefined;
	const DEBOUNCE_MS = 300;

	function onInput() {
		if (status !== 'ready') return;
		// Cached source → reflect instantly, skip the "checking" flicker.
		if (cache.has(src)) {
			runCheck(src);
			return;
		}
		checking = true;
		clearTimeout(debounceTimer);
		debounceTimer = setTimeout(() => runCheck(src), DEBOUNCE_MS);
	}

	function checkNow() {
		clearTimeout(debounceTimer);
		runCheck(src);
	}

	// --- Dark mode ---
	type Theme = 'light' | 'dark';
	let theme = $state<Theme>('dark');

	$effect(() => {
		if (!browser) return;
		const stored = localStorage.getItem('cov-theme');
		if (stored === 'light' || stored === 'dark') {
			theme = stored;
		} else {
			theme = window.matchMedia('(prefers-color-scheme: light)').matches ? 'light' : 'dark';
		}
	});

	$effect(() => {
		if (!browser) return;
		document.documentElement.dataset.theme = theme;
	});

	function toggleTheme() {
		theme = theme === 'dark' ? 'light' : 'dark';
		if (browser) localStorage.setItem('cov-theme', theme);
	}

	// --- Syntax highlighting (overlay pattern, matching the REPL route) ---
	// Known rule / keyword tokens that appear in `.cov` proof scripts.
	const KEYWORDS = new Set([
		'eq-mp', 'refl', 'reduce-prim', 'trans', 'sym', 'beta', 'eta',
		'mk-comb', 'abs', 'assume', 'deduct', 'inst', 'inst-type',
		'and-intro', 'and-elim', 'or-intro', 'or-elim', 'not-intro', 'not-elim',
		'imp-intro', 'imp-elim', 'all-intro', 'all-elim', 'exists-intro', 'exists-elim',
		'define', 'new-type', 'spec-abs', 'spec-rep', 'unfold', 'fold',
		'true', 'false', 'forall', 'exists', 'lambda', 'let', 'fun',
	]);
	function escHtml(s: string): string {
		return s.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;').replace(/"/g, '&quot;').replace(/'/g, '&#39;');
	}

	function highlight(text: string): string {
		let out = '';
		let i = 0;
		while (i < text.length) {
			const ch = text[i];
			// Block comment (; ... ;)
			if (ch === '(' && text[i + 1] === ';') {
				const end = text.indexOf(';)', i + 2);
				const stop = end === -1 ? text.length : end + 2;
				out += `<span class="hl-comment">${escHtml(text.slice(i, stop))}</span>`;
				i = stop;
			} else if (ch === ';') {
				// Line comment ;;...  (a single ; also reads as a comment here)
				let end = text.indexOf('\n', i);
				if (end === -1) end = text.length;
				out += `<span class="hl-comment">${escHtml(text.slice(i, end))}</span>`;
				i = end;
			} else if (ch === '|') {
				let end = text.indexOf('|', i + 1);
				if (end === -1) end = text.length; else end++;
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
				let cls: string;
				if (atom.startsWith('#')) cls = 'hl-directive';
				else if (KEYWORDS.has(atom)) cls = 'hl-keyword';
				else if (/^-?[0-9]/.test(atom) || /^0x[0-9a-fA-F]+$/.test(atom)) cls = 'hl-number';
				else if (atom.startsWith('$')) cls = 'hl-var';
				else cls = 'hl-atom';
				out += `<span class="${cls}">${escHtml(atom)}</span>`;
				i = end;
			}
		}
		return out;
	}

	let highlighted = $derived(highlight(src));

	// Scroll-sync the highlight layer to the textarea.
	let highlightEl = $state<HTMLPreElement | null>(null);
	function syncScroll(e: Event) {
		const ta = e.target as HTMLTextAreaElement;
		if (highlightEl) {
			highlightEl.scrollTop = ta.scrollTop;
			highlightEl.scrollLeft = ta.scrollLeft;
		}
	}
</script>

<svelte:head><title>Covalence — article check</title></svelte:head>

<main>
	<header>
		<div class="title">
			<h1>Covalence — in-browser proof check</h1>
			<button class="theme-toggle" onclick={toggleTheme} title="Toggle light/dark" aria-label="Toggle theme">
				{theme === 'dark' ? '☀' : '☾'}
			</button>
		</div>
		<p class="sub">
			The kernel is compiled to WebAssembly and runs entirely in your browser.
			{#if status === 'loading'}<span class="badge loading">loading kernel…</span>
			{:else if status === 'ready'}<span class="badge ok">kernel ready</span>
			{:else}<span class="badge err">kernel failed to load</span>{/if}
		</p>
	</header>

	{#if status === 'error'}
		<pre class="fatal">Failed to load the wasm kernel: {loadError}

Did you run `bun run build:web-kernel` first? It emits the glue into
apps/covalence-web/src/lib/kernel/.</pre>
	{/if}

	<div class="cols">
		<section class="editor">
			<div class="editor-wrap">
				<pre class="editor-highlight" aria-hidden="true" bind:this={highlightEl}>{@html highlighted}&nbsp;</pre>
				<textarea
					bind:value={src}
					spellcheck="false"
					oninput={onInput}
					onscroll={syncScroll}
				></textarea>
			</div>
			<div class="editor-bar">
				<button onclick={checkNow} disabled={status !== 'ready'}>Check</button>
				{#if checking}<span class="checking">checking…</span>{/if}
			</div>
		</section>

		<section class="result">
			{#if report}
				<p class="verdict {report.ok ? 'ok' : 'err'}">
					{report.ok ? '✓ checked' : '✗ failed'} —
					{report.theorems.length} theorem{report.theorems.length === 1 ? '' : 's'}
				</p>

				{#if report.theorems.length}
					<h2>Theorems</h2>
					<ul class="thms">
						{#each report.theorems as t}
							<li><span class="name">{t.name}</span> <code>{t.statement}</code></li>
						{/each}
					</ul>
				{/if}

				{#if report.diagnostics.length}
					<h2>Diagnostics</h2>
					<ul class="diags">
						{#each report.diagnostics as d}
							<li class={d.severity}>{d.message}</li>
						{/each}
					</ul>
				{/if}
			{:else if status === 'ready'}
				<p class="muted">Edit the article to check it.</p>
			{:else if status === 'loading'}
				<p class="muted">Loading the kernel…</p>
			{/if}
		</section>
	</div>
</main>

<style>
	/* Palette: light/dark via [data-theme] on <html>. The global app.css sets a
	   dark :root; we override per-theme here with page-local custom properties. */
	main {
		--a-bg: #ffffff;
		--a-fg: #1a1a1a;
		--a-muted: #6b7280;
		--a-surface: #f7f7f8;
		--a-border: #d1d5db;
		--a-accent: #6d28d9;
		--a-ok-bg: #dcfce7;
		--a-ok-fg: #166534;
		--a-err-bg: #fee2e2;
		--a-err-fg: #991b1b;
		--a-warn-bg: #fef3c7;
		--a-warn-fg: #92400e;
		--hl-comment: #6b7280;
		--hl-string: #047857;
		--hl-keyword: #2563eb;
		--hl-directive: #9333ea;
		--hl-number: #b45309;
		--hl-var: #be185d;
		--hl-paren: #9ca3af;
		--hl-atom: #1a1a1a;

		max-width: 70rem;
		margin: 0 auto;
		padding: 1.5rem;
		font-family: system-ui, sans-serif;
		background: var(--a-bg);
		color: var(--a-fg);
		min-height: 100vh;
	}

	:global(html[data-theme='dark']) main {
		--a-bg: #0e0e10;
		--a-fg: #e0e0e0;
		--a-muted: #8b8b92;
		--a-surface: #1a1a1e;
		--a-border: #2a2a2e;
		--a-accent: #a78bfa;
		--a-ok-bg: #14321f;
		--a-ok-fg: #4ade80;
		--a-err-bg: #3a1a1a;
		--a-err-fg: #f87171;
		--a-warn-bg: #3a2e12;
		--a-warn-fg: #fbbf24;
		--hl-comment: #6b7280;
		--hl-string: #a8e6a3;
		--hl-keyword: #7cc4f5;
		--hl-directive: #c9a0f5;
		--hl-number: #f5c07c;
		--hl-var: #f5a3c7;
		--hl-paren: #6b7280;
		--hl-atom: #e0e0e0;
	}

	.title { display: flex; align-items: center; justify-content: space-between; gap: 1rem; }
	h1 { font-size: 1.4rem; margin: 0 0 0.25rem; }
	.theme-toggle {
		font-size: 1.1rem; line-height: 1; padding: 0.35rem 0.6rem; cursor: pointer;
		border: 1px solid var(--a-border); border-radius: 0.5rem;
		background: var(--a-surface); color: var(--a-fg);
	}
	.theme-toggle:hover { border-color: var(--a-accent); }
	.sub { color: var(--a-muted); margin: 0 0 1rem; }
	.badge { font-size: 0.8rem; padding: 0.1rem 0.5rem; border-radius: 1rem; margin-left: 0.5rem; }
	.badge.loading { background: var(--a-warn-bg); color: var(--a-warn-fg); }
	.badge.ok { background: var(--a-ok-bg); color: var(--a-ok-fg); }
	.badge.err { background: var(--a-err-bg); color: var(--a-err-fg); }

	.cols { display: grid; grid-template-columns: 1fr 1fr; gap: 1rem; }
	@media (max-width: 50rem) { .cols { grid-template-columns: 1fr; } }

	/* --- Editor: highlighted <pre> behind a transparent <textarea> --- */
	.editor-wrap { position: relative; height: 24rem; }
	.editor-highlight,
	.editor-wrap textarea {
		position: absolute;
		top: 0; left: 0;
		width: 100%; height: 100%;
		font-family: ui-monospace, 'JetBrains Mono', monospace;
		font-size: 0.85rem;
		line-height: 1.5;
		padding: 0.75rem;
		border: 1px solid var(--a-border);
		border-radius: 0.5rem;
		box-sizing: border-box;
		white-space: pre;
		overflow: auto;
		margin: 0;
		tab-size: 2;
	}
	.editor-highlight {
		pointer-events: none;
		background: var(--a-surface);
		color: var(--hl-atom);
		z-index: 0;
	}
	.editor-wrap textarea {
		background: transparent;
		color: transparent;
		caret-color: var(--a-fg);
		resize: none;
		z-index: 1;
	}
	.editor-wrap textarea:focus { outline: 2px solid var(--a-accent); outline-offset: -1px; }

	.editor-bar { display: flex; align-items: center; gap: 0.75rem; margin-top: 0.5rem; }
	button {
		padding: 0.4rem 1rem; border-radius: 0.4rem;
		border: 1px solid var(--a-border); background: var(--a-surface); color: var(--a-fg);
		cursor: pointer;
	}
	button:hover:not(:disabled) { border-color: var(--a-accent); }
	button:disabled { opacity: 0.5; cursor: default; }
	.checking { font-size: 0.8rem; color: var(--a-muted); font-style: italic; }

	.result { border: 1px solid var(--a-border); border-radius: 0.5rem; padding: 0.75rem 1rem; background: var(--a-surface); }
	.verdict { font-weight: 600; }
	.verdict.ok { color: var(--a-ok-fg); }
	.verdict.err { color: var(--a-err-fg); }
	h2 { font-size: 0.95rem; margin: 0.75rem 0 0.25rem; }
	.thms { list-style: none; padding: 0; }
	.thms li { padding: 0.3rem 0; border-bottom: 1px solid var(--a-border); }
	.thms .name { font-weight: 600; margin-right: 0.5rem; }
	.thms code { font-size: 0.8rem; color: var(--a-muted); font-family: ui-monospace, monospace; }
	.diags { padding-left: 1rem; }
	.diags li.error { color: var(--a-err-fg); }
	.diags li.warning { color: var(--a-warn-fg); }
	.muted { color: var(--a-muted); }
	.fatal {
		background: var(--a-err-bg); color: var(--a-err-fg);
		padding: 0.75rem; border-radius: 0.5rem; white-space: pre-wrap;
		font-family: ui-monospace, monospace; font-size: 0.8rem; margin-bottom: 1rem;
	}

	/* --- Syntax highlight token colors --- */
	.editor-highlight :global(.hl-comment) { color: var(--hl-comment); font-style: italic; }
	.editor-highlight :global(.hl-string) { color: var(--hl-string); }
	.editor-highlight :global(.hl-keyword) { color: var(--hl-keyword); }
	.editor-highlight :global(.hl-directive) { color: var(--hl-directive); font-weight: 600; }
	.editor-highlight :global(.hl-number) { color: var(--hl-number); }
	.editor-highlight :global(.hl-var) { color: var(--hl-var); }
	.editor-highlight :global(.hl-paren) { color: var(--hl-paren); }
	.editor-highlight :global(.hl-atom) { color: var(--hl-atom); }
</style>
