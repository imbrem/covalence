<script lang="ts">
	import { browser } from '$app/environment';

	// The kernel runs *in the browser*: this page loads the wasm-bindgen build of
	// `covalence-web-kernel` (over `covalence-kernel::service`) and checks a `.cov`
	// article client-side — no server round-trip. See docs/web-kernel.md.
	//
	// The showcase: the SAME proof source is replayed against two different
	// *models* (carriers) via `check_model(src, model)`. `nat/self` proves over
	// the kernel's `nat` (integer commutativity); `nat/unary` proves the very
	// same script over `list unit` (append commutativity). Switching the model
	// re-checks the identical text and yields a *different* theorem statement.

	type Diagnostic = { severity: 'error' | 'warning' | 'info'; message: string; span: null | { start: number; end: number } };
	type TheoremInfo = { name: string; statement: string };
	type CheckReport = { ok: boolean; theorems: TheoremInfo[]; diagnostics: Diagnostic[] };

	type ModelId = 'nat/self' | 'nat/unary';
	const MODELS: { id: ModelId; label: string; carrier: string; blurb: string }[] = [
		{ id: 'nat/self', label: 'nat/self', carrier: 'nat', blurb: "the kernel's native nat (nat.add)" },
		{ id: 'nat/unary', label: 'nat/unary', carrier: 'list unit', blurb: 'unary numerals as list unit (list.cat)' }
	];

	const SAMPLE = `;; Addition is commutative — proved ONCE against the abstract Nat interface,
;; then replayed at any *model*. Pick a model on the right:
;;   - nat/self   the carrier is the kernel's \`nat\`   (integer commutativity)
;;   - nat/unary  the carrier is \`list unit\`          (append commutativity)
;; The SAME proof below checks at both. Try switching the model!

(#import core)
(#open core)
(#import natmodel)
(#open natmodel)

;; |- forall a b. a + b = b + a   (over the model's \`m.add\`), by induction on a.
(#thm add.comm
  (#concl (forall (a) (forall (b) (= (m.add a b) (m.add b a)))))
  (#by
    (m.induct a
      ;; base: 0 + b = b + 0
      (#by
        (intro b)
        (rw (all-elim b (zero.add)))
        (sym)
        (rw (all-elim b (add.zero)))
        (refl))
      ;; step: S a + b = b + S a
      (#by
        (intro b)
        (rw (all-elim b (all-elim a (succ.add))))
        (rw (all-elim b (assume (forall (b) (= (m.add a b) (m.add b a))))))
        (sym)
        (rw (all-elim a (all-elim b (add.succ))))
        (refl)))))
`;

	let src = $state(SAMPLE);
	let model = $state<ModelId>('nat/self');
	let report = $state<CheckReport | null>(null);
	let status = $state<'loading' | 'ready' | 'error'>('loading');
	let loadError = $state('');
	let checking = $state(false);

	// The kernel now runs in a Web Worker so a heavy check (notably `nat/unary`)
	// no longer blocks the UI thread. We talk to it by id-tagged messages and
	// resolve each in-flight check against a pending-requests map.
	let worker: Worker | null = null;
	let nextReqId = 0;
	const pending = new Map<number, (json: string) => void>();

	const activeModel = $derived(MODELS.find((m) => m.id === model) ?? MODELS[0]);

	// Cache check results by `model + " " + src`: the same source at different
	// models yields different theorems, so the model MUST be part of the key.
	const cache = new Map<string, CheckReport>();
	const cacheKey = (m: ModelId, source: string) => `${m} ${source}`;

	// --- Kernel load (in a Web Worker) ---
	// NOTE: this used to live in `onMount`, but `onMount` callbacks were never
	// firing for this route (only `$effect`/`setTimeout` ran). `$effect` is the
	// reliable Svelte 5 mount hook here (it's what the REPL route uses too), so
	// the worker spawn now runs from an effect that fires exactly once.
	let loadStarted = false;
	$effect(() => {
		if (!browser || loadStarted) return;
		loadStarted = true;
		spawnWorker();
	});

	function spawnWorker() {
		// Guard: never leave the badge stuck on "loading" forever (e.g. a worker
		// that never finishes initing the wasm kernel) — surface a visible error.
		const timeout = setTimeout(() => {
			if (status === 'loading') {
				status = 'error';
				loadError = 'Timed out loading the wasm kernel in the worker (no response after 20s).';
			}
		}, 20000);
		try {
			// Vite needs a statically-analyzable `new URL(..., import.meta.url)`
			// to bundle the worker. Module worker so it can `import` the glue.
			worker = new Worker(new URL('$lib/kernel.worker.ts', import.meta.url), {
				type: 'module',
			});
			worker.onmessage = (ev: MessageEvent) => {
				const msg = ev.data;
				if (msg?.type === 'ready') {
					clearTimeout(timeout);
					status = 'ready';
					runCheck(model, src);
				} else if (msg?.type === 'error') {
					clearTimeout(timeout);
					status = 'error';
					loadError = msg.message ?? 'worker reported an unknown error';
				} else if (msg?.type === 'result') {
					const resolve = pending.get(msg.id);
					if (resolve) {
						pending.delete(msg.id);
						resolve(msg.json);
					}
				}
			};
			worker.onerror = (ev) => {
				clearTimeout(timeout);
				status = 'error';
				loadError = ev.message || 'worker failed to load';
			};
		} catch (e) {
			clearTimeout(timeout);
			status = 'error';
			loadError = e instanceof Error ? e.message : String(e);
		}
	}

	// Ask the worker to check; resolves with the raw JSON string.
	function checkInWorker(source: string, m: ModelId): Promise<string> {
		return new Promise((resolve) => {
			if (!worker) {
				resolve(
					JSON.stringify({
						ok: false,
						theorems: [],
						diagnostics: [{ severity: 'error', message: 'kernel worker not available', span: null }],
					}),
				);
				return;
			}
			const id = nextReqId++;
			pending.set(id, resolve);
			worker.postMessage({ type: 'check', id, src: source, model: m });
		});
	}

	// --- Checking ---
	// Tracks the latest requested (model, source) so a slow in-flight check that
	// resolves after the user has moved on doesn't clobber the current view.
	let checkSeq = 0;

	async function runCheck(m: ModelId, source: string) {
		const key = cacheKey(m, source);
		const cached = cache.get(key);
		if (cached) {
			report = cached;
			checking = false;
			return;
		}
		const seq = ++checkSeq;
		checking = true;
		const json = await checkInWorker(source, m);
		let result: CheckReport;
		try {
			result = JSON.parse(json) as CheckReport;
		} catch (e) {
			result = { ok: false, theorems: [], diagnostics: [{ severity: 'error', message: String(e), span: null }] };
		}
		cache.set(key, result);
		// Stale guard: only apply if this is still the most recent check.
		if (seq === checkSeq) {
			report = result;
			checking = false;
		}
	}

	let debounceTimer: ReturnType<typeof setTimeout> | undefined;
	const DEBOUNCE_MS = 300;

	function scheduleCheck() {
		if (status !== 'ready') return;
		// Cached → reflect instantly, skip the "checking" flicker.
		if (cache.has(cacheKey(model, src))) {
			runCheck(model, src);
			return;
		}
		checking = true;
		clearTimeout(debounceTimer);
		debounceTimer = setTimeout(() => runCheck(model, src), DEBOUNCE_MS);
	}

	function onInput() {
		scheduleCheck();
	}

	function checkNow() {
		clearTimeout(debounceTimer);
		runCheck(model, src);
	}

	function selectModel(id: ModelId) {
		if (id === model) return;
		model = id;
		// Re-check the *current* source against the newly selected model.
		scheduleCheck();
	}

	// --- Dark mode (default DARK, regardless of prefers-color-scheme) ---
	type Theme = 'light' | 'dark';
	let theme = $state<Theme>('dark');

	$effect(() => {
		if (!browser) return;
		const stored = localStorage.getItem('cov-theme');
		// Honor an explicit prior choice; otherwise default to dark (Lean vibes).
		if (stored === 'light' || stored === 'dark') {
			theme = stored;
		} else {
			theme = 'dark';
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
		'rw', 'intro', 'induct', 'm.induct',
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

<div class="ide">
	<header class="topbar">
		<div class="brand">
			<span class="logo">∴</span>
			<h1>Covalence</h1>
			<span class="tag">in-browser proof check</span>
		</div>
		<div class="topbar-right">
			{#if status === 'loading'}<span class="badge loading">loading kernel…</span>
			{:else if status === 'ready'}<span class="badge ok">kernel ready</span>
			{:else}<span class="badge err">kernel failed</span>{/if}
			<button class="theme-toggle" onclick={toggleTheme} title="Toggle light/dark" aria-label="Toggle theme">
				{theme === 'dark' ? '☀' : '☾'}
			</button>
		</div>
	</header>

	{#if status === 'error'}
		<pre class="fatal">Failed to load the wasm kernel: {loadError}

Did you run `bun run build:web-kernel` first? It emits the glue into
apps/covalence-web/src/lib/kernel/.</pre>
	{/if}

	<div class="panes">
		<!-- LEFT: source editor -->
		<section class="pane editor-pane">
			<div class="pane-head">
				<span class="pane-title">article.cov</span>
				<div class="pane-actions">
					{#if checking}<span class="checking">checking…</span>
						{#if model === 'nat/unary'}<span class="check-hint">proving axioms at this carrier — first run can take ~10-20s</span>{/if}
					{/if}
					<button class="btn" onclick={checkNow} disabled={status !== 'ready'}>Check</button>
				</div>
			</div>
			<div class="editor-wrap">
				<pre class="editor-highlight" aria-hidden="true" bind:this={highlightEl}>{@html highlighted}&nbsp;</pre>
				<textarea
					bind:value={src}
					spellcheck="false"
					oninput={onInput}
					onscroll={syncScroll}
				></textarea>
			</div>
		</section>

		<!-- RIGHT: infoview -->
		<section class="pane info-pane">
			<div class="pane-head">
				<span class="pane-title">Infoview</span>
			</div>
			<div class="info-body">
				<!-- Model selector -->
				<div class="model-block">
					<div class="model-row">
						<span class="model-label">model</span>
						<div class="segmented" role="group" aria-label="Model selector">
							{#each MODELS as m}
								<button
									class="seg {model === m.id ? 'active' : ''}"
									onclick={() => selectModel(m.id)}
									disabled={status !== 'ready'}
									title={m.blurb}
								>{m.label}</button>
							{/each}
						</div>
					</div>
					<div class="carrier-row">
						<span class="carrier-pill">carrier: <code>{activeModel.carrier}</code></span>
						<span class="carrier-blurb">{activeModel.blurb}</span>
					</div>
				</div>

				<div class="divider"></div>

				{#if report}
					<div class="verdict-row">
						<span class="verdict {report.ok ? 'ok' : 'err'}">
							{report.ok ? '✓ checked' : '✗ failed'}
						</span>
						<span class="verdict-count">
							{report.theorems.length} theorem{report.theorems.length === 1 ? '' : 's'}
						</span>
					</div>

					{#if report.theorems.length}
						<h2 class="section-h">Theorems</h2>
						<ul class="thms">
							{#each report.theorems as t}
								<li>
									<div class="thm-name">{t.name}</div>
									<code class="thm-stmt">⊢ {t.statement}</code>
								</li>
							{/each}
						</ul>
					{/if}

					{#if report.diagnostics.length}
						<h2 class="section-h">Diagnostics</h2>
						<ul class="diags">
							{#each report.diagnostics as d}
								<li class={d.severity}>
									<span class="diag-sev">{d.severity}</span>
									<span class="diag-msg">{d.message}</span>
								</li>
							{/each}
						</ul>
					{/if}
				{:else if status === 'ready'}
					<p class="muted">Edit the article to check it.</p>
				{:else if status === 'loading'}
					<p class="muted">Loading the kernel…</p>
				{:else}
					<p class="muted">Kernel unavailable.</p>
				{/if}
			</div>
		</section>
	</div>
</div>

<style>
	/* Palette: light/dark via [data-theme] on <html>. Lean-style dark default. */
	.ide {
		--a-bg: #ffffff;
		--a-bg-2: #f7f7f8;
		--a-fg: #1a1a1a;
		--a-muted: #6b7280;
		--a-surface: #ffffff;
		--a-panel: #fbfbfc;
		--a-border: #e2e3e7;
		--a-border-strong: #d1d5db;
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

		display: flex;
		flex-direction: column;
		height: 100vh;
		height: 100dvh;
		width: 100%;
		background: var(--a-bg);
		color: var(--a-fg);
		font-family: system-ui, sans-serif;
		overflow: hidden;
	}

	:global(html[data-theme='dark']) .ide {
		--a-bg: #0d0d10;
		--a-bg-2: #131318;
		--a-fg: #e3e3e6;
		--a-muted: #8b8b92;
		--a-surface: #16161c;
		--a-panel: #131318;
		--a-border: #26262e;
		--a-border-strong: #34343e;
		--a-accent: #a78bfa;
		--a-ok-bg: #133021;
		--a-ok-fg: #4ade80;
		--a-err-bg: #38161a;
		--a-err-fg: #f87171;
		--a-warn-bg: #382c12;
		--a-warn-fg: #fbbf24;
		--hl-comment: #6b7280;
		--hl-string: #a8e6a3;
		--hl-keyword: #7cc4f5;
		--hl-directive: #c9a0f5;
		--hl-number: #f5c07c;
		--hl-var: #f5a3c7;
		--hl-paren: #6b7280;
		--hl-atom: #e3e3e6;
	}

	/* --- Top bar --- */
	.topbar {
		display: flex;
		align-items: center;
		justify-content: space-between;
		gap: 1rem;
		padding: 0.5rem 1rem;
		height: 3rem;
		box-sizing: border-box;
		border-bottom: 1px solid var(--a-border);
		background: var(--a-panel);
		flex: 0 0 auto;
	}
	.brand { display: flex; align-items: baseline; gap: 0.6rem; }
	.logo { font-size: 1.25rem; color: var(--a-accent); transform: translateY(2px); }
	.topbar h1 { font-size: 1.05rem; font-weight: 600; margin: 0; letter-spacing: 0.01em; }
	.tag { font-size: 0.78rem; color: var(--a-muted); }
	.topbar-right { display: flex; align-items: center; gap: 0.6rem; }
	.theme-toggle {
		font-size: 1rem; line-height: 1; padding: 0.3rem 0.55rem; cursor: pointer;
		border: 1px solid var(--a-border-strong); border-radius: 0.5rem;
		background: var(--a-surface); color: var(--a-fg);
	}
	.theme-toggle:hover { border-color: var(--a-accent); }

	.badge { font-size: 0.74rem; padding: 0.12rem 0.55rem; border-radius: 1rem; font-weight: 500; }
	.badge.loading { background: var(--a-warn-bg); color: var(--a-warn-fg); }
	.badge.ok { background: var(--a-ok-bg); color: var(--a-ok-fg); }
	.badge.err { background: var(--a-err-bg); color: var(--a-err-fg); }

	.fatal {
		background: var(--a-err-bg); color: var(--a-err-fg);
		padding: 0.75rem 1rem; white-space: pre-wrap;
		font-family: ui-monospace, monospace; font-size: 0.8rem; margin: 0;
		border-bottom: 1px solid var(--a-border);
	}

	/* --- Panes --- */
	.panes {
		display: grid;
		grid-template-columns: 1fr 1fr;
		flex: 1 1 auto;
		min-height: 0;
	}
	.pane {
		display: flex;
		flex-direction: column;
		min-height: 0;
		min-width: 0;
		overflow: hidden;
	}
	.editor-pane { border-right: 1px solid var(--a-border); }
	.pane-head {
		display: flex;
		align-items: center;
		justify-content: space-between;
		gap: 0.5rem;
		padding: 0.4rem 0.75rem;
		height: 2.25rem;
		box-sizing: border-box;
		border-bottom: 1px solid var(--a-border);
		background: var(--a-bg-2);
		flex: 0 0 auto;
	}
	.pane-title {
		font-size: 0.78rem;
		font-weight: 600;
		letter-spacing: 0.03em;
		text-transform: uppercase;
		color: var(--a-muted);
		font-family: ui-monospace, monospace;
	}
	.pane-actions { display: flex; align-items: center; gap: 0.6rem; }
	.checking { font-size: 0.78rem; color: var(--a-muted); font-style: italic; }
	.check-hint { font-size: 0.72rem; color: var(--a-muted); opacity: 0.85; }
	.btn {
		padding: 0.25rem 0.8rem; border-radius: 0.4rem; font-size: 0.8rem;
		border: 1px solid var(--a-border-strong); background: var(--a-surface); color: var(--a-fg);
		cursor: pointer;
	}
	.btn:hover:not(:disabled) { border-color: var(--a-accent); }
	.btn:disabled { opacity: 0.5; cursor: default; }

	/* --- Editor: highlighted <pre> behind a transparent <textarea> --- */
	.editor-wrap { position: relative; flex: 1 1 auto; min-height: 0; }
	.editor-highlight,
	.editor-wrap textarea {
		position: absolute;
		inset: 0;
		width: 100%; height: 100%;
		font-family: ui-monospace, 'JetBrains Mono', monospace;
		font-size: 0.85rem;
		line-height: 1.55;
		padding: 0.75rem 1rem;
		border: 0;
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
		caret-color: var(--a-accent);
		resize: none;
		z-index: 1;
	}
	.editor-wrap textarea:focus { outline: 2px solid var(--a-accent); outline-offset: -2px; }

	/* --- Infoview --- */
	.info-pane { background: var(--a-panel); }
	.info-body {
		flex: 1 1 auto;
		min-height: 0;
		overflow: auto;
		padding: 1rem 1.25rem;
		font-family: ui-monospace, monospace;
		font-size: 0.85rem;
	}

	.model-block { display: flex; flex-direction: column; gap: 0.55rem; }
	.model-row { display: flex; align-items: center; gap: 0.75rem; }
	.model-label {
		font-size: 0.72rem; text-transform: uppercase; letter-spacing: 0.05em;
		color: var(--a-muted); font-weight: 600;
	}
	.segmented {
		display: inline-flex;
		border: 1px solid var(--a-border-strong);
		border-radius: 0.5rem;
		overflow: hidden;
		background: var(--a-bg-2);
	}
	.seg {
		font-family: ui-monospace, monospace;
		font-size: 0.8rem;
		padding: 0.32rem 0.85rem;
		border: 0;
		border-right: 1px solid var(--a-border-strong);
		background: transparent;
		color: var(--a-fg);
		cursor: pointer;
	}
	.seg:last-child { border-right: 0; }
	.seg:hover:not(:disabled):not(.active) { background: var(--a-surface); }
	.seg.active { background: var(--a-accent); color: #fff; font-weight: 600; }
	.seg:disabled { opacity: 0.5; cursor: default; }

	.carrier-row { display: flex; align-items: center; gap: 0.6rem; flex-wrap: wrap; }
	.carrier-pill {
		font-size: 0.78rem;
		padding: 0.15rem 0.55rem;
		border-radius: 1rem;
		background: var(--a-bg-2);
		border: 1px solid var(--a-border);
		color: var(--a-muted);
	}
	.carrier-pill code { color: var(--a-accent); font-weight: 600; }
	.carrier-blurb { font-size: 0.76rem; color: var(--a-muted); font-style: italic; }

	.divider { height: 1px; background: var(--a-border); margin: 1rem 0; }

	.verdict-row { display: flex; align-items: baseline; gap: 0.6rem; }
	.verdict { font-weight: 700; font-size: 0.95rem; }
	.verdict.ok { color: var(--a-ok-fg); }
	.verdict.err { color: var(--a-err-fg); }
	.verdict-count { font-size: 0.8rem; color: var(--a-muted); }

	.section-h {
		font-size: 0.72rem;
		text-transform: uppercase;
		letter-spacing: 0.05em;
		color: var(--a-muted);
		margin: 1rem 0 0.4rem;
		font-weight: 600;
	}
	.thms { list-style: none; padding: 0; margin: 0; }
	.thms li {
		padding: 0.55rem 0.7rem;
		margin-bottom: 0.5rem;
		border: 1px solid var(--a-border);
		border-left: 3px solid var(--a-accent);
		border-radius: 0.4rem;
		background: var(--a-bg-2);
	}
	.thm-name { font-weight: 700; color: var(--a-accent); margin-bottom: 0.25rem; }
	.thm-stmt { display: block; font-size: 0.82rem; color: var(--a-fg); white-space: pre-wrap; word-break: break-word; }

	.diags { list-style: none; padding: 0; margin: 0; }
	.diags li {
		display: flex;
		gap: 0.5rem;
		padding: 0.45rem 0.6rem;
		margin-bottom: 0.4rem;
		border-radius: 0.4rem;
		font-size: 0.8rem;
		white-space: pre-wrap;
		word-break: break-word;
	}
	.diags li.error { background: var(--a-err-bg); color: var(--a-err-fg); }
	.diags li.warning { background: var(--a-warn-bg); color: var(--a-warn-fg); }
	.diags li.info { background: var(--a-bg-2); color: var(--a-muted); }
	.diag-sev {
		flex: 0 0 auto;
		font-size: 0.68rem;
		text-transform: uppercase;
		font-weight: 700;
		letter-spacing: 0.04em;
		opacity: 0.85;
		padding-top: 0.05rem;
	}
	.diag-msg { flex: 1 1 auto; }

	.muted { color: var(--a-muted); }

	/* --- Syntax highlight token colors --- */
	.editor-highlight :global(.hl-comment) { color: var(--hl-comment); font-style: italic; }
	.editor-highlight :global(.hl-string) { color: var(--hl-string); }
	.editor-highlight :global(.hl-keyword) { color: var(--hl-keyword); }
	.editor-highlight :global(.hl-directive) { color: var(--hl-directive); font-weight: 600; }
	.editor-highlight :global(.hl-number) { color: var(--hl-number); }
	.editor-highlight :global(.hl-var) { color: var(--hl-var); }
	.editor-highlight :global(.hl-paren) { color: var(--hl-paren); }
	.editor-highlight :global(.hl-atom) { color: var(--hl-atom); }

	/* --- Narrow screens: stack the panes --- */
	@media (max-width: 52rem) {
		.ide { height: auto; min-height: 100vh; overflow: visible; }
		.panes { grid-template-columns: 1fr; }
		.editor-pane { border-right: 0; border-bottom: 1px solid var(--a-border); }
		.editor-wrap { height: 22rem; flex: 0 0 22rem; }
		.info-body { max-height: none; }
	}
</style>
