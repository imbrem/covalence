<script lang="ts">
	import { browser } from '$app/environment';
	import { liveCheck } from '$lib/kernelState.svelte';
	// Imported for the shared `--ok` / `--err` status hues on `:root`; this page
	// is not a `.demo-page`, so none of that file's scoped rules apply here.
	import '$lib/kernelPages.css';
	import { highlight } from '$lib/repl/sexpr';

	// The kernel runs *in the browser*: this page loads the wasm-bindgen build of
	// `covalence-web-kernel` (over `covalence-kernel::service`) and checks a `.cov`
	// article client-side — no server round-trip. See notes/web-kernel.md.
	//
	// The showcase: the SAME proof source is replayed against two different
	// *models* (carriers) via `check_model(src, model)`. `nat/self` proves over
	// the kernel's `nat` (integer commutativity); `nat/unary` proves the very
	// same script over `list unit` (append commutativity). Switching the model
	// re-checks the identical text and yields a *different* theorem statement.
	//
	// The kernel lives in a Web Worker here (unlike `/haskell` and `/proofs`,
	// which call it on the main thread): a `nat/unary` check proves four
	// `list unit` axioms then replays an induction, ~10-20s on a cold run, and
	// that would freeze the UI outright.

	type Diagnostic = {
		severity: 'error' | 'warning' | 'info';
		message: string;
		span: null | { start: number; end: number };
	};
	type TheoremInfo = { name: string; statement: string };
	type CheckReport = { ok: boolean; theorems: TheoremInfo[]; diagnostics: Diagnostic[] };

	type ModelId = 'nat/self' | 'nat/unary';
	const MODELS: { id: ModelId; label: string; carrier: string; blurb: string }[] = [
		{ id: 'nat/self', label: 'nat/self', carrier: 'nat', blurb: "the kernel's native nat (nat.add)" },
		{
			id: 'nat/unary',
			label: 'nat/unary',
			carrier: 'list unit',
			blurb: 'unary numerals as list unit (list.cat)'
		}
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
	let status = $state<'loading' | 'ready' | 'error'>('loading');
	let loadError = $state('');

	// --- Kernel worker RPC ---
	// In-flight checks are id-tagged and resolved against a pending map.
	let worker: Worker | null = null;
	let nextReqId = 0;
	const pending = new Map<number, (json: string) => void>();

	const activeModel = $derived(MODELS.find((m) => m.id === model) ?? MODELS[0]);

	// See the mount note in `kernelState.svelte.ts`: `onMount` is a silent no-op
	// in this app, so `$effect` plus a once-flag is the mount hook.
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
			worker = new Worker(new URL('$lib/kernel.worker.ts', import.meta.url), { type: 'module' });
			worker.onmessage = (ev: MessageEvent) => {
				const msg = ev.data;
				if (msg?.type === 'ready') {
					clearTimeout(timeout);
					status = 'ready';
					live.now({ src, model });
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

	/** Ask the worker to check; resolves with the raw JSON string. */
	function checkInWorker(source: string, m: ModelId): Promise<string> {
		return new Promise((resolve) => {
			if (!worker) {
				resolve(
					JSON.stringify({
						ok: false,
						theorems: [],
						diagnostics: [{ severity: 'error', message: 'kernel worker not available', span: null }]
					})
				);
				return;
			}
			const id = nextReqId++;
			pending.set(id, resolve);
			worker.postMessage({ type: 'check', id, src: source, model: m });
		});
	}

	// Debounce + cache + stale-guard, shared with `/haskell` and `/proofs`.
	// The model MUST be in the cache key: the same source at a different model
	// yields different theorems.
	const live = liveCheck<{ src: string; model: ModelId }, CheckReport>({
		key: (i) => `${i.model} ${i.src}`,
		run: async ({ src, model }) => {
			const json = await checkInWorker(src, model);
			try {
				return JSON.parse(json) as CheckReport;
			} catch (e) {
				return {
					ok: false,
					theorems: [],
					diagnostics: [{ severity: 'error', message: String(e), span: null }]
				};
			}
		}
	});

	let report = $derived(live.result);

	$effect(() => {
		const s = src;
		const m = model;
		if (status !== 'ready') return;
		live.schedule({ src: s, model: m });
	});

	function checkNow() {
		live.now({ src, model });
	}

	// --- Syntax highlighting (overlay pattern, matching the REPL routes) ---
	// `.cov` proof-script vocabulary. The `#`-prefixed reader directives are in
	// the same set as the rule names: the shared highlighter has one keyword
	// class, and a directive rendering as a keyword beats not rendering at all.
	//
	// TODO(cov:web.article-block-comments, minor): the shared highlighter has no
	// `(; … ;)` block-comment rule, so a block comment highlights as a paren plus
	// a line comment.
	const KEYWORDS: ReadonlySet<string> = new Set([
		'eq-mp', 'refl', 'reduce-prim', 'trans', 'sym', 'beta', 'eta',
		'mk-comb', 'abs', 'assume', 'deduct', 'inst', 'inst-type',
		'and-intro', 'and-elim', 'or-intro', 'or-elim', 'not-intro', 'not-elim',
		'imp-intro', 'imp-elim', 'all-intro', 'all-elim', 'exists-intro', 'exists-elim',
		'define', 'new-type', 'spec-abs', 'spec-rep', 'unfold', 'fold',
		'true', 'false', 'forall', 'exists', 'lambda', 'let', 'fun',
		'rw', 'intro', 'induct', 'm.induct',
		'#import', '#open', '#thm', '#concl', '#by', '#def', '#axiom'
	]);

	// `hashLinks: false` — a 64-hex atom inside a proof script is a term, not a
	// store address, and must not become a `/view/…` link.
	// The trailing `&nbsp;` keeps a final empty line rendered, so the highlight
	// layer and the textarea stay the same height (and scroll in step).
	let highlighted = $derived(highlight(src, KEYWORDS, { hashLinks: false }) + '&nbsp;');

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
			<h1>article check</h1>
			<span class="tag">in-browser proof check</span>
		</div>
		<div class="topbar-right">
			{#if status === 'loading'}<span class="badge loading">loading kernel…</span>
			{:else if status === 'ready'}<span class="badge ok" data-testid="kernel-badge">kernel ready</span>
			{:else}<span class="badge err">kernel failed</span>{/if}
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
					{#if live.busy}
						<span class="checking">checking…</span>
						{#if model === 'nat/unary'}<span class="check-hint"
								>proving axioms at this carrier — first run can take ~10-20s</span
							>{/if}
					{/if}
					<button class="btn" onclick={checkNow} disabled={status !== 'ready'}>Check</button>
				</div>
			</div>
			<div class="editor-wrap">
				<pre class="editor-highlight" aria-hidden="true" bind:this={highlightEl}>{@html highlighted}</pre>
				<textarea bind:value={src} spellcheck="false" onscroll={syncScroll} data-testid="article-input"
				></textarea>
			</div>
		</section>

		<!-- RIGHT: infoview -->
		<section class="pane info-pane">
			<div class="pane-head">
				<span class="pane-title">Infoview</span>
			</div>
			<div class="info-body">
				<div class="model-block">
					<div class="model-row">
						<span class="model-label">model</span>
						<div class="segmented" role="group" aria-label="Model selector">
							{#each MODELS as m}
								<button
									class="seg {model === m.id ? 'active' : ''}"
									onclick={() => (model = m.id)}
									disabled={status !== 'ready'}
									title={m.blurb}>{m.label}</button
								>
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
						<span class="verdict {report.ok ? 'ok' : 'err'}" data-testid="article-verdict">
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
	/* Colors come from the SITE variables (`app.css`), like every other route.
	   This page used to carry a private `--a-*` palette plus its own
	   light/dark toggle keyed on localStorage `cov-theme`, which bypassed the
	   site theme entirely and left the surrounding nav mismatched.
	   The site has exactly one (dark) theme, so the per-page toggle is gone.

	   TODO(cov:web.site-light-theme, minor): no site-wide light theme exists;
	   `/article` dropped its page-local one instead of keeping a toggle only
	   one route honoured. */
	.ide {
		/* Token hues for the shared highlighter, expressed against the site
		   accent/fg so they track the theme rather than pinning hex. */
		--hl-comment: var(--muted);
		--hl-string: color-mix(in srgb, var(--ok) 75%, var(--fg));
		--hl-keyword: color-mix(in srgb, var(--accent) 80%, var(--fg));
		--hl-number: color-mix(in srgb, var(--err) 45%, var(--fg));
		--hl-var: color-mix(in srgb, var(--accent) 55%, var(--fg));
		--hl-paren: var(--muted);
		--hl-atom: var(--fg);

		display: flex;
		flex-direction: column;
		/* `.cov-body` in the layout is already `calc(100vh - nav)`; filling it
		   (not 100vh) is what keeps the page from scrolling as a whole. */
		height: 100%;
		width: 100%;
		background: var(--bg);
		color: var(--fg);
		font-family: var(--font-mono);
		overflow: hidden;
	}

	/* --- Top bar --- */
	.topbar {
		display: flex;
		align-items: center;
		justify-content: space-between;
		gap: 1rem;
		padding: 0.5rem 1rem;
		height: 3rem;
		border-bottom: 1px solid var(--border);
		background: var(--surface);
		flex: 0 0 auto;
	}
	.brand {
		display: flex;
		align-items: baseline;
		gap: 0.6rem;
	}
	.logo {
		font-size: 1.25rem;
		color: var(--accent);
	}
	.topbar h1 {
		font-size: 1.05rem;
		font-weight: 600;
	}
	.tag {
		font-size: 0.78rem;
		color: var(--muted);
	}
	.topbar-right {
		display: flex;
		align-items: center;
		gap: 0.6rem;
	}

	.badge {
		font-size: 0.74rem;
		padding: 0.12rem 0.55rem;
		border-radius: 1rem;
		border: 1px solid var(--border);
	}
	.badge.loading {
		color: var(--muted);
	}
	.badge.ok {
		color: var(--ok);
		border-color: color-mix(in srgb, var(--ok) 40%, transparent);
		background: color-mix(in srgb, var(--ok) 14%, transparent);
	}
	.badge.err {
		color: var(--err);
		border-color: color-mix(in srgb, var(--err) 40%, transparent);
		background: color-mix(in srgb, var(--err) 14%, transparent);
	}

	.fatal {
		background: color-mix(in srgb, var(--err) 14%, transparent);
		color: color-mix(in srgb, var(--err) 70%, var(--fg));
		padding: 0.75rem 1rem;
		white-space: pre-wrap;
		font-size: 0.8rem;
		border-bottom: 1px solid var(--border);
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
	.editor-pane {
		border-right: 1px solid var(--border);
	}
	.pane-head {
		display: flex;
		align-items: center;
		justify-content: space-between;
		gap: 0.5rem;
		padding: 0.4rem 0.75rem;
		height: 2.25rem;
		border-bottom: 1px solid var(--border);
		background: var(--surface);
		flex: 0 0 auto;
	}
	.pane-title {
		font-size: 0.72rem;
		font-weight: 600;
		letter-spacing: 0.04em;
		text-transform: uppercase;
		color: var(--muted);
	}
	.pane-actions {
		display: flex;
		align-items: center;
		gap: 0.6rem;
	}
	.checking {
		font-size: 0.78rem;
		color: var(--muted);
		font-style: italic;
	}
	.check-hint {
		font-size: 0.72rem;
		color: var(--muted);
		opacity: 0.85;
	}
	.btn {
		font: inherit;
		padding: 0.25rem 0.8rem;
		border-radius: 5px;
		font-size: 0.8rem;
		border: 1px solid var(--border);
		background: var(--surface);
		color: var(--fg);
		cursor: pointer;
	}
	.btn:hover:not(:disabled) {
		border-color: var(--accent);
		color: var(--fg);
	}
	.btn:disabled {
		opacity: 0.5;
		cursor: default;
	}

	/* --- Editor: highlighted <pre> behind a transparent <textarea> --- */
	.editor-wrap {
		position: relative;
		flex: 1 1 auto;
		min-height: 0;
	}
	.editor-highlight,
	.editor-wrap textarea {
		position: absolute;
		inset: 0;
		width: 100%;
		height: 100%;
		font-family: var(--font-mono);
		font-size: 0.85rem;
		line-height: 1.55;
		padding: 0.75rem 1rem;
		border: 0;
		white-space: pre;
		overflow: auto;
		margin: 0;
		tab-size: 2;
	}
	.editor-highlight {
		pointer-events: none;
		background: var(--bg);
		color: var(--hl-atom);
		z-index: 0;
	}
	.editor-wrap textarea {
		background: transparent;
		color: transparent;
		caret-color: var(--accent);
		resize: none;
		z-index: 1;
	}
	.editor-wrap textarea:focus {
		outline: 1px solid var(--accent);
		outline-offset: -1px;
	}

	/* --- Infoview --- */
	.info-pane {
		background: var(--surface);
	}
	.info-body {
		flex: 1 1 auto;
		min-height: 0;
		overflow: auto;
		padding: 1rem 1.25rem;
		font-size: 0.85rem;
	}

	.model-block {
		display: flex;
		flex-direction: column;
		gap: 0.55rem;
	}
	.model-row {
		display: flex;
		align-items: center;
		gap: 0.75rem;
	}
	.model-label {
		font-size: 0.72rem;
		text-transform: uppercase;
		letter-spacing: 0.05em;
		color: var(--muted);
		font-weight: 600;
	}
	.segmented {
		display: inline-flex;
		border: 1px solid var(--border);
		border-radius: 6px;
		overflow: hidden;
		background: var(--bg);
	}
	.seg {
		font: inherit;
		font-size: 0.8rem;
		padding: 0.32rem 0.85rem;
		border: 0;
		border-right: 1px solid var(--border);
		background: transparent;
		color: var(--muted);
		cursor: pointer;
	}
	.seg:last-child {
		border-right: 0;
	}
	.seg:hover:not(:disabled):not(.active) {
		color: var(--fg);
	}
	.seg.active {
		background: color-mix(in srgb, var(--accent) 22%, transparent);
		color: var(--fg);
		font-weight: 600;
	}
	.seg:disabled {
		opacity: 0.5;
		cursor: default;
	}

	.carrier-row {
		display: flex;
		align-items: center;
		gap: 0.6rem;
		flex-wrap: wrap;
	}
	.carrier-pill {
		font-size: 0.78rem;
		padding: 0.15rem 0.55rem;
		border-radius: 1rem;
		background: var(--bg);
		border: 1px solid var(--border);
		color: var(--muted);
	}
	.carrier-pill code {
		color: var(--accent);
		font-weight: 600;
	}
	.carrier-blurb {
		font-size: 0.76rem;
		color: var(--muted);
		font-style: italic;
	}

	.divider {
		height: 1px;
		background: var(--border);
		margin: 1rem 0;
	}

	.verdict-row {
		display: flex;
		align-items: baseline;
		gap: 0.6rem;
	}
	.verdict {
		font-weight: 700;
		font-size: 0.95rem;
	}
	.verdict.ok {
		color: var(--ok);
	}
	.verdict.err {
		color: var(--err);
	}
	.verdict-count {
		font-size: 0.8rem;
		color: var(--muted);
	}

	.section-h {
		font-size: 0.72rem;
		text-transform: uppercase;
		letter-spacing: 0.05em;
		color: var(--muted);
		margin: 1rem 0 0.4rem;
		font-weight: 600;
	}
	.thms {
		list-style: none;
	}
	.thms li {
		padding: 0.55rem 0.7rem;
		margin-bottom: 0.5rem;
		border: 1px solid var(--border);
		border-left: 3px solid var(--accent);
		border-radius: 6px;
		background: var(--bg);
	}
	.thm-name {
		font-weight: 700;
		color: var(--accent);
		margin-bottom: 0.25rem;
	}
	.thm-stmt {
		display: block;
		font-size: 0.82rem;
		color: var(--fg);
		white-space: pre-wrap;
		word-break: break-word;
	}

	.diags {
		list-style: none;
	}
	.diags li {
		display: flex;
		gap: 0.5rem;
		padding: 0.45rem 0.6rem;
		margin-bottom: 0.4rem;
		border-radius: 6px;
		font-size: 0.8rem;
		white-space: pre-wrap;
		word-break: break-word;
		border: 1px solid var(--border);
	}
	.diags li.error {
		background: color-mix(in srgb, var(--err) 14%, transparent);
		color: color-mix(in srgb, var(--err) 70%, var(--fg));
		border-color: color-mix(in srgb, var(--err) 35%, transparent);
	}
	.diags li.warning {
		background: color-mix(in srgb, var(--accent) 12%, transparent);
		color: color-mix(in srgb, var(--accent) 60%, var(--fg));
	}
	.diags li.info {
		background: var(--bg);
		color: var(--muted);
	}
	.diag-sev {
		flex: 0 0 auto;
		font-size: 0.68rem;
		text-transform: uppercase;
		font-weight: 700;
		letter-spacing: 0.04em;
		opacity: 0.85;
	}
	.diag-msg {
		flex: 1 1 auto;
	}

	.muted {
		color: var(--muted);
	}

	/* --- Shared-highlighter token colors --- */
	.editor-highlight :global(.hl-comment) {
		color: var(--hl-comment);
		font-style: italic;
	}
	.editor-highlight :global(.hl-string) {
		color: var(--hl-string);
	}
	.editor-highlight :global(.hl-keyword) {
		color: var(--hl-keyword);
		font-weight: 600;
	}
	.editor-highlight :global(.hl-number) {
		color: var(--hl-number);
	}
	.editor-highlight :global(.hl-var) {
		color: var(--hl-var);
	}
	.editor-highlight :global(.hl-paren) {
		color: var(--hl-paren);
	}
	.editor-highlight :global(.hl-atom) {
		color: var(--hl-atom);
	}

	/* --- Narrow screens: stack the panes --- */
	@media (max-width: 52rem) {
		.ide {
			height: auto;
			min-height: 100%;
			overflow: visible;
		}
		.panes {
			grid-template-columns: 1fr;
		}
		.editor-pane {
			border-right: 0;
			border-bottom: 1px solid var(--border);
		}
		.editor-wrap {
			height: 22rem;
			flex: 0 0 22rem;
		}
	}
</style>
