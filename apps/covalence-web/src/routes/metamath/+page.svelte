<script lang="ts">
	// TEMPORARY / DEMO PAGE.
	// Downloads a Metamath `.mm` database, streams a per-theorem import into the
	// native HOL kernel over the `/api/mm/import` WebSocket, and lets you browse
	// each theorem's Metamath statement + HOL representation info. Throwaway UX.
	import { client } from '$lib/api';
	import type { ImportMessage, ImportedTheorem } from 'covalence-client';

	const PRESETS = {
		hol: 'https://raw.githubusercontent.com/metamath/set.mm/refs/heads/develop/hol.mm',
		set: 'https://raw.githubusercontent.com/metamath/set.mm/refs/heads/develop/set.mm',
	};

	let url = $state(PRESETS.hol);
	let phase = $state<'idle' | 'downloading' | 'parsing' | 'importing' | 'done' | 'error'>('idle');
	let statusMsg = $state('');
	let total = $state(0);
	let done = $state(0);
	let currentLabel = $state('');
	let elapsedMs = $state(0);
	let nOk = $state(0);
	let theorems = $state<ImportedTheorem[]>([]);
	let selected = $state<ImportedTheorem | null>(null);
	let failuresOnly = $state(false);
	let search = $state('');
	let showHisto = $state(false);
	let copyMsg = $state('');
	let ws: WebSocket | null = null;

	const failures = $derived(theorems.filter((t) => !t.ok));
	const nErr = $derived(failures.length);
	const timed = $derived(theorems.filter((t) => t.importMs != null));
	const totalMs = $derived(timed.reduce((a, t) => a + (t.importMs ?? 0), 0));
	const avgMs = $derived(timed.length ? totalMs / timed.length : 0);
	const slowest = $derived(
		timed.reduce<ImportedTheorem | null>(
			(m, t) => ((t.importMs ?? 0) > (m?.importMs ?? -1) ? t : m),
			null,
		),
	);
	// Filter: failures-only AND a case-insensitive substring match on label OR mm.
	const filtered = $derived.by(() => {
		const q = search.trim().toLowerCase();
		let list = failuresOnly ? failures : theorems;
		if (q) {
			list = list.filter(
				(t) => t.label.toLowerCase().includes(q) || t.mm.toLowerCase().includes(q),
			);
		}
		return list;
	});

	// --- timing statistics -------------------------------------------------
	// Linear-interpolation quantile (the "type 7" / numpy default): for p in
	// [0,1] over a sorted ascending array, index = p*(n-1), interpolate between
	// the two surrounding samples.
	function quantile(sorted: number[], p: number): number {
		const n = sorted.length;
		if (n === 0) return 0;
		if (n === 1) return sorted[0];
		const idx = p * (n - 1);
		const lo = Math.floor(idx);
		const hi = Math.ceil(idx);
		if (lo === hi) return sorted[lo];
		const frac = idx - lo;
		return sorted[lo] * (1 - frac) + sorted[hi] * frac;
	}
	const sortedMs = $derived(
		timed
			.map((t) => t.importMs ?? 0)
			.slice()
			.sort((a, b) => a - b),
	);
	const stats = $derived(
		sortedMs.length
			? {
					min: sortedMs[0],
					q1: quantile(sortedMs, 0.25),
					median: quantile(sortedMs, 0.5),
					q3: quantile(sortedMs, 0.75),
					max: sortedMs[sortedMs.length - 1],
				}
			: null,
	);

	// --- histogram (linear buckets over importMs) --------------------------
	const HISTO_BUCKETS = 30;
	const histo = $derived.by(() => {
		const xs = sortedMs;
		if (xs.length === 0) return null;
		const min = xs[0];
		const max = xs[xs.length - 1];
		const span = max - min || 1;
		const counts = new Array<number>(HISTO_BUCKETS).fill(0);
		for (const x of xs) {
			let b = Math.floor(((x - min) / span) * HISTO_BUCKETS);
			if (b >= HISTO_BUCKETS) b = HISTO_BUCKETS - 1;
			if (b < 0) b = 0;
			counts[b]++;
		}
		const peak = Math.max(...counts, 1);
		return { min, max, counts, peak };
	});
	// SVG geometry for the histogram.
	const HW = 640;
	const HH = 160;
	const HPAD = 24;

	async function copyFailures() {
		const data = failures.map((t) => ({ label: t.label, mm: t.mm, ess: t.ess, error: t.error }));
		try {
			await navigator.clipboard.writeText(JSON.stringify(data, null, 2));
			copyMsg = `copied ${data.length} failures`;
		} catch {
			copyMsg = 'clipboard blocked — see console';
			console.log(JSON.stringify(data, null, 2));
		}
		setTimeout(() => (copyMsg = ''), 2500);
	}
	const isRunning = $derived(
		phase === 'downloading' || phase === 'parsing' || phase === 'importing',
	);

	function reset() {
		total = 0;
		done = 0;
		currentLabel = '';
		elapsedMs = 0;
		nOk = 0;
		theorems = [];
		selected = null;
	}

	function stop() {
		if (ws) {
			ws.close();
			ws = null;
		}
		if (isRunning) {
			phase = 'idle';
			statusMsg = 'stopped';
		}
	}

	async function run() {
		stop();
		reset();
		phase = 'downloading';
		statusMsg = `downloading ${url} …`;

		let source: string;
		try {
			const res = await fetch(url);
			if (!res.ok) throw new Error(`${res.status} ${res.statusText}`);
			source = await res.text();
		} catch (e) {
			phase = 'error';
			statusMsg = `download failed: ${e instanceof Error ? e.message : String(e)}`;
			return;
		}

		statusMsg = `downloaded ${(source.length / 1_000_000).toFixed(1)} MB — connecting …`;
		phase = 'parsing';

		ws = client.connectMmImport();
		ws.onopen = () => {
			statusMsg = 'parsing & importing …';
			ws?.send(source);
		};
		ws.onerror = () => {
			phase = 'error';
			statusMsg = 'websocket error';
		};
		ws.onclose = () => {
			if (isRunning) {
				phase = 'error';
				statusMsg = 'connection closed unexpectedly';
			}
		};
		ws.onmessage = (ev) => {
			let msg: ImportMessage;
			try {
				msg = JSON.parse(ev.data as string) as ImportMessage;
			} catch {
				return;
			}
			handle(msg);
		};
	}

	function handle(msg: ImportMessage) {
		switch (msg.type) {
			case 'parsed':
				total = msg.total;
				phase = 'importing';
				statusMsg = `importing ${total} theorems …`;
				break;
			case 'theorem':
				done = msg.done;
				currentLabel = msg.label;
				theorems.push({
					label: msg.label,
					mm: msg.mm,
					ess: msg.ess ?? [],
					proof: msg.proof,
					deps: msg.deps,
					ok: msg.ok,
					hyps: msg.hyps,
					genuine: msg.genuine,
					holPreview: msg.holPreview,
					error: msg.error,
					importMs: msg.importMs,
				});
				break;
			case 'done':
				phase = 'done';
				nOk = msg.ok;
				elapsedMs = msg.elapsedMs;
				statusMsg = `done — ${msg.ok}/${msg.total} imported in ${(msg.elapsedMs / 1000).toFixed(1)}s`;
				ws?.close();
				ws = null;
				break;
			case 'error':
				phase = 'error';
				statusMsg = `error: ${msg.message}`;
				ws?.close();
				ws = null;
				break;
		}
	}
</script>

<main>
	<header>
		<h1>Metamath → HOL import <span class="tag">temporary demo</span></h1>
		<p class="lede">
			Downloads a Metamath <code>.mm</code> database, then imports each theorem one-by-one into the
			native HOL kernel (constructing <code>⊢ Derivable_L ⌜S⌝</code> per theorem). Pick a source,
			hit import, and watch the progress bar — click any theorem to inspect its Metamath statement
			and HOL representation. This page is a throwaway UX experiment, not a stable feature.
		</p>
	</header>

	<section class="controls">
		<div class="presets">
			<button class:active={url === PRESETS.hol} onclick={() => (url = PRESETS.hol)}>
				hol.mm <small>~151 thms · seconds</small>
			</button>
			<button class:active={url === PRESETS.set} onclick={() => (url = PRESETS.set)}>
				set.mm <small>~48 MB · ~47k thms · minutes</small>
			</button>
		</div>
		<div class="row">
			<input
				type="text"
				bind:value={url}
				placeholder=".mm URL"
				spellcheck="false"
				disabled={isRunning}
			/>
			{#if isRunning}
				<button class="primary stop" onclick={stop}>Stop</button>
			{:else}
				<button class="primary" onclick={run}>Download &amp; Import</button>
			{/if}
		</div>
		{#if url === PRESETS.set}
			<p class="warn">
				set.mm is ~48 MB and ~47k theorems — the download + WebSocket upload is heavy and the
				import runs for minutes. hol.mm is the snappy default.
			</p>
		{/if}
	</section>

	<section class="status">
		<div class="bar">
			<progress value={done} max={Math.max(total, 1)}></progress>
			<span class="counts">{done} / {total || '?'}</span>
		</div>
		<div class="statline">
			<span class="phase phase-{phase}">{phase}</span>
			<span class="msg">{statusMsg}</span>
			{#if currentLabel && isRunning}<span class="cur">{currentLabel}</span>{/if}
		</div>
		{#if theorems.length > 0}
			<div class="summary">
				<span class="ok">{nOk || theorems.filter((t) => t.ok).length} ok</span>
				{#if nErr > 0}<span class="err">{nErr} failed</span>{/if}
				{#if phase === 'done'}<span>{(elapsedMs / 1000).toFixed(1)}s wall</span>{/if}
				{#if avgMs > 0}<span class="dim">avg {avgMs.toFixed(1)} ms/thm</span>{/if}
				{#if slowest}<span class="dim">slowest {slowest.label} {(slowest.importMs ?? 0).toFixed(0)} ms</span>{/if}
				<span class="spacer"></span>
				<label class="filter">
					<input type="checkbox" bind:checked={failuresOnly} />
					failures only
				</label>
				{#if timed.length > 0}
					<button class="copy" class:on={showHisto} onclick={() => (showHisto = !showHisto)}>
						{showHisto ? 'hide plot' : 'plot'}
					</button>
				{/if}
				{#if nErr > 0}
					<button class="copy" onclick={copyFailures}>Copy failures (JSON)</button>
				{/if}
				{#if copyMsg}<span class="dim">{copyMsg}</span>{/if}
			</div>
			{#if stats}
				<div class="quantiles">
					<span class="qlabel">import ms</span>
					<span class="q">min <b>{stats.min.toFixed(1)}</b></span>
					<span class="q">q1 <b>{stats.q1.toFixed(1)}</b></span>
					<span class="q">median <b>{stats.median.toFixed(1)}</b></span>
					<span class="q">q3 <b>{stats.q3.toFixed(1)}</b></span>
					<span class="q">max <b>{stats.max.toFixed(1)}</b></span>
				</div>
			{/if}
			{#if showHisto && histo}
				<div class="histo">
					<svg viewBox="0 0 {HW} {HH}" preserveAspectRatio="none" role="img"
						aria-label="histogram of import times">
						{#each histo.counts as c, i (i)}
							{@const bw = (HW - 2 * HPAD) / HISTO_BUCKETS}
							{@const h = (c / histo.peak) * (HH - 2 * HPAD)}
							<rect
								x={HPAD + i * bw}
								y={HH - HPAD - h}
								width={Math.max(bw - 1, 1)}
								height={h}
								fill="var(--accent)"
							/>
						{/each}
						<line x1={HPAD} y1={HH - HPAD} x2={HW - HPAD} y2={HH - HPAD} stroke="var(--border)" />
					</svg>
					<div class="haxis">
						<span>{histo.min.toFixed(1)} ms</span>
						<span class="dim">{HISTO_BUCKETS} buckets · peak {histo.peak}</span>
						<span>{histo.max.toFixed(1)} ms</span>
					</div>
				</div>
			{/if}
		{/if}
	</section>

	<section class="panes">
		<div class="list">
			<div class="searchbar">
				<input
					type="text"
					class="search"
					bind:value={search}
					placeholder="filter by label or statement…"
					spellcheck="false"
				/>
				{#if search || failuresOnly}
					<span class="shown">{filtered.length} / {theorems.length}</span>
				{/if}
			</div>
			<div class="rows">
				{#each filtered as t (t.label)}
					<button
						class="item"
						class:fail={!t.ok}
						class:sel={selected?.label === t.label}
						onclick={() => (selected = t)}
					>
						<span class="dot" class:bad={!t.ok}></span>
						<span class="lbl">{t.label}</span>
						<span class="mini">{t.mm}</span>
						{#if t.importMs != null}<span class="time">{t.importMs.toFixed(0)} ms</span>{/if}
					</button>
				{/each}
				{#if theorems.length === 0}
					<div class="empty">No theorems yet. Choose a source and import.</div>
				{:else if filtered.length === 0}
					<div class="empty">No theorems match the current filter.</div>
				{/if}
			</div>
		</div>

		<div class="detail">
			{#if selected}
				<h2>{selected.label}</h2>
				<div class="field">
					<div class="flabel">Metamath statement</div>
					<pre class="mm">{selected.mm}</pre>
					{#if selected.ess.length > 0}
						<div class="flabel sub">essential hypotheses</div>
						{#each selected.ess as e (e)}
							<pre class="mm hyp">{e}</pre>
						{/each}
					{/if}
				</div>
				<div class="field">
					<div class="flabel">HOL representation</div>
					{#if selected.ok}
						<div class="kv">
							<span>hypotheses</span><span>{selected.hyps}</span>
						</div>
						<div class="kv">
							<span>genuine (oracle-free)</span>
							<span class:yes={selected.genuine} class:no={!selected.genuine}>
								{selected.genuine ? 'yes' : 'no'}
							</span>
						</div>
						{#if selected.importMs != null}
							<div class="kv">
								<span>import time</span><span>{selected.importMs.toFixed(1)} ms</span>
							</div>
						{/if}
						<div class="flabel sub">conclusion preview</div>
						<p class="note">
							Truncated preview of <code>⊢ Derivable_L ⌜S⌝</code> (the real conclusion is huge —
							that's the point of proof-irrelevance).
						</p>
						<pre class="hol">{selected.holPreview}…</pre>
					{:else}
						<div class="kv">
							<span>status</span><span class="no">import failed</span>
						</div>
						<pre class="hol err">{selected.error}</pre>
					{/if}
				</div>
				<div class="field">
					<div class="flabel">Dependencies</div>
					{#if selected.deps && selected.deps.length > 0}
						{@const axioms = selected.deps.filter((d) => d.kind === 'axiom')}
						{@const defs = selected.deps.filter((d) => d.kind === 'def')}
						{@const thms = selected.deps.filter((d) => d.kind === 'thm')}
						{#if axioms.length > 0}
							<div class="depgroup">
								<span class="dkind axiom">Axioms ({axioms.length})</span>
								<span class="chips">
									{#each axioms as d (d.label)}<span class="chip axiom">{d.label}</span>{/each}
								</span>
							</div>
						{/if}
						{#if defs.length > 0}
							<div class="depgroup">
								<span class="dkind def">Definitions ({defs.length})</span>
								<span class="chips">
									{#each defs as d (d.label)}<span class="chip def">{d.label}</span>{/each}
								</span>
							</div>
						{/if}
						{#if thms.length > 0}
							<div class="depgroup">
								<span class="dkind thm">Theorems ({thms.length})</span>
								<span class="chips">
									{#each thms as d (d.label)}<span class="chip thm">{d.label}</span>{/each}
								</span>
							</div>
						{/if}
					{:else}
						<p class="note">none (axiom instance / hypotheses only)</p>
					{/if}
				</div>
				<div class="field">
					<div class="flabel">Metamath proof (compressed)</div>
					{#if selected.proof}
						<pre class="mm proof">{selected.proof}</pre>
					{:else}
						<p class="note">no proof code (axiom).</p>
					{/if}
				</div>
			{:else}
				<div class="empty">Select a theorem to see its Metamath + HOL details.</div>
			{/if}
		</div>
	</section>
</main>

<style>
	/* Dark theme — uses the site palette from app.css
	   (--bg/--fg/--surface/--border/--accent/--muted). */
	main {
		--ok: #4ade80;
		--bad: #f87171;
		--warnc: #fbbf24;
		--code-bg: #0e0e10;
		max-width: 1100px;
		margin: 0 auto;
		padding: 1.5rem;
		font-family: var(--font-mono);
		color: var(--fg);
	}
	h1 {
		font-size: 1.4rem;
		margin: 0 0 0.4rem;
		color: var(--fg);
	}
	.tag {
		font-size: 0.65rem;
		text-transform: uppercase;
		letter-spacing: 0.08em;
		background: rgba(251, 191, 36, 0.16);
		color: var(--warnc);
		padding: 0.15rem 0.45rem;
		border-radius: 4px;
		vertical-align: middle;
	}
	.lede {
		color: var(--muted);
		font-size: 0.9rem;
		line-height: 1.5;
		max-width: 70ch;
	}
	code {
		font-family: var(--font-mono);
		background: var(--surface);
		border: 1px solid var(--border);
		padding: 0.05rem 0.25rem;
		border-radius: 3px;
		font-size: 0.85em;
		color: var(--fg);
	}

	.controls {
		margin: 1.25rem 0;
	}
	.presets {
		display: flex;
		gap: 0.5rem;
		margin-bottom: 0.6rem;
	}
	.presets button {
		flex: 1;
		text-align: left;
		padding: 0.5rem 0.7rem;
		border: 1px solid var(--border);
		border-radius: 6px;
		background: var(--surface);
		color: var(--fg);
		cursor: pointer;
		line-height: 1.2;
	}
	.presets button small {
		display: block;
		color: var(--muted);
		font-size: 0.7rem;
		margin-top: 0.15rem;
	}
	.presets button.active {
		border-color: var(--accent);
		background: rgba(124, 111, 247, 0.16);
	}
	.row {
		display: flex;
		gap: 0.5rem;
	}
	input[type='text'] {
		flex: 1;
		padding: 0.5rem 0.6rem;
		border: 1px solid var(--border);
		border-radius: 6px;
		background: var(--code-bg);
		color: var(--fg);
		font-family: var(--font-mono);
		font-size: 0.85rem;
	}
	button.primary {
		padding: 0.5rem 1rem;
		border: none;
		border-radius: 6px;
		background: var(--accent);
		color: #fff;
		font-weight: 600;
		cursor: pointer;
		white-space: nowrap;
	}
	button.primary.stop {
		background: var(--bad);
	}
	.warn {
		margin: 0.5rem 0 0;
		font-size: 0.8rem;
		color: var(--warnc);
		background: rgba(251, 191, 36, 0.1);
		border: 1px solid rgba(251, 191, 36, 0.25);
		padding: 0.4rem 0.6rem;
		border-radius: 5px;
	}

	.status {
		margin: 1rem 0;
	}
	.bar {
		display: flex;
		align-items: center;
		gap: 0.6rem;
	}
	progress {
		flex: 1;
		height: 12px;
		accent-color: var(--accent);
	}
	.counts {
		font-variant-numeric: tabular-nums;
		font-size: 0.85rem;
		color: var(--muted);
		min-width: 6em;
		text-align: right;
	}
	.statline {
		display: flex;
		gap: 0.6rem;
		align-items: center;
		margin-top: 0.4rem;
		font-size: 0.82rem;
	}
	.phase {
		text-transform: uppercase;
		font-size: 0.62rem;
		letter-spacing: 0.06em;
		padding: 0.12rem 0.4rem;
		border-radius: 4px;
		background: var(--surface);
		border: 1px solid var(--border);
		color: var(--muted);
	}
	.phase-importing,
	.phase-downloading,
	.phase-parsing {
		background: rgba(124, 111, 247, 0.16);
		border-color: transparent;
		color: var(--accent);
	}
	.phase-done {
		background: rgba(74, 222, 128, 0.16);
		border-color: transparent;
		color: var(--ok);
	}
	.phase-error {
		background: rgba(248, 113, 113, 0.16);
		border-color: transparent;
		color: var(--bad);
	}
	.msg {
		color: var(--muted);
	}
	.cur {
		font-family: var(--font-mono);
		color: var(--accent);
		margin-left: auto;
	}
	.summary {
		display: flex;
		gap: 0.8rem;
		align-items: center;
		flex-wrap: wrap;
		margin-top: 0.4rem;
		font-size: 0.8rem;
	}
	.summary .ok {
		color: var(--ok);
	}
	.summary .err {
		color: var(--bad);
		font-weight: 600;
	}
	.summary .dim {
		color: var(--muted);
	}
	.summary .spacer {
		flex: 1;
	}
	.summary .filter {
		display: flex;
		align-items: center;
		gap: 0.3rem;
		color: var(--muted);
		cursor: pointer;
	}
	.summary .copy {
		padding: 0.25rem 0.55rem;
		border: 1px solid var(--border);
		border-radius: 5px;
		background: var(--surface);
		color: var(--fg);
		cursor: pointer;
		font-size: 0.76rem;
	}
	.summary .copy:hover {
		border-color: var(--accent);
	}

	.panes {
		display: grid;
		grid-template-columns: minmax(280px, 1fr) minmax(320px, 1.2fr);
		gap: 1rem;
		margin-top: 0.5rem;
	}
	.list {
		display: flex;
		flex-direction: column;
		border: 1px solid var(--border);
		border-radius: 8px;
		max-height: 60vh;
		background: var(--surface);
	}
	.searchbar {
		display: flex;
		align-items: center;
		gap: 0.5rem;
		padding: 0.4rem 0.5rem;
		border-bottom: 1px solid var(--border);
		flex: none;
	}
	input.search {
		flex: 1;
		padding: 0.35rem 0.5rem;
		border: 1px solid var(--border);
		border-radius: 5px;
		background: var(--code-bg);
		color: var(--fg);
		font-family: var(--font-mono);
		font-size: 0.78rem;
	}
	.searchbar .shown {
		font-size: 0.72rem;
		color: var(--muted);
		font-variant-numeric: tabular-nums;
		white-space: nowrap;
	}
	.rows {
		flex: 1;
		overflow-y: auto;
	}
	.quantiles {
		display: flex;
		gap: 0.8rem;
		align-items: center;
		flex-wrap: wrap;
		margin-top: 0.4rem;
		font-size: 0.78rem;
		color: var(--muted);
	}
	.quantiles .qlabel {
		text-transform: uppercase;
		font-size: 0.62rem;
		letter-spacing: 0.06em;
	}
	.quantiles .q b {
		color: var(--fg);
		font-variant-numeric: tabular-nums;
		font-weight: 600;
	}
	.histo {
		margin-top: 0.6rem;
		border: 1px solid var(--border);
		border-radius: 6px;
		padding: 0.5rem;
		background: var(--code-bg);
	}
	.histo svg {
		display: block;
		width: 100%;
		height: 160px;
	}
	.haxis {
		display: flex;
		justify-content: space-between;
		margin-top: 0.3rem;
		font-size: 0.7rem;
		color: var(--fg);
		font-variant-numeric: tabular-nums;
	}
	.haxis .dim {
		color: var(--muted);
	}
	.copy.on {
		border-color: var(--accent);
		color: var(--accent);
	}
	.item {
		display: flex;
		align-items: center;
		gap: 0.5rem;
		width: 100%;
		text-align: left;
		padding: 0.4rem 0.6rem;
		border: none;
		border-bottom: 1px solid var(--border);
		background: transparent;
		color: var(--fg);
		cursor: pointer;
		font-size: 0.8rem;
	}
	.item:hover {
		background: rgba(124, 111, 247, 0.1);
	}
	.item.sel {
		background: rgba(124, 111, 247, 0.2);
	}
	.item .dot {
		width: 7px;
		height: 7px;
		border-radius: 50%;
		background: var(--ok);
		flex: none;
	}
	.item .dot.bad {
		background: var(--bad);
	}
	.item .lbl {
		font-family: var(--font-mono);
		font-weight: 600;
		flex: none;
		color: var(--fg);
	}
	.item .mini {
		flex: 1;
		color: var(--muted);
		font-family: var(--font-mono);
		white-space: nowrap;
		overflow: hidden;
		text-overflow: ellipsis;
	}
	.item .time {
		flex: none;
		color: var(--muted);
		font-variant-numeric: tabular-nums;
		font-size: 0.72rem;
		opacity: 0.75;
	}
	.item.fail .lbl {
		color: var(--bad);
	}

	.detail {
		border: 1px solid var(--border);
		border-radius: 8px;
		padding: 1rem;
		max-height: 60vh;
		overflow-y: auto;
		background: var(--surface);
	}
	.detail h2 {
		margin: 0 0 0.8rem;
		font-family: var(--font-mono);
		font-size: 1.05rem;
		color: var(--fg);
	}
	.field {
		margin-bottom: 1rem;
	}
	.flabel {
		font-size: 0.68rem;
		text-transform: uppercase;
		letter-spacing: 0.06em;
		color: var(--muted);
		margin-bottom: 0.3rem;
	}
	.flabel.sub {
		margin-top: 0.7rem;
	}
	pre.mm,
	pre.hol {
		background: var(--code-bg);
		border: 1px solid var(--border);
		border-radius: 5px;
		padding: 0.5rem 0.6rem;
		font-family: var(--font-mono);
		font-size: 0.78rem;
		white-space: pre-wrap;
		word-break: break-word;
		margin: 0 0 0.3rem;
		color: var(--fg);
	}
	pre.hyp {
		background: var(--surface);
	}
	pre.hol.err {
		color: var(--bad);
		background: rgba(248, 113, 113, 0.08);
		border-color: rgba(248, 113, 113, 0.3);
	}
	.kv {
		display: flex;
		justify-content: space-between;
		font-size: 0.82rem;
		padding: 0.2rem 0;
		border-bottom: 1px dashed var(--border);
	}
	.kv .yes {
		color: var(--ok);
		font-weight: 600;
	}
	.kv .no {
		color: var(--bad);
		font-weight: 600;
	}
	.note {
		font-size: 0.74rem;
		color: var(--muted);
		margin: 0.2rem 0 0.4rem;
		line-height: 1.4;
	}
	.empty {
		padding: 1.5rem;
		color: var(--muted);
		font-size: 0.85rem;
		text-align: center;
	}
	.depgroup {
		margin-bottom: 0.5rem;
	}
	.dkind {
		display: block;
		font-size: 0.68rem;
		text-transform: uppercase;
		letter-spacing: 0.06em;
		margin-bottom: 0.25rem;
		color: var(--muted);
	}
	.dkind.axiom {
		color: var(--warnc);
	}
	.dkind.def {
		color: var(--accent);
	}
	.dkind.thm {
		color: var(--ok);
	}
	.chips {
		display: flex;
		flex-wrap: wrap;
		gap: 0.3rem;
	}
	.chip {
		font-family: var(--font-mono);
		font-size: 0.72rem;
		padding: 0.1rem 0.4rem;
		border-radius: 4px;
		border: 1px solid var(--border);
		background: var(--code-bg);
		color: var(--fg);
	}
	.chip.axiom {
		border-color: rgba(251, 191, 36, 0.4);
	}
	.chip.def {
		border-color: rgba(124, 111, 247, 0.4);
	}
	.chip.thm {
		border-color: rgba(74, 222, 128, 0.4);
	}
	pre.proof {
		max-height: 14rem;
		overflow-y: auto;
	}
</style>
