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

	// Only render the last RENDER_CAP rows so set.mm (47k theorems) doesn't
	// explode the DOM. All rows stay in `theorems` for the count/selection.
	const RENDER_CAP = 500;

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
	let ws: WebSocket | null = null;

	const nErr = $derived(theorems.filter((t) => !t.ok).length);
	const visible = $derived(
		theorems.length > RENDER_CAP ? theorems.slice(theorems.length - RENDER_CAP) : theorems,
	);
	const truncated = $derived(theorems.length - visible.length);
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
					ok: msg.ok,
					hyps: msg.hyps,
					genuine: msg.genuine,
					holPreview: msg.holPreview,
					error: msg.error,
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
				{#if phase === 'done'}<span>{(elapsedMs / 1000).toFixed(1)}s</span>{/if}
			</div>
		{/if}
	</section>

	<section class="panes">
		<div class="list">
			{#if truncated > 0}
				<div class="trunc">… {truncated} earlier theorems hidden (showing last {RENDER_CAP})</div>
			{/if}
			{#each visible as t (t.label)}
				<button
					class="item"
					class:fail={!t.ok}
					class:sel={selected?.label === t.label}
					onclick={() => (selected = t)}
				>
					<span class="dot" class:bad={!t.ok}></span>
					<span class="lbl">{t.label}</span>
					<span class="mini">{t.mm}</span>
				</button>
			{/each}
			{#if theorems.length === 0}
				<div class="empty">No theorems yet. Choose a source and import.</div>
			{/if}
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
			{:else}
				<div class="empty">Select a theorem to see its Metamath + HOL details.</div>
			{/if}
		</div>
	</section>
</main>

<style>
	main {
		max-width: 1100px;
		margin: 0 auto;
		padding: 1.5rem;
		font-family: system-ui, sans-serif;
		color: #1a1a1a;
	}
	h1 {
		font-size: 1.4rem;
		margin: 0 0 0.4rem;
	}
	.tag {
		font-size: 0.65rem;
		text-transform: uppercase;
		letter-spacing: 0.08em;
		background: #ffe9a8;
		color: #7a5c00;
		padding: 0.15rem 0.45rem;
		border-radius: 4px;
		vertical-align: middle;
	}
	.lede {
		color: #555;
		font-size: 0.9rem;
		line-height: 1.5;
		max-width: 70ch;
	}
	code {
		font-family: ui-monospace, monospace;
		background: #f0f0f2;
		padding: 0.05rem 0.25rem;
		border-radius: 3px;
		font-size: 0.85em;
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
		border: 1px solid #ccc;
		border-radius: 6px;
		background: #fff;
		cursor: pointer;
		line-height: 1.2;
	}
	.presets button small {
		display: block;
		color: #888;
		font-size: 0.7rem;
		margin-top: 0.15rem;
	}
	.presets button.active {
		border-color: #3b6cff;
		background: #eef2ff;
	}
	.row {
		display: flex;
		gap: 0.5rem;
	}
	input[type='text'] {
		flex: 1;
		padding: 0.5rem 0.6rem;
		border: 1px solid #ccc;
		border-radius: 6px;
		font-family: ui-monospace, monospace;
		font-size: 0.85rem;
	}
	button.primary {
		padding: 0.5rem 1rem;
		border: none;
		border-radius: 6px;
		background: #3b6cff;
		color: #fff;
		font-weight: 600;
		cursor: pointer;
		white-space: nowrap;
	}
	button.primary.stop {
		background: #c0392b;
	}
	.warn {
		margin: 0.5rem 0 0;
		font-size: 0.8rem;
		color: #8a5b00;
		background: #fff7e0;
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
	}
	.counts {
		font-variant-numeric: tabular-nums;
		font-size: 0.85rem;
		color: #444;
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
		background: #eee;
		color: #555;
	}
	.phase-importing,
	.phase-downloading,
	.phase-parsing {
		background: #eef2ff;
		color: #3b6cff;
	}
	.phase-done {
		background: #e3f6e8;
		color: #1d7a3a;
	}
	.phase-error {
		background: #fde8e6;
		color: #c0392b;
	}
	.msg {
		color: #555;
	}
	.cur {
		font-family: ui-monospace, monospace;
		color: #3b6cff;
		margin-left: auto;
	}
	.summary {
		display: flex;
		gap: 0.8rem;
		margin-top: 0.4rem;
		font-size: 0.8rem;
	}
	.summary .ok {
		color: #1d7a3a;
	}
	.summary .err {
		color: #c0392b;
	}

	.panes {
		display: grid;
		grid-template-columns: minmax(280px, 1fr) minmax(320px, 1.2fr);
		gap: 1rem;
		margin-top: 0.5rem;
	}
	.list {
		border: 1px solid #e0e0e4;
		border-radius: 8px;
		max-height: 60vh;
		overflow-y: auto;
		background: #fafafb;
	}
	.trunc {
		padding: 0.4rem 0.6rem;
		font-size: 0.72rem;
		color: #999;
		border-bottom: 1px solid #eee;
	}
	.item {
		display: flex;
		align-items: center;
		gap: 0.5rem;
		width: 100%;
		text-align: left;
		padding: 0.4rem 0.6rem;
		border: none;
		border-bottom: 1px solid #efeff2;
		background: transparent;
		cursor: pointer;
		font-size: 0.8rem;
	}
	.item:hover {
		background: #f0f3ff;
	}
	.item.sel {
		background: #e4ebff;
	}
	.item .dot {
		width: 7px;
		height: 7px;
		border-radius: 50%;
		background: #1d7a3a;
		flex: none;
	}
	.item .dot.bad {
		background: #c0392b;
	}
	.item .lbl {
		font-family: ui-monospace, monospace;
		font-weight: 600;
		flex: none;
	}
	.item .mini {
		color: #999;
		font-family: ui-monospace, monospace;
		white-space: nowrap;
		overflow: hidden;
		text-overflow: ellipsis;
	}
	.item.fail .lbl {
		color: #c0392b;
	}

	.detail {
		border: 1px solid #e0e0e4;
		border-radius: 8px;
		padding: 1rem;
		max-height: 60vh;
		overflow-y: auto;
	}
	.detail h2 {
		margin: 0 0 0.8rem;
		font-family: ui-monospace, monospace;
		font-size: 1.05rem;
	}
	.field {
		margin-bottom: 1rem;
	}
	.flabel {
		font-size: 0.68rem;
		text-transform: uppercase;
		letter-spacing: 0.06em;
		color: #888;
		margin-bottom: 0.3rem;
	}
	.flabel.sub {
		margin-top: 0.7rem;
	}
	pre.mm,
	pre.hol {
		background: #f6f6f8;
		border: 1px solid #ececf0;
		border-radius: 5px;
		padding: 0.5rem 0.6rem;
		font-family: ui-monospace, monospace;
		font-size: 0.78rem;
		white-space: pre-wrap;
		word-break: break-word;
		margin: 0 0 0.3rem;
	}
	pre.hyp {
		background: #fff;
	}
	pre.hol.err {
		color: #c0392b;
		background: #fdf0ef;
	}
	.kv {
		display: flex;
		justify-content: space-between;
		font-size: 0.82rem;
		padding: 0.2rem 0;
		border-bottom: 1px dashed #eee;
	}
	.kv .yes {
		color: #1d7a3a;
		font-weight: 600;
	}
	.kv .no {
		color: #c0392b;
		font-weight: 600;
	}
	.note {
		font-size: 0.74rem;
		color: #777;
		margin: 0.2rem 0 0.4rem;
		line-height: 1.4;
	}
	.empty {
		padding: 1.5rem;
		color: #aaa;
		font-size: 0.85rem;
		text-align: center;
	}
</style>
