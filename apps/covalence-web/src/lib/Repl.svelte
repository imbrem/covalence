<script lang="ts">
	// A reusable single-box REPL: a scrolling transcript + a prompt line.
	// `evalCell` is the (synchronous) wasm call `src -> {ok, result, error}`.
	// `showCell`, if given, lazily fetches HOL info for a cell on hover (e.g. the
	// `⊢ lhs = rhs` theorem behind a Lisp value, via the `#show` directive).
	type EvalResult = { ok: boolean; result: string; error: string };
	type Example = { title: string; src: string };

	let {
		evalCell,
		showCell = null,
		onReset = null,
		ready = false,
		loadError = '',
		examples = [],
		prompt = 'λ>',
		placeholder = 'type a form, press Enter — Shift+Enter for a newline'
	}: {
		evalCell: (src: string) => EvalResult;
		showCell?: ((src: string) => string) | null;
		onReset?: (() => void) | null;
		ready?: boolean;
		loadError?: string;
		examples?: Example[];
		prompt?: string;
		placeholder?: string;
	} = $props();

	type Entry = {
		input: string;
		output: string;
		ok: boolean;
		directive: boolean;
		pending: boolean;
		hol: string | null;
		holTried: boolean;
	};

	let entries = $state<Entry[]>([]);
	let input = $state('');
	let scroller = $state<HTMLDivElement | null>(null);

	function scrollSoon() {
		requestAnimationFrame(() => {
			if (scroller) scroller.scrollTop = scroller.scrollHeight;
		});
	}

	function submit() {
		const src = input.trim();
		if (!src || !ready) return;
		input = '';
		const entry: Entry = {
			input: src,
			output: '',
			ok: true,
			directive: src.startsWith('#'),
			pending: true,
			hol: null,
			holTried: false
		};
		entries.push(entry);
		scrollSoon();
		// Defer the (possibly slow first) synchronous wasm call so the "proving…"
		// state paints before the kernel-init blocks the main thread.
		setTimeout(() => {
			try {
				const r = evalCell(src);
				entry.output = r.ok ? r.result : r.error;
				entry.ok = r.ok;
			} catch (e) {
				entry.output = String(e);
				entry.ok = false;
			}
			entry.pending = false;
			scrollSoon();
		}, 0);
	}

	function onKey(e: KeyboardEvent) {
		if (e.key === 'Enter' && !e.shiftKey) {
			e.preventDefault();
			submit();
		}
	}

	function runExample(src: string) {
		input = src;
		submit();
	}

	function reset() {
		entries = [];
		input = '';
		onReset?.();
	}

	// Hover a cell → lazily fetch its HOL theorem (once).
	function loadHol(entry: Entry) {
		if (!showCell || entry.holTried || entry.directive || !entry.ok || entry.pending) return;
		entry.holTried = true;
		try {
			const h = showCell(entry.input);
			entry.hol = h && h.length ? h : null;
		} catch {
			entry.hol = null;
		}
	}
</script>

{#if examples.length}
	<div class="examples">
		{#each examples as c}
			<button disabled={!ready} onclick={() => runExample(c.src)} title={c.src}>{c.title}</button>
		{/each}
	</div>
{/if}

<div class="repl">
	<div class="transcript" bind:this={scroller}>
		{#if loadError}
			<div class="line err">failed to load wasm: {loadError}</div>
		{:else if !ready}
			<div class="line muted">loading the kernel (WASM)…</div>
		{:else if entries.length === 0}
			<div class="line muted">ready — type a form below, or pick an example.</div>
		{/if}

		{#each entries as entry}
			<div
				class="cell"
				class:has-hol={showCell && !entry.directive && entry.ok}
				onmouseenter={() => loadHol(entry)}
				role="group"
			>
				<div class="in"><span class="p">{prompt}</span> <span class="src">{entry.input}</span></div>
				{#if entry.pending}
					<div class="out muted">proving…</div>
				{:else if entry.ok}
					<div class="out">{entry.output}</div>
				{:else}
					<div class="out err">{entry.output}</div>
				{/if}
				{#if entry.hol}
					<div class="hol" title="the kernel theorem behind this value">{entry.hol}</div>
				{:else if showCell && !entry.directive && entry.ok && !entry.pending && !entry.holTried}
					<div class="hol-hint">hover for ⊢ proof</div>
				{/if}
			</div>
		{/each}
	</div>

	<div class="prompt-line">
		<span class="p">{prompt}</span>
		<textarea
			class="input"
			bind:value={input}
			onkeydown={onKey}
			{placeholder}
			spellcheck="false"
			rows="1"
			disabled={!ready}
		></textarea>
		{#if entries.length}
			<button class="reset" onclick={reset} title="clear the transcript and reset the session">⟲ reset</button>
		{/if}
	</div>
</div>

<style>
	.examples {
		display: flex;
		flex-wrap: wrap;
		gap: 0.35rem;
		margin: 1rem 0 0.6rem;
	}
	.examples button {
		font: inherit;
		font-size: 0.78rem;
		color: var(--fg);
		background: var(--surface);
		border: 1px solid var(--border);
		border-radius: 5px;
		padding: 0.25rem 0.55rem;
		cursor: pointer;
	}
	.examples button:hover:not(:disabled) {
		border-color: var(--accent);
	}
	.examples button:disabled {
		opacity: 0.5;
		cursor: default;
	}
	.repl {
		border: 1px solid var(--border);
		border-radius: 8px;
		background: var(--surface);
		overflow: hidden;
		font-family: var(--font-mono);
	}
	.transcript {
		max-height: 26rem;
		min-height: 10rem;
		overflow-y: auto;
		padding: 0.6rem 0.7rem;
	}
	.line {
		font-size: 0.85rem;
		padding: 0.2rem 0;
	}
	.cell {
		padding: 0.35rem 0.4rem;
		margin: 0 -0.4rem;
		border-radius: 5px;
	}
	.cell.has-hol:hover {
		background: color-mix(in srgb, var(--accent) 8%, transparent);
	}
	.in {
		font-size: 0.85rem;
		line-height: 1.5;
		white-space: pre-wrap;
		word-break: break-word;
	}
	.p {
		color: var(--accent);
		user-select: none;
	}
	.in .src {
		color: var(--fg);
	}
	.out {
		font-size: 0.85rem;
		line-height: 1.5;
		padding-left: 1.4rem;
		white-space: pre-wrap;
		word-break: break-word;
		color: color-mix(in srgb, #30a46c 55%, var(--fg));
	}
	.out.muted {
		color: var(--muted);
	}
	.out.err {
		color: color-mix(in srgb, #e5484d 65%, var(--fg));
	}
	.hol {
		margin: 0.2rem 0 0.1rem 1.4rem;
		padding: 0.3rem 0.5rem;
		font-size: 0.78rem;
		line-height: 1.45;
		color: var(--fg);
		background: color-mix(in srgb, var(--accent) 10%, var(--surface));
		border-left: 2px solid var(--accent);
		border-radius: 0 4px 4px 0;
		white-space: pre-wrap;
		word-break: break-word;
	}
	.hol-hint {
		margin-left: 1.4rem;
		font-size: 0.72rem;
		color: var(--muted);
		opacity: 0;
		transition: opacity 0.12s;
	}
	.cell.has-hol:hover .hol-hint {
		opacity: 0.75;
	}
	.prompt-line {
		display: flex;
		align-items: flex-start;
		gap: 0.4rem;
		border-top: 1px solid var(--border);
		padding: 0.5rem 0.7rem;
		background: color-mix(in srgb, var(--fg) 3%, var(--surface));
	}
	.prompt-line .p {
		font-size: 0.9rem;
		padding-top: 0.15rem;
	}
	.input {
		flex: 1;
		font: inherit;
		font-size: 0.9rem;
		font-family: var(--font-mono);
		color: var(--fg);
		background: transparent;
		border: 0;
		outline: none;
		resize: none;
		line-height: 1.5;
		min-height: 1.5rem;
		overflow: hidden;
	}
	.input::placeholder {
		color: var(--muted);
	}
	.reset {
		font: inherit;
		font-size: 0.72rem;
		color: var(--muted);
		background: transparent;
		border: 1px solid var(--border);
		border-radius: 5px;
		padding: 0.15rem 0.45rem;
		cursor: pointer;
		white-space: nowrap;
	}
	.reset:hover {
		color: var(--fg);
		border-color: var(--accent);
	}
</style>
