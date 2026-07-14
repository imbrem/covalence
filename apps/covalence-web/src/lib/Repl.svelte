<script lang="ts">
	// A reusable terminal-style REPL: a scrolling transcript + a prompt line.
	// `evalCell` is async (a `fetch` to the running server's native kernel —
	// e.g. POST /api/lisp). `showCell`, if given, lazily fetches HOL info for a
	// cell on hover (the `⊢ lhs = rhs` theorem, via the `#show` directive).
	type EvalResult = { ok: boolean; result: string; error: string };
	type Example = { title: string; src: string };

	let {
		evalCell,
		showCell = null,
		onReset = null,
		examples = [],
		prompt = 'λ>',
		placeholder = 'type a form, press Enter — Shift+Enter for a newline'
	}: {
		evalCell: (src: string) => Promise<EvalResult>;
		showCell?: ((src: string) => Promise<string>) | null;
		onReset?: (() => void) | null;
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
	let busy = $state(false);
	let scroller = $state<HTMLDivElement | null>(null);

	function scrollSoon() {
		requestAnimationFrame(() => {
			if (scroller) scroller.scrollTop = scroller.scrollHeight;
		});
	}

	async function submit() {
		const src = input.trim();
		if (!src || busy) return;
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
		busy = true;
		try {
			const r = await evalCell(src);
			entry.output = r.ok ? r.result : r.error;
			entry.ok = r.ok;
		} catch (e) {
			entry.output = String(e);
			entry.ok = false;
		}
		entry.pending = false;
		busy = false;
		scrollSoon();
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
	async function loadHol(entry: Entry) {
		if (!showCell || entry.holTried || entry.directive || !entry.ok || entry.pending) return;
		entry.holTried = true;
		try {
			const h = await showCell(entry.input);
			entry.hol = h && h.length ? h : null;
		} catch {
			entry.hol = null;
		}
	}
</script>

{#if examples.length}
	<div class="examples">
		{#each examples as c}
			<button onclick={() => runExample(c.src)} title={c.src}>{c.title}</button>
		{/each}
		{#if onReset || entries.length}
			<button class="reset" onclick={reset} title="clear the transcript and reset the session">⟲ reset</button>
		{/if}
	</div>
{/if}

<div class="term">
	<div class="transcript" bind:this={scroller}>
		{#if entries.length === 0}
			<div class="hint">Type a form below and press Enter — or pick an example.</div>
		{/if}
		{#each entries as entry}
			<div
				class="cell"
				class:has-hol={showCell && !entry.directive && entry.ok}
				onmouseenter={() => loadHol(entry)}
				role="group"
			>
				<div class="in"><span class="p">{prompt}</span> {entry.input}</div>
				{#if entry.pending}
					<div class="out muted">proving…</div>
				{:else if entry.ok}
					<div class="out">{entry.output}</div>
				{:else}
					<div class="out err">{entry.output}</div>
				{/if}
				{#if entry.hol}
					<div class="hol" title="the kernel theorem behind this value">{entry.hol}</div>
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
			disabled={busy}
		></textarea>
	</div>
</div>

<style>
	.examples {
		display: flex;
		flex-wrap: wrap;
		gap: 0.35rem;
		margin: 1rem 0 0.5rem;
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
	.examples button:hover {
		border-color: var(--accent);
	}
	.examples .reset {
		margin-left: auto;
		color: var(--muted);
	}

	/* A terminal, not a box: flush background, hairline separators, no card. */
	.term {
		font-family: var(--font-mono);
		border-top: 1px solid var(--border);
	}
	.transcript {
		max-height: 30rem;
		overflow-y: auto;
		padding: 0.6rem 0.1rem;
	}
	.hint {
		color: var(--muted);
		font-size: 0.85rem;
		padding: 0.3rem 0.2rem;
	}
	.cell {
		padding: 0.25rem 0.3rem;
		margin: 0 -0.3rem;
		border-radius: 4px;
	}
	.cell.has-hol:hover {
		background: color-mix(in srgb, var(--accent) 7%, transparent);
	}
	.in {
		font-size: 0.9rem;
		line-height: 1.5;
		white-space: pre-wrap;
		word-break: break-word;
		color: var(--fg);
	}
	.p {
		color: var(--accent);
		user-select: none;
	}
	.out {
		font-size: 0.9rem;
		line-height: 1.5;
		padding-left: 1.5rem;
		white-space: pre-wrap;
		word-break: break-word;
		color: color-mix(in srgb, #30a46c 60%, var(--fg));
	}
	.out.muted {
		color: var(--muted);
	}
	.out.err {
		color: color-mix(in srgb, #e5484d 70%, var(--fg));
	}
	.hol {
		margin: 0.2rem 0 0.15rem 1.5rem;
		padding: 0.3rem 0.5rem;
		font-size: 0.8rem;
		line-height: 1.45;
		color: var(--fg);
		background: color-mix(in srgb, var(--accent) 9%, transparent);
		border-left: 2px solid var(--accent);
		border-radius: 0 4px 4px 0;
		white-space: pre-wrap;
		word-break: break-word;
	}
	.prompt-line {
		display: flex;
		align-items: flex-start;
		gap: 0.5rem;
		border-top: 1px solid var(--border);
		padding: 0.55rem 0.2rem;
	}
	.prompt-line .p {
		font-size: 0.95rem;
		padding-top: 0.1rem;
	}
	.input {
		flex: 1;
		font: inherit;
		font-size: 0.95rem;
		font-family: var(--font-mono);
		color: var(--fg);
		background: transparent;
		border: 0;
		outline: none;
		resize: none;
		line-height: 1.5;
		min-height: 1.5rem;
	}
	.input::placeholder {
		color: var(--muted);
	}
</style>
