<script lang="ts">
	// A reusable terminal-style REPL: a scrolling transcript + a prompt line.
	// `evalCell` is async (a `fetch` to the running server's native kernel —
	// e.g. POST /api/lisp). `showCell`, if given, lazily fetches HOL info for a
	// cell on hover: the FULL `hyps ⊢ lhs = rhs` sequent (turnstile included),
	// via the `#show` directive. The string is rendered verbatim — the server
	// prints the genuine kernel theorem, hypotheses and all; the client never
	// adds a turnstile of its own (that would misstate a hypothesis-carrying
	// theorem as `⊢ concl`).
	//
	// `help` is an optional snippet rendered *inline in the transcript* when the
	// user types `#help` — a first, minimal "widget result" (rich HTML in the
	// REPL), the groundwork for IPython-style widget outputs.
	import type { Snippet } from 'svelte';

	type EvalResult = { ok: boolean; result: string; error: string };
	// `active` marks a button as the currently-selected one (e.g. the current
	// dialect's `#lang` tab on /lisp) — purely presentational, so the component
	// stays agnostic about what "active" means.
	type Example = { title: string; src: string; active?: boolean };

	let {
		evalCell,
		showCell = null,
		onReset = null,
		help = null,
		examples = [],
		prompt = 'λ>',
		placeholder = 'type a form, press Enter — Shift+Enter for a newline'
	}: {
		evalCell: (src: string) => Promise<EvalResult>;
		showCell?: ((src: string) => Promise<string>) | null;
		onReset?: (() => void) | null;
		help?: Snippet | null;
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
		widget: boolean;
		hol: string | null;
		holTried: boolean;
		// `#show` failed (or returned nothing) for this cell — e.g. a
		// defun/defthm ack, which is not a reducible expression. No popover:
		// a turnstile with no theorem behind it would be a false claim.
		holFailed: boolean;
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

	function blankEntry(src: string, over: Partial<Entry> = {}): Entry {
		return {
			input: src,
			output: '',
			ok: true,
			directive: src.startsWith('#'),
			pending: true,
			widget: false,
			hol: null,
			holTried: false,
			holFailed: false,
			...over
		};
	}

	async function submit() {
		const src = input.trim();
		if (!src || busy) return;
		input = '';
		// `#help` renders the help snippet inline as a widget — no server round-trip.
		if (src === '#help' && help) {
			entries.push(blankEntry(src, { pending: false, widget: true }));
			scrollSoon();
			return;
		}
		entries.push(blankEntry(src));
		// Mutate through the array proxy (Svelte 5 deep reactivity): a captured
		// raw reference would update the data but never fire the signal, leaving
		// the cell stuck on "proving…".
		const e = entries[entries.length - 1];
		scrollSoon();
		busy = true;
		try {
			const r = await evalCell(src);
			e.output = r.ok ? r.result : r.error;
			e.ok = r.ok;
		} catch (err) {
			e.output = String(err);
			e.ok = false;
		}
		e.pending = false;
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

	// Split an error message into plain / `#lang …` segments so a dialect hint
	// in a server error ("unknown #lang `x` (try: …)", "… try #lang scheme")
	// stands out visually. Light formatting only — the text itself is untouched.
	function errSegments(msg: string): { text: string; hint: boolean }[] {
		const out: { text: string; hint: boolean }[] = [];
		const re = /#lang(?:\s+[A-Za-z][\w-]*)?/g;
		let last = 0;
		for (const m of msg.matchAll(re)) {
			const at = m.index ?? 0;
			if (at > last) out.push({ text: msg.slice(last, at), hint: false });
			out.push({ text: m[0], hint: true });
			last = at + m[0].length;
		}
		if (last < msg.length) out.push({ text: msg.slice(last), hint: false });
		return out;
	}

	// Hover a cell → lazily fetch its HOL sequent (once). On failure the cell
	// is marked `holFailed`, which removes its popover for good.
	async function loadHol(entry: Entry) {
		if (!showCell || entry.holTried || entry.directive || !entry.ok || entry.pending) return;
		entry.holTried = true;
		try {
			const h = await showCell(entry.input);
			entry.hol = h && h.length ? h : null;
		} catch {
			entry.hol = null;
		}
		entry.holFailed = entry.hol === null;
		// If the fetch failed while this cell's popover is up, drop it now — a
		// lingering "fetching proof…" with no theorem behind it is a false claim.
		if (entry.holFailed && hover?.entry === entry) hover = null;
	}

	// The hover popover is a single FIXED-position floating layer rendered
	// outside the transcript, so the scrolling container can never clip it (the
	// old in-cell absolute popover was cut off above the first cells and popped
	// a scrollbar). It prefers to sit ABOVE the hovered cell and flips below
	// when there isn't room; a short hide delay lets the cursor travel into the
	// popover to scroll a long sequent.
	let hover = $state<{ entry: Entry; rect: DOMRect } | null>(null);
	let hideTimer: ReturnType<typeof setTimeout> | undefined;

	function showHover(entry: Entry, el: HTMLElement) {
		clearTimeout(hideTimer);
		loadHol(entry);
		hover = { entry, rect: el.getBoundingClientRect() };
	}
	function scheduleHide() {
		clearTimeout(hideTimer);
		hideTimer = setTimeout(() => (hover = null), 120);
	}
	function cancelHide() {
		clearTimeout(hideTimer);
	}

	// Geometry for the floating popover. Above the cell when at least ~7rem of
	// viewport is available there, else below; height capped to the free space.
	const holStyle = $derived.by(() => {
		if (!hover) return '';
		const r = hover.rect;
		const gap = 4;
		const left = r.left + 16;
		const width = Math.max(r.width - 24, 200);
		const spaceAbove = r.top - gap - 8;
		const above = spaceAbove > 112;
		const maxH = Math.min(224, above ? spaceAbove : window.innerHeight - r.bottom - gap - 8);
		const anchor = above
			? `bottom: ${window.innerHeight - r.top + gap}px;`
			: `top: ${r.bottom + gap}px;`;
		return `left: ${left}px; width: ${width}px; max-height: ${Math.max(maxH, 60)}px; ${anchor}`;
	});
</script>

{#if examples.length}
	<div class="examples">
		{#each examples as c}
			<button class:active={c.active} onclick={() => runExample(c.src)} title={c.src}>
				{c.title}
			</button>
		{/each}
		{#if onReset || entries.length}
			<button class="reset" onclick={reset} title="clear the transcript and reset the session">⟲ reset</button>
		{/if}
	</div>
{/if}

<div class="term">
	<!-- Scrolling makes the popover's anchor rect stale — just dismiss it. -->
	<div class="transcript" bind:this={scroller} onscroll={() => (hover = null)}>
		{#if entries.length === 0}
			<div class="hint">
				Type a form below and press Enter — or pick an example.{#if help}
					Type <code>#help</code> for docs.{/if}
			</div>
		{/if}
		{#each entries as entry}
			{@const hasHol =
				!!showCell && !entry.directive && entry.ok && !entry.pending && !entry.widget && !entry.holFailed}
			<div
				class="cell"
				class:has-hol={hasHol}
				onmouseenter={(e) => hasHol && showHover(entry, e.currentTarget as HTMLElement)}
				onmouseleave={scheduleHide}
				role="group"
			>
				<div class="in"><span class="p">{prompt}</span> {entry.input}</div>
				{#if entry.widget && help}
					<!-- A "widget result": rich HTML rendered inline in the transcript
					     (groundwork for IPython-style widget outputs). -->
					<div class="widget">{@render help()}</div>
				{:else if entry.pending}
					<div class="out muted">proving…</div>
				{:else if entry.ok}
					<div class="out">{entry.output}</div>
				{:else}
					<!-- Errors get the same care as values: a gutter mark, the message
					     verbatim (only *marked up*, never rewritten), and any `#lang …`
					     dialect hint highlighted as a chip. -->
					<div class="out err">
						<span class="err-mark" aria-hidden="true">✗</span
						>{#each errSegments(entry.output) as seg}{#if seg.hint}<span class="lang-hint"
									>{seg.text}</span
								>{:else}{seg.text}{/if}{/each}
					</div>
				{/if}
			</div>
		{/each}
	</div>

	{#if hover}
		<!-- Transient floating popover (single instance, position: fixed — never
		     clipped by the transcript's scroll box, never affects its scroll
		     height). Shown while the cursor is on the cell or the popover
		     itself; gone on leave or scroll. The sequent string (`hyps ⊢ concl`,
		     from `#show`) is rendered VERBATIM — no client-side turnstile. While
		     the fetch is in flight a plain "fetching proof…" shows, asserting
		     nothing. -->
		<div
			class="hol"
			role="tooltip"
			style={holStyle}
			onmouseenter={cancelHide}
			onmouseleave={scheduleHide}
		>
			{#if hover.entry.hol}
				<span class="hol-body">{hover.entry.hol}</span>
			{:else}
				<span class="hol-body hol-pending">fetching proof…</span>
			{/if}
		</div>
	{/if}

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
	.examples button.active {
		border-color: var(--accent);
		color: var(--accent);
		background: color-mix(in srgb, var(--accent) 10%, transparent);
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
		overflow-x: hidden;
		padding: 0.6rem 0.1rem;
	}
	.hint {
		color: var(--muted);
		font-size: 0.85rem;
		padding: 0.3rem 0.2rem;
	}
	.cell {
		position: relative;
		padding: 0.25rem 0.3rem;
		margin: 0 -0.3rem;
		border-radius: 4px;
	}
	.cell.has-hol {
		cursor: help;
	}
	.cell.has-hol:hover {
		background: color-mix(in srgb, var(--accent) 7%, transparent);
	}
	.in {
		font-size: 0.9rem;
		line-height: 1.5;
		white-space: pre-wrap;
		overflow-wrap: anywhere;
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
		overflow-wrap: anywhere;
		color: color-mix(in srgb, #30a46c 60%, var(--fg));
	}
	.out.muted {
		color: var(--muted);
	}
	.out.err {
		color: color-mix(in srgb, #e5484d 70%, var(--fg));
	}
	.err-mark {
		color: #e5484d;
		margin-right: 0.45rem;
		user-select: none;
	}
	/* A `#lang …` mention inside an error — the "switch dialect" hint — pops as
	   a small chip so the fix is obvious at a glance. */
	.lang-hint {
		display: inline-block;
		padding: 0 4px;
		border: 1px solid color-mix(in srgb, var(--accent) 60%, transparent);
		border-radius: 4px;
		background: color-mix(in srgb, var(--accent) 10%, transparent);
		color: var(--accent);
		white-space: nowrap;
	}
	.widget {
		margin: 0.35rem 0 0.35rem 1.5rem;
		padding: 0.6rem 0.8rem;
		border: 1px solid var(--border);
		border-left: 2px solid var(--accent);
		border-radius: 0 6px 6px 0;
		background: color-mix(in srgb, var(--accent) 5%, transparent);
		font-size: 0.83rem;
		line-height: 1.55;
	}
	.hint code,
	.widget :global(code) {
		background: var(--surface);
		border: 1px solid var(--border);
		border-radius: 3px;
		padding: 0 3px;
		font-size: 0.9em;
	}
	/* Transient hover popover — a single fixed-position floating layer (left/
	   width/max-height/anchor set inline from the hovered cell's rect, above
	   the cell or flipped below near the viewport top). Fixed positioning means
	   the transcript's overflow can never clip it and it never disturbs the
	   scroll geometry; its own overflow scrolls long sequents. */
	.hol {
		position: fixed;
		z-index: 30;
		overflow-y: auto;
		padding: 0.45rem 0.6rem;
		font-size: 0.78rem;
		line-height: 1.5;
		color: var(--fg);
		background: var(--surface);
		border: 1px solid var(--accent);
		border-radius: 6px;
		box-shadow: 0 8px 24px rgba(0, 0, 0, 0.45);
		white-space: pre-wrap;
		overflow-wrap: anywhere;
		font-family: var(--font-mono);
	}
	.hol-pending {
		color: var(--muted);
		font-style: italic;
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
