<script lang="ts">
	// The primary REPL: a WebSocket line protocol against `cov serve`. Lines are
	// tab-global (`repl.svelte.ts`) so the session survives navigation; the
	// terminal chrome is shared with the language REPLs via `ReplShell`.
	import { client } from '$lib/api';
	import type { ObjectInfoResponse } from 'covalence-client';
	import ReplShell from '$lib/repl/ReplShell.svelte';
	import {
		WAT_KEYWORDS, WAT_SPECIAL_FORMS, escHtml, highlight as hl, isCodeOutput,
	} from '$lib/repl/sexpr';
	import {
		init, destroy, send, setOutputEl, formatDuration, doPoll,
		getLines, getInput, setInput, getHistory,
		isWsConnected, isHealthy, getLastHealth, getConnectedDuration,
	} from '$lib/repl.svelte';

	const highlight = (text: string) => hl(text, WAT_KEYWORDS);

	// --- Inline preview block detection ---
	// Server emits SVG previews wrapped in sentinel markers that the REPL
	// passes through verbatim. The web REPL renders the SVG inline.
	const PREVIEW_BEGIN = 'cov-preview-svg';
	const PREVIEW_END = '/cov-preview-svg';

	type OutputSegment = { kind: 'text'; value: string } | { kind: 'svg'; value: string };

	function splitPreviewSegments(text: string): OutputSegment[] {
		const segments: OutputSegment[] = [];
		let i = 0;
		while (i < text.length) {
			const start = text.indexOf(PREVIEW_BEGIN, i);
			if (start === -1) {
				if (i < text.length) segments.push({ kind: 'text', value: text.slice(i) });
				break;
			}
			if (start > i) segments.push({ kind: 'text', value: text.slice(i, start) });
			const afterBegin = start + PREVIEW_BEGIN.length;
			const end = text.indexOf(PREVIEW_END, afterBegin);
			if (end === -1) {
				// Unterminated — show the rest as text.
				segments.push({ kind: 'text', value: text.slice(start) });
				break;
			}
			// Strip surrounding newlines added by the emitter.
			const svg = text.slice(afterBegin, end).replace(/^\n/, '').replace(/\n$/, '');
			segments.push({ kind: 'svg', value: svg });
			i = end + PREVIEW_END.length;
			if (text[i] === '\n') i++;
		}
		return segments;
	}

	function trimTrailingNewline(s: string): string {
		return s.endsWith('\n') ? s.slice(0, -1) : s;
	}

	// --- Use shared REPL state ---
	let lines = $derived(getLines());
	let input = $derived(getInput());
	let history = $derived(getHistory());
	let wsConnected = $derived(isWsConnected());
	let healthy = $derived(isHealthy());
	let lastHealth = $derived(getLastHealth());
	let connectedDuration = $derived(getConnectedDuration());

	let outputEl = $state<HTMLElement | null>(null);

	// --- Tooltip state ---
	let tooltipText = $state('');
	let tooltipX = $state(0);
	let tooltipY = $state(0);
	let tooltipVisible = $state(false);
	const infoCache = new Map<string, ObjectInfoResponse>();

	function onOutputMouseOver(e: MouseEvent) {
		const target = e.target as HTMLElement;
		if (target.tagName === 'A' && target.classList.contains('hl-hash')) {
			const hash = target.dataset.hash;
			if (!hash) return;
			showTooltip(hash, target);
		}
	}

	function onOutputMouseOut(e: MouseEvent) {
		const target = e.target as HTMLElement;
		if (target.tagName === 'A' && target.classList.contains('hl-hash')) {
			tooltipVisible = false;
		}
	}

	async function showTooltip(hash: string, el: HTMLElement) {
		const rect = el.getBoundingClientRect();
		tooltipX = rect.left;
		tooltipY = rect.top - 4;

		let info = infoCache.get(hash);
		if (!info) {
			tooltipText = 'loading…';
			tooltipVisible = true;
			const fetched = await client.objectInfo(hash);
			if (fetched) {
				infoCache.set(hash, fetched);
				info = fetched;
			} else {
				tooltipText = 'not found';
				return;
			}
		}
		tooltipText = `${info.kind} · ${formatSize(info.size)}`;
		tooltipVisible = true;
	}

	function formatSize(bytes: number): string {
		if (bytes < 1024) return `${bytes} B`;
		if (bytes < 1024 * 1024) return `${(bytes / 1024).toFixed(1)} KB`;
		return `${(bytes / (1024 * 1024)).toFixed(1)} MB`;
	}

	$effect(() => {
		init();
		return () => destroy();
	});

	$effect(() => {
		if (outputEl) setOutputEl(outputEl);
	});
</script>

{#snippet transcript()}
	{#each lines as line}
		{#if line.kind === 'input'}
			<div class="line input"><span class="prompt">cov&gt;</span> {@html highlight(line.text)}</div>
		{:else if line.kind === 'error'}
			<div class="line error">{line.text}</div>
		{:else}
			{#each splitPreviewSegments(line.text) as seg}
				{#if seg.kind === 'svg'}
					<div class="line preview-svg">{@html seg.value}</div>
				{:else}
					{@const trimmed = trimTrailingNewline(seg.value)}
					{#if trimmed.length > 0}
						<div class="line output">{@html isCodeOutput(trimmed) ? highlight(trimmed) : escHtml(trimmed)}</div>
					{/if}
				{/if}
			{/each}
		{/if}
	{/each}
{/snippet}

{#snippet status()}
	<button
		class="health-dot"
		class:healthy
		class:unhealthy={!healthy}
		onclick={() => doPoll()}
		title={healthy ? 'API connected' : 'API unreachable'}
		aria-label={healthy ? 'API connected' : 'API unreachable'}
	></button>
	<span class="status-text">
		{#if healthy && lastHealth}
			connected {formatDuration(connectedDuration)} &mdash; server up {formatDuration(Math.floor(lastHealth.uptime_secs))}
		{:else}
			API unreachable
		{/if}
	</span>
	{#if wsConnected}
		<span class="ws-badge">ws</span>
	{/if}
{/snippet}

<ReplShell
	prompt="cov>"
	{highlight}
	{transcript}
	{status}
	{history}
	specialForms={WAT_SPECIAL_FORMS}
	value={input}
	onValueChange={setInput}
	onSubmit={send}
	placeholder={wsConnected ? 'help' : 'connecting...'}
	busy={!wsConnected}
	bind:outputEl
	{onOutputMouseOver}
	{onOutputMouseOut}
/>

{#if tooltipVisible}
	<div class="hash-tooltip" style="left:{tooltipX}px;top:{tooltipY}px">
		{tooltipText}
	</div>
{/if}

<style>
	/* Transcript line kinds and highlight colors live in `ReplShell`; only the
	   page's own extras are styled here. */
	.line.preview-svg {
		background: #ffffff;
		border: 1px solid var(--border);
		border-radius: 6px;
		padding: 0.5rem;
		margin: 0.25rem 0;
		max-width: 100%;
		overflow-x: auto;
		white-space: normal;
	}

	.line.preview-svg :global(svg) {
		max-width: 100%;
		height: auto;
		display: block;
	}

	/* --- Tooltip --- */
	.hash-tooltip {
		position: fixed;
		transform: translateY(-100%);
		background: var(--surface);
		border: 1px solid var(--border);
		border-radius: 4px;
		padding: 0.25rem 0.5rem;
		font-size: 0.75rem;
		color: var(--fg);
		pointer-events: none;
		z-index: 100;
		white-space: nowrap;
	}

	/* --- Status bar --- */
	.health-dot {
		width: 8px;
		height: 8px;
		border-radius: 50%;
		border: none;
		cursor: pointer;
		padding: 0;
		flex-shrink: 0;
	}

	.health-dot.healthy {
		background: #4ade80;
		box-shadow: 0 0 4px #4ade8066;
	}

	.health-dot.unhealthy {
		background: #f87171;
		box-shadow: 0 0 4px #f8717166;
	}

	.status-text {
		font-size: 0.75rem;
		color: var(--muted);
	}

	.ws-badge {
		font-size: 0.65rem;
		color: var(--accent);
		border: 1px solid var(--accent);
		border-radius: 3px;
		padding: 0 4px;
		line-height: 1.4;
		margin-left: auto;
	}
</style>
