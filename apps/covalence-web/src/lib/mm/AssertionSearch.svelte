<script lang="ts">
	// Debounced type-ahead over GET .../search.
	//
	// The debounce is not cosmetic: a needle that matches nothing forces a full
	// scan of the database (~25 ms on set.mm in release, ~4× that in a debug
	// build), so a keystroke-per-request type-ahead would queue up behind itself
	// on the big databases.
	import type { MmSearchHit } from 'covalence-client';
	import { renderMm } from '$lib/mmUnicode';

	interface Props {
		search: (q: string) => Promise<{ results: MmSearchHit[]; truncated: boolean }>;
		onpick: (hit: MmSearchHit) => void;
		unicode: boolean;
		symbolMap: Record<string, string>;
		disabled?: boolean;
	}
	const { search, onpick, unicode, symbolMap, disabled = false }: Props = $props();

	const DEBOUNCE_MS = 180;

	let q = $state('');
	let hits = $state<MmSearchHit[]>([]);
	let truncated = $state(false);
	let busy = $state(false);
	let error = $state('');
	// Monotonic request id: a slow response for an older needle must not
	// overwrite the results of a newer one.
	let seq = 0;

	$effect(() => {
		const needle = q;
		const id = ++seq;
		const timer = setTimeout(async () => {
			busy = true;
			error = '';
			try {
				const res = await search(needle);
				if (id !== seq) return; // superseded
				hits = res.results;
				truncated = res.truncated;
			} catch (e) {
				if (id !== seq) return;
				hits = [];
				error = e instanceof Error ? e.message : String(e);
			} finally {
				if (id === seq) busy = false;
			}
		}, DEBOUNCE_MS);
		return () => clearTimeout(timer);
	});
</script>

<div class="asearch">
	<div class="as-bar">
		<input
			type="text"
			class="search"
			bind:value={q}
			{disabled}
			placeholder="search assertions by label or statement…"
			spellcheck="false"
			data-testid="assertion-search-input"
		/>
		{#if busy}<span class="dim">…</span>{/if}
	</div>
	{#if error}
		<p class="err" data-testid="assertion-search-error">search failed: {error}</p>
	{:else if hits.length === 0}
		<p class="note">{q ? `nothing matches “${q}”.` : 'no assertions.'}</p>
	{:else}
		<div class="as-list">
			{#each hits as h (h.label)}
				<button
					class="as-item"
					data-testid="assertion-result"
					{disabled}
					onclick={() => onpick(h)}
					title="apply {h.label} to the selected goal"
				>
					<span class="lbl">{h.label}</span>
					<span class="kind kind-{h.kind}">{h.kind}</span>
					<span class="mm">{renderMm(h.mm, unicode, symbolMap)}</span>
					<span class="hyps" title="{h.hypCount} essential hypotheses">{h.hypCount} $e</span>
				</button>
			{/each}
		</div>
		{#if truncated}
			<p class="note">more results exist — narrow the search.</p>
		{/if}
	{/if}
</div>

<style>
	.as-bar {
		display: flex;
		align-items: center;
		gap: 0.4rem;
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
	.as-list {
		margin-top: 0.35rem;
		max-height: 14rem;
		overflow-y: auto;
		border: 1px solid var(--border);
		border-radius: 6px;
		background: var(--code-bg);
		scrollbar-width: thin;
		scrollbar-color: var(--border) transparent;
	}
	.as-item {
		display: flex;
		align-items: center;
		gap: 0.5rem;
		width: 100%;
		text-align: left;
		padding: 0.25rem 0.5rem;
		border: none;
		border-bottom: 1px solid var(--border);
		background: transparent;
		color: var(--fg);
		font-family: var(--font-mono);
		font-size: 0.76rem;
		cursor: pointer;
	}
	.as-item:hover:not(:disabled) {
		background: rgba(124, 111, 247, 0.12);
	}
	.as-item:disabled {
		opacity: 0.5;
		cursor: default;
	}
	.as-item .lbl {
		flex: none;
		min-width: 5em;
		font-weight: 600;
	}
	.as-item .kind {
		flex: none;
		font-size: 0.6rem;
		text-transform: uppercase;
		letter-spacing: 0.04em;
		color: var(--muted);
		border: 1px solid var(--border);
		border-radius: 3px;
		padding: 0.02rem 0.25rem;
	}
	.as-item .kind-axiom {
		color: var(--warnc);
		border-color: rgba(251, 191, 36, 0.4);
	}
	.as-item .kind-def {
		color: var(--accent);
		border-color: rgba(124, 111, 247, 0.4);
	}
	.as-item .mm {
		flex: 1;
		color: var(--muted);
		white-space: nowrap;
		overflow: hidden;
		text-overflow: ellipsis;
	}
	.as-item .hyps {
		flex: none;
		color: var(--muted);
		font-size: 0.7rem;
	}
	.dim {
		color: var(--muted);
	}
	.note {
		font-size: 0.74rem;
		color: var(--muted);
		margin: 0.35rem 0 0;
	}
	.err {
		font-size: 0.76rem;
		color: var(--bad);
		margin: 0.35rem 0 0;
	}
</style>
