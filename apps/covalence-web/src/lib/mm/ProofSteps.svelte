<script lang="ts">
	// Step-by-step view of a verifying proof replay (GET .../steps, or the
	// `steps` a successful /verify returns — same shape).
	//
	// Two things this deliberately does NOT do:
	//   - It never expands compressed-proof sharing. `save` and `heapRef` steps
	//     render as themselves, because the heap is the interesting structure:
	//     silently inlining a heapRef would hide the fact that a subproof was
	//     reused rather than re-derived.
	//   - It never reconstructs anything. Every expression, substitution and
	//     stack depth shown is what the checker reported.
	import type { MmProofStep, MmStepKind } from 'covalence-client';
	import { renderMm } from '$lib/mmUnicode';
	import SubstPanel from './SubstPanel.svelte';

	interface Props {
		steps: MmProofStep[];
		unicode: boolean;
		symbolMap: Record<string, string>;
		/** Reset selection when the caller switches theorems. */
		resetKey?: string;
	}
	const { steps, unicode, symbolMap, resetKey = '' }: Props = $props();

	let sel = $state<number | null>(null);
	let listEl = $state<HTMLDivElement | null>(null);

	// New theorem ⇒ drop the old step selection rather than pointing at an index
	// that means something else now.
	$effect(() => {
		resetKey;
		sel = null;
	});

	const maxDepth = $derived(steps.reduce((m, s) => Math.max(m, s.stackDepth), 0));
	const selStep = $derived(sel != null ? (steps[sel] ?? null) : null);

	const KIND_LABEL: Record<MmStepKind, string> = {
		floatHyp: '$f',
		essentialHyp: '$e',
		assertion: 'apply',
		save: 'save',
		heapRef: 'heap'
	};

	function select(i: number) {
		sel = i;
		// Keep the focused row on screen during keyboard paging.
		listEl?.querySelector<HTMLElement>(`[data-step="${i}"]`)?.scrollIntoView({ block: 'nearest' });
	}

	// j/k mirror the arrow keys (vi habit); Home/End jump to the ends. Bound on
	// the list container, which is focusable, so it never steals the page's keys.
	function onKey(e: KeyboardEvent) {
		if (steps.length === 0) return;
		const cur = sel ?? -1;
		let next: number | null = null;
		if (e.key === 'ArrowDown' || e.key === 'j') next = Math.min(cur + 1, steps.length - 1);
		else if (e.key === 'ArrowUp' || e.key === 'k') next = Math.max(cur - 1, 0);
		else if (e.key === 'Home') next = 0;
		else if (e.key === 'End') next = steps.length - 1;
		if (next === null) return;
		e.preventDefault();
		select(next);
	}
</script>

<div class="proof-steps">
	<div class="ps-head">
		<span class="dim">{steps.length} steps · max stack depth {maxDepth}</span>
		<span class="dim hint">↑/↓ or j/k to page through</span>
	</div>
	<div
		class="ps-list"
		bind:this={listEl}
		role="listbox"
		tabindex="0"
		aria-label="proof steps"
		aria-activedescendant={sel != null ? `mm-step-${sel}` : undefined}
		onkeydown={onKey}
	>
		{#each steps as s (s.i)}
			<button
				id="mm-step-{s.i}"
				class="ps-row kind-{s.kind}"
				class:sel={sel === s.i}
				data-step={s.i}
				data-testid="proof-step"
				role="option"
				aria-selected={sel === s.i}
				onclick={() => select(s.i)}
			>
				<span class="idx">{s.i}</span>
				{#if s.label === null}
					<!-- save/heapRef cite no label: mark the sharing operation itself. -->
					<span class="lbl none" data-testid="step-no-label"
						>{s.kind === 'heapRef' ? `#${s.heapIndex}` : '·'}</span
					>
				{:else}
					<span class="lbl">{s.label}</span>
				{/if}
				<span class="kind">{KIND_LABEL[s.kind]}</span>
				<span class="expr">{renderMm(s.expr, unicode, symbolMap)}</span>
				<!-- The RPN stack made legible: a fixed track with a fill scaled to
				     the depth, so pushes and pops read at a glance down the column. -->
				<span class="depth" title="stack depth after this step">
					<span class="dtrack">
						<span class="dfill" style="width:{(s.stackDepth / Math.max(maxDepth, 1)) * 100}%"
						></span>
					</span>
					<span class="dnum">{s.stackDepth}</span>
				</span>
			</button>
			{#if sel === s.i && s.kind === 'assertion'}
				<SubstPanel step={s} {unicode} {symbolMap} />
			{/if}
		{/each}
	</div>
	{#if selStep && selStep.kind !== 'assertion'}
		<p class="note" data-testid="step-note">
			{#if selStep.kind === 'save'}
				A <b>save</b>: the compressed proof recorded this expression on the heap for later reuse. It
				pushes nothing, so the stack depth is unchanged.
			{:else if selStep.kind === 'heapRef'}
				A <b>heap reference</b>: re-pushes the expression saved at heap index
				<b>{selStep.heapIndex}</b>. The subproof was shared, not re-derived — which is the whole
				point of the compressed format, so it is shown rather than expanded.
			{:else if selStep.kind === 'floatHyp'}
				A <b>floating hypothesis</b> ($f): pushes the variable's typecode assertion.
			{:else}
				An <b>essential hypothesis</b> ($e) of the theorem being proved.
			{/if}
		</p>
	{:else if !selStep}
		<p class="note">Select a step to see its detail; assertion steps show the substitution.</p>
	{/if}
</div>

<style>
	.ps-head {
		display: flex;
		justify-content: space-between;
		gap: 0.5rem;
		font-size: 0.72rem;
		margin-bottom: 0.3rem;
	}
	.ps-head .hint {
		opacity: 0.7;
	}
	.dim {
		color: var(--muted);
	}
	.ps-list {
		max-height: 22rem;
		overflow-y: auto;
		border: 1px solid var(--border);
		border-radius: 6px;
		background: var(--code-bg);
		scrollbar-width: thin;
		scrollbar-color: var(--border) transparent;
	}
	.ps-list:focus-visible {
		outline: 1px solid var(--accent);
		outline-offset: -1px;
	}
	.ps-row {
		display: flex;
		align-items: center;
		gap: 0.5rem;
		width: 100%;
		text-align: left;
		padding: 0.22rem 0.5rem;
		border: none;
		border-bottom: 1px solid var(--border);
		background: transparent;
		color: var(--fg);
		font-family: var(--font-mono);
		font-size: 0.76rem;
		cursor: pointer;
	}
	.ps-row:hover {
		background: rgba(124, 111, 247, 0.1);
	}
	.ps-row.sel {
		background: rgba(124, 111, 247, 0.2);
	}
	.idx {
		flex: none;
		width: 2.2em;
		text-align: right;
		color: var(--muted);
		font-variant-numeric: tabular-nums;
	}
	.lbl {
		flex: none;
		min-width: 5em;
		font-weight: 600;
	}
	/* save/heapRef have no label — render the slot distinctly rather than blank. */
	.lbl.none {
		font-weight: 400;
		color: var(--warnc);
		font-style: italic;
	}
	.kind {
		flex: none;
		/* Must fit the widest badge ("APPLY") — narrower and it bleeds into the
		   expression column. */
		width: 4.2em;
		font-size: 0.62rem;
		text-transform: uppercase;
		letter-spacing: 0.04em;
		color: var(--muted);
		border: 1px solid var(--border);
		border-radius: 3px;
		padding: 0.02rem 0.2rem;
		text-align: center;
	}
	.kind-assertion .kind {
		color: var(--accent);
		border-color: rgba(124, 111, 247, 0.5);
	}
	.kind-save .kind,
	.kind-heapRef .kind {
		color: var(--warnc);
		border-color: rgba(251, 191, 36, 0.45);
	}
	.expr {
		flex: 1;
		white-space: nowrap;
		overflow: hidden;
		text-overflow: ellipsis;
	}
	.depth {
		flex: none;
		width: 4.5em;
		display: flex;
		align-items: center;
		gap: 0.3rem;
	}
	.dtrack {
		flex: 1;
		height: 6px;
		border-radius: 2px;
		background: var(--border);
		overflow: hidden;
	}
	.dfill {
		display: block;
		height: 100%;
		background: var(--accent);
		border-radius: 2px;
		min-width: 2px;
	}
	.dnum {
		flex: none;
		width: 1.4em;
		text-align: right;
		color: var(--muted);
		font-variant-numeric: tabular-nums;
		font-size: 0.7rem;
	}
	.note {
		font-size: 0.74rem;
		color: var(--muted);
		margin: 0.35rem 0 0;
		line-height: 1.45;
	}
	.note b {
		color: var(--fg);
	}
</style>
