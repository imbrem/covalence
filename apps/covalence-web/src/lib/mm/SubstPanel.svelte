<script lang="ts">
	// The click-a-step mapping panel (the LAMP "how do the hypotheses map?"
	// view): for one applied assertion, its hypotheses before and after
	// substitution side by side, plus the variable → expression table.
	//
	// EVERY FIELD HERE IS THE CHECKER'S OWN OUTPUT. `subst` is the substitution
	// the Metamath verifier actually derived while replaying this proof, and
	// `hyps[k].before/after` are its hypotheses as declared and as instantiated
	// (server invariant: `hyps[k].after === args[k]`). Do NOT replace this with
	// a client-side re-derivation — the point of the panel is that it shows what
	// the checker did, not what we think it should have done.
	import type { MmProofStep } from 'covalence-client';
	import { renderMm } from '$lib/mmUnicode';

	interface Props {
		step: MmProofStep;
		unicode: boolean;
		symbolMap: Record<string, string>;
	}
	const { step, unicode, symbolMap }: Props = $props();

	const show = (s: string) => renderMm(s, unicode, symbolMap);
</script>

<div class="subst-panel" data-testid="subst-panel">
	<div class="sp-head">
		<span class="flabel">step {step.i} · applied</span>
		<code class="sp-label" data-testid="subst-label">{step.label}</code>
		<span class="dim">→</span>
		<code class="sp-result">{show(step.expr)}</code>
	</div>

	{#if step.hyps && step.hyps.length > 0}
		<div class="flabel sub">hypothesis mapping</div>
		<table class="map" data-testid="subst-hyps">
			<thead>
				<tr><th>hyp</th><th>as declared</th><th>as applied</th></tr>
			</thead>
			<tbody>
				{#each step.hyps as h, k (h.label + k)}
					<tr>
						<td class="hl">{h.label}</td>
						<td class="before">{show(h.before)}</td>
						<td class="after">{show(h.after)}</td>
					</tr>
				{/each}
			</tbody>
		</table>
	{:else}
		<p class="note">No hypotheses — this assertion takes no arguments.</p>
	{/if}

	{#if step.subst && step.subst.length > 0}
		<div class="flabel sub">substitution</div>
		<table class="map subst" data-testid="subst-vars">
			<tbody>
				{#each step.subst as s (s.var)}
					<tr>
						<td class="hl">{show(s.var)}</td>
						<td class="dim arrow">↦</td>
						<td class="after">{show(s.expr)}</td>
					</tr>
				{/each}
			</tbody>
		</table>
		<p class="note">
			The substitution the checker derived while replaying this proof — expressions carry no
			typecode.
		</p>
	{/if}
</div>

<style>
	.subst-panel {
		border: 1px solid var(--accent);
		border-radius: 6px;
		padding: 0.6rem;
		margin: 0.4rem 0 0.6rem;
		background: rgba(124, 111, 247, 0.06);
	}
	.sp-head {
		display: flex;
		align-items: baseline;
		gap: 0.4rem;
		flex-wrap: wrap;
		margin-bottom: 0.4rem;
	}
	.sp-label {
		font-weight: 600;
		color: var(--accent);
	}
	.sp-result {
		font-size: 0.78rem;
	}
	.flabel {
		font-size: 0.65rem;
		text-transform: uppercase;
		letter-spacing: 0.06em;
		color: var(--muted);
	}
	.flabel.sub {
		display: block;
		margin: 0.5rem 0 0.25rem;
	}
	table.map {
		width: 100%;
		border-collapse: collapse;
		font-family: var(--font-mono);
		font-size: 0.76rem;
	}
	table.map th {
		text-align: left;
		font-weight: 400;
		font-size: 0.62rem;
		text-transform: uppercase;
		letter-spacing: 0.05em;
		color: var(--muted);
		padding: 0 0.5rem 0.2rem 0;
		border-bottom: 1px solid var(--border);
	}
	table.map td {
		padding: 0.22rem 0.5rem 0.22rem 0;
		border-bottom: 1px dashed var(--border);
		vertical-align: top;
		word-break: break-word;
	}
	td.hl {
		color: var(--fg);
		font-weight: 600;
		white-space: nowrap;
	}
	td.before {
		color: var(--muted);
	}
	td.after {
		color: var(--fg);
	}
	td.arrow {
		width: 1.5em;
		text-align: center;
	}
	.dim {
		color: var(--muted);
	}
	.note {
		font-size: 0.72rem;
		color: var(--muted);
		margin: 0.35rem 0 0;
		line-height: 1.4;
	}
</style>
