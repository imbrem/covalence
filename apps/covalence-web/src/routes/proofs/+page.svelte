<script lang="ts">
	// PROOF CHECKER page — LIVE. The Haskell dialect, connected to the kernel for
	// PROOF CHECKING: a theorem MODULE (equation statements) and a separate S-expr
	// PROOF file are linked BY NAME and verified end-to-end through the kernel
	// (`covalence-web-kernel`'s `check_haskell_proofs`, backed by NativeHol via the
	// abstract Hol / Nat trait replayer). Each theorem is reported proved ✓, an
	// unproven hole ○, an axiom, or a rejected proof ✗.
	//
	//   theorem module + S-expr proof  ==(link by name, replay)==>  kernel Thm  ==(α-check)==>  ✓ / ✗
	//
	import { onMount } from 'svelte';
	import seed from '$lib/proofExamples.json';

	let moduleSrc = $state((seed.module as string).replace(/\n$/, ''));
	let proofSrc = $state((seed.proof as string).replace(/\n$/, ''));
	// The wasm-bindgen module (loaded on mount); `any` to avoid import-type churn.
	let wasm = $state<any>(null);
	let loadError = $state('');

	type Outcome = 'proved' | 'axiom' | 'hole' | 'mismatch';
	type Entry = { name: string; statement: string; outcome: Outcome; detail: string };
	type Report =
		| { ok: true; results: Entry[]; pending?: boolean; error?: string }
		| { ok: false; error: string; results?: never; pending?: boolean };

	// Live check: recomputed whenever either editor (or `wasm`) changes.
	let report = $derived.by((): Report & { pending: boolean } => {
		if (!wasm) return { ok: true, results: [], pending: true };
		try {
			const r = JSON.parse(wasm.check_haskell_proofs(moduleSrc, proofSrc));
			if (r.ok) return { ok: true, results: r.results ?? [], pending: false };
			return { ok: false, error: r.error ?? 'unknown error', pending: false };
		} catch (e) {
			return { ok: false, error: String(e), pending: false };
		}
	});

	// A one-line summary of the per-theorem outcomes.
	let summary = $derived.by(() => {
		if (!report.ok || report.pending) return '';
		const n = { proved: 0, axiom: 0, hole: 0, mismatch: 0 } as Record<Outcome, number>;
		for (const e of report.results) n[e.outcome]++;
		const parts: string[] = [];
		if (n.proved) parts.push(`${n.proved} proved`);
		if (n.axiom) parts.push(`${n.axiom} axiom`);
		if (n.hole) parts.push(`${n.hole} hole${n.hole === 1 ? '' : 's'}`);
		if (n.mismatch) parts.push(`${n.mismatch} rejected`);
		return parts.join(' · ') || 'no theorems';
	});

	const badge: Record<Outcome, string> = {
		proved: '✓',
		axiom: '◆',
		hole: '○',
		mismatch: '✗'
	};

	onMount(async () => {
		try {
			const mod = await import('$lib/kernel/covalence_web_kernel.js');
			const wasmUrl = (await import('$lib/kernel/covalence_web_kernel_bg.wasm?url')).default;
			await mod.default({ module_or_path: wasmUrl });
			wasm = mod;
		} catch (e) {
			loadError = String(e);
		}
	});
</script>

<svelte:head><title>proof checker — covalence</title></svelte:head>

<main>
	<h1>proof checker</h1>
	<p class="sub">
		A dialect <strong>theorem module</strong> and a separate
		<strong>S-expression proof file</strong>, linked <strong>by name</strong> and
		verified <strong>end-to-end through the kernel</strong>. Each theorem's
		statement is an equation lowered to a HOL proposition; its proof is replayed
		through the abstract <code>Hol</code> / <code>Nat</code> inference rules to
		build a real <code>Thm</code>, whose conclusion is checked against the
		statement. Runs live in your browser via WASM
		(<code>check_haskell_proofs</code>).
	</p>

	<div class="pipeline">
		<span class="stage">theorem module<br /><em>(equation statements)</em></span>
		<span class="arrow">+</span>
		<span class="stage">S-expr proof<br /><em>(linked by name)</em></span>
		<span class="arrow">→</span>
		<span class="stage">replay via Hol/Nat rules</span>
		<span class="arrow">→</span>
		<span class="stage muted">kernel <code>Thm</code><br /><em>α-checked vs statement</em></span>
	</div>

	<div class="panes">
		<section class="pane">
			<header>theorem module <span class="tag">editable</span></header>
			<textarea class="src" bind:value={moduleSrc} spellcheck="false"></textarea>
		</section>
		<section class="pane">
			<header>proof file <span class="tag">editable</span></header>
			<textarea class="src" bind:value={proofSrc} spellcheck="false"></textarea>
		</section>
	</div>

	<section class="report">
		<header>
			<span>result</span>
			{#if report.pending && !loadError}<span class="tag">compiling to WASM…</span>
			{:else if report.ok}<span class="tag ok">{summary}</span>{/if}
		</header>

		{#if loadError}
			<pre class="err">failed to load wasm: {loadError}</pre>
		{:else if report.pending}
			<pre class="muted">loading the kernel…</pre>
		{:else if !report.ok}
			<pre class="err">{report.error}</pre>
		{:else if report.results.length === 0}
			<pre class="muted">no theorems declared</pre>
		{:else}
			<ul class="results">
				{#each report.results as r}
					<li class={r.outcome}>
						<span class="badge" title={r.outcome}>{badge[r.outcome]}</span>
						<div class="body">
							<div class="line">
								<code class="name">{r.name}</code>
								<span class="kind">{r.outcome}</span>
							</div>
							{#if r.statement}<pre class="statement">{r.statement}</pre>{/if}
							<pre class="detail">{r.detail}</pre>
						</div>
					</li>
				{/each}
			</ul>
		{/if}
	</section>

	<p class="status">
		<strong>Status:</strong> live — parsed, lowered, replayed and
		<strong>proof-checked in your browser</strong>, in the kernel. The proof
		format is backend-decoupled: it names no kernel type except through the
		<code>Hol</code> / <code>Nat</code> traits, so a produced <code>Thm</code> is
		sound by construction and the linker's only remaining check is that the
		conclusion α-equals the lowered statement. Try editing a proof step to see it
		rejected (✗), or delete a proof to see the theorem become a hole (○).
	</p>
</main>

<style>
	main {
		max-width: 60rem;
		margin: 1.5rem auto;
		padding: 0 1rem 3rem;
		font-family: var(--font-mono);
		color: var(--fg);
	}
	h1 {
		font-size: 1.4rem;
	}
	.sub {
		color: var(--muted);
		font-size: 0.85rem;
		line-height: 1.5;
		margin: 0.4rem 0 1rem;
	}
	code {
		background: var(--surface);
		border: 1px solid var(--border);
		border-radius: 3px;
		padding: 0 3px;
		font-size: 0.85em;
	}
	.pipeline {
		display: flex;
		flex-wrap: wrap;
		align-items: center;
		gap: 0.5rem;
		margin: 1rem 0;
	}
	.pipeline .stage {
		border: 1px solid var(--border);
		border-radius: 6px;
		padding: 0.4rem 0.7rem;
		background: var(--surface);
		font-size: 0.8rem;
		text-align: center;
	}
	.pipeline .stage.muted {
		color: var(--muted);
	}
	.pipeline .stage em {
		font-size: 0.72rem;
		opacity: 0.75;
	}
	.pipeline .stage code {
		border: 0;
		background: transparent;
		padding: 0;
	}
	.pipeline .arrow {
		color: var(--accent);
	}
	.panes {
		display: grid;
		grid-template-columns: 1fr 1fr;
		gap: 0.75rem;
		align-items: stretch;
	}
	.pane {
		border: 1px solid var(--border);
		border-radius: 8px;
		overflow: hidden;
		background: var(--surface);
		display: flex;
		flex-direction: column;
	}
	.pane header {
		font-size: 0.72rem;
		text-transform: uppercase;
		letter-spacing: 0.04em;
		color: var(--muted);
		padding: 0.4rem 0.7rem;
		border-bottom: 1px solid var(--border);
		display: flex;
		justify-content: space-between;
	}
	.pane header .tag {
		color: var(--accent);
	}
	.pane textarea {
		padding: 0.7rem;
		font-size: 0.85rem;
		line-height: 1.5;
		flex: 1;
		margin: 0;
		resize: vertical;
		min-height: 11rem;
		font-family: var(--font-mono);
		color: var(--fg);
		background: transparent;
		border: 0;
		outline: none;
		white-space: pre;
	}
	.report {
		margin-top: 0.75rem;
		border: 1px solid var(--border);
		border-radius: 8px;
		background: var(--surface);
		overflow: hidden;
	}
	.report header {
		font-size: 0.72rem;
		text-transform: uppercase;
		letter-spacing: 0.04em;
		color: var(--muted);
		padding: 0.4rem 0.7rem;
		border-bottom: 1px solid var(--border);
		display: flex;
		justify-content: space-between;
		gap: 0.5rem;
	}
	.report header .tag {
		text-transform: none;
		letter-spacing: 0;
		color: var(--accent);
	}
	.report header .tag.ok {
		color: var(--muted);
	}
	.report pre.muted {
		color: var(--muted);
		padding: 0.7rem;
		margin: 0;
		font-size: 0.85rem;
	}
	.report pre.err {
		color: color-mix(in srgb, #e5484d 70%, var(--fg));
		padding: 0.7rem;
		margin: 0;
		font-size: 0.85rem;
		white-space: pre-wrap;
		word-break: break-word;
	}
	.results {
		list-style: none;
		margin: 0;
		padding: 0;
	}
	.results li {
		display: flex;
		gap: 0.6rem;
		padding: 0.6rem 0.7rem;
		border-bottom: 1px solid var(--border);
	}
	.results li:last-child {
		border-bottom: 0;
	}
	.results .badge {
		flex: none;
		width: 1.4rem;
		height: 1.4rem;
		display: grid;
		place-items: center;
		border-radius: 4px;
		font-weight: 700;
		font-size: 0.9rem;
	}
	.results li.proved .badge {
		color: #30a46c;
		background: color-mix(in srgb, #30a46c 16%, transparent);
	}
	.results li.mismatch .badge {
		color: #e5484d;
		background: color-mix(in srgb, #e5484d 16%, transparent);
	}
	.results li.hole .badge {
		color: var(--accent);
		background: color-mix(in srgb, var(--accent) 16%, transparent);
	}
	.results li.axiom .badge {
		color: var(--muted);
		background: color-mix(in srgb, var(--fg) 10%, transparent);
	}
	.results .body {
		min-width: 0;
		flex: 1;
	}
	.results .line {
		display: flex;
		align-items: baseline;
		gap: 0.5rem;
	}
	.results .name {
		border: 0;
		background: transparent;
		padding: 0;
		font-size: 0.85rem;
		color: var(--fg);
	}
	.results .kind {
		font-size: 0.68rem;
		text-transform: uppercase;
		letter-spacing: 0.04em;
		color: var(--muted);
	}
	.results .statement {
		margin: 0.25rem 0 0;
		font-size: 0.8rem;
		color: color-mix(in srgb, var(--accent) 55%, var(--fg));
		white-space: pre-wrap;
		word-break: break-word;
	}
	.results .detail {
		margin: 0.2rem 0 0;
		font-size: 0.78rem;
		color: var(--muted);
		white-space: pre-wrap;
		word-break: break-word;
	}
	.results li.mismatch .detail {
		color: color-mix(in srgb, #e5484d 55%, var(--fg));
	}
	.status {
		margin-top: 1.25rem;
		font-size: 0.8rem;
		color: var(--muted);
		line-height: 1.5;
	}
	@media (max-width: 640px) {
		.panes {
			grid-template-columns: 1fr;
		}
	}
</style>
