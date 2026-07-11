<script lang="ts">
	// HASKELL FRONTEND page. The `covalence-haskell` crate (crates/lang/haskell)
	// is a kernel-agnostic surface: a hand-written parser for a small Haskell
	// EXPRESSION dialect + top-level defs, ONE canonical lowering to an
	// S-expression interchange IR, and a pluggable `Realize` backend.
	//
	//   Haskell dialect  ==(one canonical lowering)==>  S-expressions  ==(pluggable)==>  backend
	//
	// The examples below are PRECOMPUTED: each `src -> sexpr` pair is the real
	// output of running the crate's parse + `expr_to_sexpr` / `module_to_text`
	// pipeline (generated from the crate, not hand-written). Wiring a *live*
	// in-browser parse (compile `covalence-haskell` to wasm-bindgen the way
	// `covalence-web-kernel` is built for the article page) is the recorded
	// follow-on — see crates/lang/haskell/SKELETONS.md.
	import examples from '$lib/haskellExamples.json';

	type Example = { title: string; kind: string; src: string; sexpr: string };
	const cases = examples as Example[];

	let selected = $state(0);
	let current = $derived(cases[selected]);
</script>

<svelte:head><title>haskell frontend — covalence</title></svelte:head>

<main>
	<h1>haskell frontend</h1>
	<p class="sub">
		<code>covalence-haskell</code> (<code>crates/lang/haskell</code>) is a
		kernel-agnostic on-ramp: a small Haskell dialect lowered through ONE
		canonical desugaring into an S-expression interchange IR, then realized by
		a pluggable backend.
	</p>

	<div class="pipeline">
		<span class="stage">Haskell dialect</span>
		<span class="arrow">→</span>
		<span class="stage">canonical lowering</span>
		<span class="arrow">→</span>
		<span class="stage">S-expression IR</span>
		<span class="arrow">→</span>
		<span class="stage muted">Realize backend<br /><em>(Text · Peano · HOL kernel term)</em></span>
	</div>

	<p class="note">
		The <strong>S-expression IR</strong> is the interchange point: third-party
		producers/consumers use it directly (text in / canonical text out) and
		never touch Haskell syntax. The <code>hol</code> feature realizes the same
		IR into carved <code>sexpr</code> kernel <code>Term</code>s.
	</p>

	<div class="examples">
		{#each cases as c, i}
			<button class:on={selected === i} onclick={() => (selected = i)}>{c.title}</button>
		{/each}
	</div>

	<div class="panes">
		<section class="pane">
			<header>Haskell <span class="tag">{current.kind}</span></header>
			<pre class="src">{current.src.replace(/\n$/, '')}</pre>
		</section>
		<div class="mid">→</div>
		<section class="pane">
			<header>S-expression IR</header>
			<pre class="sexpr">{current.sexpr.replace(/\n$/, '')}</pre>
		</section>
	</div>

	<p class="status">
		<strong>Status:</strong> precomputed (real crate output). Live in-browser
		parsing via WASM is the recorded follow-on — see
		<code>crates/lang/haskell/SKELETONS.md</code>.
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
	.sub,
	.note {
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
	.pipeline .arrow {
		color: var(--accent);
	}
	.examples {
		display: flex;
		flex-wrap: wrap;
		gap: 0.35rem;
		margin: 1rem 0;
	}
	button {
		font: inherit;
		font-size: 0.78rem;
		color: var(--muted);
		background: var(--surface);
		border: 1px solid var(--border);
		border-radius: 5px;
		padding: 0.25rem 0.55rem;
		cursor: pointer;
	}
	button:hover {
		color: var(--fg);
	}
	button.on {
		color: var(--fg);
		border-color: var(--accent);
		background: color-mix(in srgb, var(--accent) 18%, transparent);
	}
	.panes {
		display: grid;
		grid-template-columns: 1fr auto 1fr;
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
	.pane pre {
		padding: 0.7rem;
		font-size: 0.85rem;
		white-space: pre-wrap;
		word-break: break-word;
		line-height: 1.5;
		flex: 1;
	}
	.pane .sexpr {
		color: color-mix(in srgb, var(--accent) 55%, var(--fg));
	}
	.mid {
		display: flex;
		align-items: center;
		color: var(--accent);
		font-size: 1.1rem;
	}
	.status {
		margin-top: 1.25rem;
		font-size: 0.8rem;
		color: var(--muted);
	}
	@media (max-width: 640px) {
		.panes {
			grid-template-columns: 1fr;
		}
		.mid {
			justify-content: center;
		}
	}
</style>
