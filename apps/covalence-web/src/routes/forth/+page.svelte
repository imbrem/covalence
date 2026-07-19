<script lang="ts">
	// FORTH page — PLACEHOLDER, deliberately. The /forth route and the
	// `forth_eval_cell` wasm seam exist; the evaluator does not.
	//
	// WHY NOT A REPL: `Repl.svelte` + `ReplShell` would drop in here in a few
	// lines, but `forth_eval_cell` rejects EVERY input with the fixed string
	// "forth: coming soon". A prompt that accepts typing and then refuses 100% of
	// it is a fake affordance: it costs the reader time to discover what this
	// page states in one sentence, and its error text carries strictly less
	// information than the prose does. The moment the seam can evaluate even one
	// word, this page should become a real `Repl` — see /forsp and /lisp for the
	// shape it will take.
	//
	// What the page DOES do is call the seam once and print the verbatim reply,
	// so the claim "the seam exists and is not implemented" is demonstrated
	// rather than asserted.
	//
	// SKELETON(cov:web.forth-evaluator, major): `forth_eval_cell` is a stub that
	// always errors; no small-step Forth reduction relation or in-kernel Forth
	// theory exists yet.
	import '$lib/kernelPages.css';
	import { useKernel } from '$lib/kernelState.svelte';

	const PROBE = '1 2 +';
	const k = useKernel();

	// The seam's actual reply, verbatim — never paraphrased.
	let seam = $derived.by(() => {
		if (!k.kernel) return null;
		try {
			return k.kernel.forth_eval_cell(PROBE);
		} catch (e) {
			return String(e);
		}
	});
</script>

<svelte:head><title>forth — covalence</title></svelte:head>

<main class="demo-page">
	<h1>forth <span class="badge">not implemented</span></h1>
	<p class="sub">
		A <strong>Forth</strong> REPL is planned as the third stack-language demo, alongside
		<a href="/forsp">/forsp</a> and <a href="/lisp">/lisp</a>. The route and the
		<code>forth_eval_cell</code> WASM seam already exist; what's left is the evaluator —
		a small-step Forth reduction relation over the shared <code>covalence-repl-core</code>
		<code>Semantics</code> traits, and eventually an in-kernel Forth theory so its words
		are backed by theorems (as with <a href="/lisp">/lisp</a>).
	</p>
	<p class="sub">
		Forth is the concatenative dual of Lisp: a word is a stack transformer, and
		composition is sequencing — the same <code>compose</code> that threads a parser's
		remaining input. It's also the natural toy model for the WASM-executor axis (WASM is
		a stack machine).
	</p>

	<section class="pane">
		<header>
			the seam, called for real
			<span class="tag quiet">forth_eval_cell({JSON.stringify(PROBE)})</span>
		</header>
		{#if k.error}
			<pre class="err">failed to load wasm: {k.error}</pre>
		{:else if seam === null}
			<pre class="muted">loading the kernel…</pre>
		{:else}
			<pre class="seam" data-testid="forth-seam">{seam}</pre>
		{/if}
	</section>

	<p class="status">
		<strong>Status:</strong> the route and the WASM export are wired end-to-end — the reply
		above came out of <code>covalence-web-kernel</code> just now. There is no evaluator
		behind it yet, so there is deliberately no prompt to type into: a REPL that rejects
		every input would tell you less than this page already does.
	</p>
</main>

<style>
	.badge {
		font-size: 0.7rem;
		color: var(--muted);
		border: 1px solid var(--border);
		border-radius: 5px;
		padding: 0.1rem 0.4rem;
		vertical-align: middle;
	}
	.pane .seam {
		color: color-mix(in srgb, var(--err) 55%, var(--fg));
		font-size: 0.8rem;
	}
</style>
