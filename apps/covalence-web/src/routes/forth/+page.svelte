<script lang="ts">
	// FORTH page — PLACEHOLDER. The /forth route + the `forth_eval_cell` wasm
	// seam exist; the evaluator itself is future work (a small-step Forth
	// reduction relation + an in-kernel Forth theory, mirroring forsp/lisp).
</script>

<svelte:head><title>forth — covalence</title></svelte:head>

<main>
	<h1>forth <span class="badge">coming soon</span></h1>
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
	.badge {
		font-size: 0.7rem;
		color: var(--muted);
		border: 1px solid var(--border);
		border-radius: 5px;
		padding: 0.1rem 0.4rem;
		vertical-align: middle;
	}
	.sub {
		color: var(--muted);
		font-size: 0.85rem;
		line-height: 1.55;
		margin: 0.6rem 0;
	}
	.sub a {
		color: var(--accent);
	}
	code {
		background: var(--surface);
		border: 1px solid var(--border);
		border-radius: 3px;
		padding: 0 3px;
		font-size: 0.85em;
	}
</style>
