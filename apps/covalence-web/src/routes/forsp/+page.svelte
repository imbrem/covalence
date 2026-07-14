<script lang="ts">
	// FORSP REPL — connects to the RUNNING SERVER (POST /api/forsp), a native
	// persistent per-tab session ($x bindings + word defs accumulate). No WASM.
	import Repl from '$lib/Repl.svelte';
	import { serverRepl } from '$lib/serverRepl';
	import examples from '$lib/forspExamples.json';

	const { evalCell, onReset } = serverRepl('/api/forsp');
</script>

<svelte:head><title>forsp — covalence</title></svelte:head>

<main>
	<h1>forsp</h1>
	<p class="sub">
		<code>covalence-forsp</code> is a tiny <strong>concatenative</strong> language —
		a Forth/Lisp hybrid (after xorvoid's Forsp) with a stack, an environment, and
		call-by-push-value. This REPL runs it on the running server; the result shown is the
		top of the stack. A real REPL: <code>$x</code> bindings and word definitions persist
		across cells.
	</p>
	<p class="sub note">
		Unlike <a href="/lisp">/lisp</a>, Forsp values are <em>not yet</em> kernel-theorem
		backed — it has a small-step reduction relation (<code>covalence-forsp</code>'s
		<code>Semantics</code>) arranged so a kernel-backed Forsp theory can drop in later.
	</p>

	<Repl {evalCell} {onReset} examples={examples as any} prompt="forsp>" />
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
		line-height: 1.55;
		margin: 0.4rem 0 0.8rem;
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
