<script lang="ts">
	// LISP REPL — connects to the RUNNING SERVER (POST /api/lisp), which evaluates
	// each cell on the NATIVE kernel in a persistent per-tab session (`defun`s
	// accumulate). No client-side WASM. Every printed value is read off a genuine
	// kernel theorem (`⊢ program = value`); hover a cell to see it (via `#show`).
	import Repl from '$lib/Repl.svelte';
	import { serverRepl } from '$lib/serverRepl';
	import examples from '$lib/lispExamples.json';

	// A persistent per-tab session on the native kernel; `show` enables the
	// hover-for-`⊢`-theorem affordance (`#show`).
	const { evalCell, showCell, onReset } = serverRepl('/api/lisp', { show: true });
</script>

<svelte:head><title>lisp — covalence</title></svelte:head>

<!-- The intro/help lives in a `#help` widget rendered inline in the REPL, so the
     page chrome stays minimal. -->
{#snippet help()}
	<p>
		<strong>covalence-lisp</strong> — a small, kernel-backed Lisp. Each cell is evaluated on
		the <strong>native kernel</strong> (via <code>cov serve</code>); every printed value is
		read off a genuine <code>⊢ program = value</code> theorem. <strong>Hover a result</strong>
		to see its proof.
	</p>
	<p>
		A real REPL — <code>defun</code>s persist across cells (a per-tab server session). Try the
		numbered examples in order: define <code>lat?</code>, then use it; or define the
		<code>★ metacircular eval</code> and run it. User definitions ride along as
		<em>hypotheses</em> (<code>definitions ⊢ program = value</code>), sound even for recursion
		that might not terminate.
	</p>
	<p class="muted">
		Little Schemer ch1 primitives (<code>car cdr cons atom? null? eq?</code>) +
		<code>cond</code>/<code>lambda</code>/<code>defun</code> recursion; the metacircular
		interpreter runs its ground <code>quote/car/cdr/cons</code> fragment.
	</p>
{/snippet}

<main>
	<h1>lisp <span class="tag">type <code>#help</code> for docs</span></h1>
	<Repl {evalCell} {showCell} {onReset} {help} examples={examples as any} />
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
		display: flex;
		align-items: baseline;
		gap: 0.6rem;
	}
	.tag {
		font-size: 0.72rem;
		font-weight: 400;
		color: var(--muted);
	}
	.tag code,
	:global(.widget code) {
		font-size: 0.9em;
	}
	:global(.widget .muted) {
		color: var(--muted);
	}
</style>
