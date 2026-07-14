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
		read off a genuine kernel theorem. <strong>Hover a result</strong> to see its proof.
	</p>
	<p>
		<strong>Dialects</strong> — switch with <code>#lang &lt;name&gt;</code> (resets the
		session):
	</p>
	<ul>
		<li>
			<code>#lang lisp</code> <em>(default)</em> — primitives + <strong>integers</strong>
			(<code>+ - * &lt;= =</code>), run through the <em>reduction relation</em>: every value
			is a <code>⊢ Reduces&nbsp;input&nbsp;value</code> theorem. Try <code>(+ 2 2)</code>.
		</li>
		<li>
			<code>#lang scheme</code> — the equational value semantics with
			<code>cond</code>/<code>lambda</code>/<code>defun</code> <strong>recursion</strong>
			(<code>lat?</code>, the metacircular <code>eval</code>). No integers here (yet). User
			definitions ride along as <em>hypotheses</em> — <code>definitions ⊢ program = value</code>.
		</li>
		<li>
			<code>#lang sector</code> — pure McCarthy Lisp (no integers); <code>(+ 2 2)</code> is
			stuck, showing <code>sector ⊑ sector+int</code>.
		</li>
	</ul>
	<p class="muted">
		<code>defun</code>s persist across cells (a per-tab server session). Integers are the
		default dialect; recursion + integers together (full Scheme in one dialect) is the next
		step. Other directives: <code>#show EXPR</code>, <code>#help</code>.
	</p>
	<p><strong>Examples</strong> — the buttons above the prompt, in order:</p>
	<ul class="examples-list">
		{#each examples as ex}
			<li><span class="ex-title">{ex.title}</span> — <code>{ex.src}</code></li>
		{/each}
	</ul>
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
	:global(.widget p) {
		margin: 0 0 0.5rem;
	}
	:global(.widget ul) {
		margin: 0 0 0.6rem;
		padding-left: 1.2rem;
	}
	:global(.widget li) {
		margin: 0.3rem 0;
	}
	:global(.widget .examples-list code) {
		white-space: pre-wrap;
		overflow-wrap: anywhere;
	}
	:global(.widget .ex-title) {
		color: var(--muted);
	}
</style>
