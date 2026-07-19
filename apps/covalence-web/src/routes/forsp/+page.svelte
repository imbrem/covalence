<script lang="ts">
	// FORSP REPL — connects to the RUNNING SERVER (POST /api/forsp), a native
	// persistent per-tab session ($x bindings + word defs accumulate). No WASM.
	import Repl from '$lib/Repl.svelte';
	import { serverRepl } from '$lib/serverRepl';
	import { HealthPoll } from '$lib/repl/health.svelte';
	import { highlight as hl } from '$lib/repl/sexpr';
	import examples from '$lib/forspExamples.json';

	const { evalCell, onReset } = serverRepl('/api/forsp');

	const health = new HealthPoll();
	$effect(() => {
		health.start();
		return () => health.stop();
	});

	// Forsp is concatenative, not S-expression-shaped, but the lexical shapes
	// (parens for thunks, `$x`/`^x`, `'a` quotes, `;` comments) are the same —
	// so the shared tokenizer applies with an empty keyword set.
	const FORSP_KEYWORDS: ReadonlySet<string> = new Set([
		'cons', 'car', 'cdr', 'eq', 'force', 'swap', 'cswap', 'stack', 'print'
	]);
	const highlight = (text: string) => hl(text, FORSP_KEYWORDS, { hashLinks: false });
</script>

<svelte:head><title>forsp — covalence</title></svelte:head>

{#snippet help(run: (src: string) => Promise<void>)}
	<p>
		<strong>covalence-forsp</strong> is a tiny <strong>concatenative</strong> language — a
		Forth/Lisp hybrid (after xorvoid's Forsp) with a stack, an environment, and
		call-by-push-value. Each cell runs on the running server; the result shown is the
		<strong>top of the stack</strong>. <code>$x</code> bindings and word definitions persist
		across cells.
	</p>
	<p class="muted">
		Unlike <a href="/lisp">/lisp</a>, Forsp values are <em>not yet</em> kernel-theorem backed —
		it has a small-step reduction relation (<code>covalence-forsp</code>'s
		<code>Semantics</code>) arranged so a kernel-backed Forsp theory can drop in later. So there
		is no hover-for-proof here.
	</p>
	<p><strong>Examples</strong> — click to run:</p>
	<div class="row examples">
		{#each examples as ex}
			<button data-testid="example-button" title={ex.src} onclick={() => run(ex.src)}>
				{ex.title}
			</button>
		{/each}
	</div>
	<p class="muted">Directives: <code>#help</code>, <code>#reset</code> (clears the session).</p>
{/snippet}

{#snippet status()}
	<span
		class="health-dot"
		class:healthy={health.healthy}
		title={health.healthy ? 'API connected' : 'API unreachable'}
	></span>
	<span class="status-text">
		{health.healthy ? 'forsp session on cov serve' : 'API unreachable'}
	</span>
{/snippet}

<Repl
	{evalCell}
	{onReset}
	{help}
	{status}
	{highlight}
	storeKey="/api/forsp"
	prompt="forsp>"
	placeholder="type a program, press Enter — #help for docs and examples"
/>

<style>
	.health-dot {
		width: 8px;
		height: 8px;
		border-radius: 50%;
		background: #f87171;
		box-shadow: 0 0 4px #f8717166;
		flex-shrink: 0;
	}
	.health-dot.healthy {
		background: #4ade80;
		box-shadow: 0 0 4px #4ade8066;
	}
	.status-text {
		font-size: 0.75rem;
		color: var(--muted);
	}
	:global(.widget p) {
		margin: 0 0 0.5rem;
	}
	:global(.widget .muted) {
		color: var(--muted);
	}
	:global(.widget a) {
		color: var(--accent);
	}
	:global(.widget .row) {
		display: flex;
		flex-wrap: wrap;
		align-items: center;
		gap: 0.35rem;
	}
	:global(.widget .row.examples) {
		margin: 0 0 0.5rem;
	}
</style>
