<script module lang="ts">
	import { DEFAULT_LANG } from '$lib/lispDialect';

	// The current dialect, mirrored client-side by observing evaluated cells: a
	// `#lang X` cell that returns ok switches it; reset restores the default.
	// MODULE-level, like the transcript and the session it describes — a remount
	// that reset this to `lisp` would print a prompt the session doesn't agree
	// with.
	let dialect = $state(DEFAULT_LANG);
</script>

<script lang="ts">
	// LISP REPL — connects to the RUNNING SERVER (POST /api/lisp), which evaluates
	// each cell on the NATIVE kernel in a persistent per-tab session (`defun`s
	// accumulate). No client-side WASM. Every printed value is read off a genuine
	// kernel theorem (`⊢ program = value`); hover a cell to see it (via `#show`).
	import Repl from '$lib/Repl.svelte';
	import { serverRepl } from '$lib/serverRepl';
	import { HealthPoll } from '$lib/repl/health.svelte';
	import { LISP_KEYWORDS, LISP_SPECIAL_FORMS, highlight as hl } from '$lib/repl/sexpr';
	import allExamples from '$lib/lispExamples.json';
	import { dialectAfter, dialectsOf } from '$lib/lispDialect';

	// A persistent per-tab session on the native kernel; `show` enables the
	// hover-for-`⊢`-theorem affordance (`#show`).
	const server = serverRepl('/api/lisp', { show: true });
	const showCell = server.showCell;

	async function evalCell(src: string) {
		const r = await server.evalCell(src);
		const next = dialectAfter(src, r.ok, r.result);
		if (next) dialect = next;
		return r;
	}

	function onReset() {
		dialect = DEFAULT_LANG;
		server.onReset();
	}

	const health = new HealthPoll();
	$effect(() => {
		health.start();
		return () => health.stop();
	});

	const highlight = (text: string) => hl(text, LISP_KEYWORDS, { hashLinks: false });

	const dialects = dialectsOf(allExamples);
	const examplesOf = (lang: string) => allExamples.filter((e) => e.lang === lang);

	// One-line summaries for the dialect tabs; the details are in the prose
	// below each one.
	const BLURB: Record<string, string> = {
		lisp: 'primitives + integers, through the reduction relation',
		scheme: 'equational value semantics with recursion and integers',
		sector: 'pure McCarthy Lisp — no integers',
		acl2: 'an ACL2 slice: admissibility-checked defun, ground defthm'
	};

	/**
	 * Run an example honestly: a foreign-dialect example switches dialect FIRST,
	 * as a visible `#lang` cell in the transcript (the server resets the session
	 * on a switch, and hiding that would misrepresent what just happened).
	 */
	async function runExample(run: (src: string) => Promise<void>, lang: string, src: string) {
		if (lang !== dialect) await run(`#lang ${lang}`);
		await run(src);
	}
</script>

<svelte:head><title>lisp — covalence</title></svelte:head>

<!-- The docs live in a `#help` widget rendered inline in the REPL. Every button
     in here runs a real cell through the transcript — there is no privileged
     path that evaluates something the user can't type. -->
{#snippet help(run: (src: string) => Promise<void>)}
	<p>
		<strong>covalence-lisp</strong> — a small, kernel-backed Lisp. Each cell is evaluated on the
		<strong>native kernel</strong> (via <code>cov serve</code>); every printed value is read off
		a genuine kernel theorem. <strong>Hover a result</strong> to see its proof.
	</p>
	<p>
		<strong>Dialects</strong> — click a tab to switch (a <code>#lang</code> cell, which
		<em>resets the session</em>), or a form to run it:
	</p>
	<ul class="dialects">
		{#each dialects as lang}
			<li>
				<div class="row">
					<button
						class:active={lang === dialect}
						data-testid="example-button"
						onclick={() => run(`#lang ${lang}`)}>#lang {lang}</button
					>
					<span class="blurb">{BLURB[lang] ?? ''}</span>
				</div>
				<div class="row examples">
					{#each examplesOf(lang) as ex}
						<button data-testid="example-button" title={ex.src} onclick={() => runExample(run, lang, ex.src)}>
							{ex.title}
						</button>
					{/each}
				</div>
			</li>
		{/each}
	</ul>
	<p>
		<code>lisp</code> runs the <em>reduction relation</em> — every value is a
		<code>⊢ Reduces&nbsp;input&nbsp;value</code> theorem. <code>scheme</code> adds
		<code>cond</code>/<code>lambda</code>/<code>defun</code> <strong>recursion</strong>; user
		definitions ride along as <em>hypotheses</em> (<code>definitions ⊢ program = value</code>),
		<code>defun</code> parameters are always list-valued, and an integer can't sit inside a
		list. <code>sector</code> drops integers entirely, so <code>(+ 2 2)</code> is stuck —
		showing <code>sector ⊑ sector+int</code>.
	</p>
	<p>
		<code>acl2</code> admits a <code>defun</code> only if it is syntactically
		<em>structurally recursive</em> (a check, not a termination proof), and <code>defthm</code>
		proves <strong>ground goals only</strong>: a ground <code>(equal L R)</code> over quoted
		data, integer literals and
		<code>car</code>/<code>cdr</code>/<code>cons</code>/<code>consp</code>/<code>equal</code>/<code>+</code>
		is proved via a <em>reified <code>Derivable_ACL2</code> certificate</em> plus a
		machine-checked <em>soundness metatheorem</em> — the stored theorem is the transported
		base-HOL model equation (<code>#show NAME</code> reveals it). Goals with free variables are
		honestly rejected: <em>induction is not implemented</em>.
	</p>
	<p class="muted">
		Directives: <code>#lang NAME</code>, <code>#show EXPR</code>, <code>#help</code>,
		<code>#reset</code> (clears this transcript and the session), and in <code>acl2</code>
		<code>#book PATH</code> — runs a <code>.lisp</code> book of events and prints an honest
		per-event tally. Book paths resolve on the <em>server</em>, confined to its working
		directory (e.g. <code>#book crates/lang/lisp/tests/books/app-basics</code>).
		<code>defun</code>s and <code>defthm</code>s persist across cells; each cell is exactly one
		S-expression.
	</p>
{/snippet}

{#snippet status()}
	<span
		class="health-dot"
		class:healthy={health.healthy}
		title={health.healthy ? 'API connected' : 'API unreachable'}
	></span>
	<span class="status-text">
		{health.healthy ? 'kernel session on cov serve' : 'API unreachable'} &mdash; #lang {dialect}
	</span>
{/snippet}

<Repl
	{evalCell}
	{showCell}
	{onReset}
	{help}
	{status}
	{highlight}
	specialForms={LISP_SPECIAL_FORMS}
	storeKey="/api/lisp"
	prompt="{dialect}>"
	placeholder="type a form, press Enter — #help for docs and examples"
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
	/* The help widget is rendered inside `<Repl>`, so its innards need `:global`
	   (the chip/button styling itself lives with the widget, in Repl.svelte). */
	:global(.widget p) {
		margin: 0 0 0.5rem;
	}
	:global(.widget .muted) {
		color: var(--muted);
	}
	:global(.widget ul.dialects) {
		list-style: none;
		margin: 0 0 0.6rem;
		padding: 0;
	}
	:global(.widget ul.dialects li) {
		margin: 0 0 0.5rem;
	}
	:global(.widget .row) {
		display: flex;
		flex-wrap: wrap;
		align-items: center;
		gap: 0.35rem;
	}
	:global(.widget .row.examples) {
		margin: 0.25rem 0 0 1rem;
	}
	:global(.widget .blurb) {
		color: var(--muted);
		font-size: 0.9em;
	}
</style>
