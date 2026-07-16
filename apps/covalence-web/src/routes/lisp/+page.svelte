<script lang="ts">
	// LISP REPL — connects to the RUNNING SERVER (POST /api/lisp), which evaluates
	// each cell on the NATIVE kernel in a persistent per-tab session (`defun`s
	// accumulate). No client-side WASM. Every printed value is read off a genuine
	// kernel theorem (`⊢ program = value`); hover a cell to see it (via `#show`).
	import Repl from '$lib/Repl.svelte';
	import { serverRepl } from '$lib/serverRepl';
	import allExamples from '$lib/lispExamples.json';
	import { DEFAULT_LANG, dialectAfter, dialectsOf } from '$lib/lispDialect';

	// A persistent per-tab session on the native kernel; `show` enables the
	// hover-for-`⊢`-theorem affordance (`#show`).
	const server = serverRepl('/api/lisp', { show: true });
	const showCell = server.showCell;

	// The current dialect, mirrored client-side by observing evaluated cells:
	// a `#lang X` cell that returns ok switches it; reset restores the default.
	let dialect = $state(DEFAULT_LANG);

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

	// Dialect tabs (each an honest `#lang` cell, run through the transcript so
	// the reset-on-switch is visible) followed by ONLY the current dialect's
	// examples — a differently-dialected example can never be clicked into the
	// wrong session.
	const dialects = dialectsOf(allExamples);
	const examples = $derived([
		...dialects.map((l) => ({ title: `#lang ${l}`, src: `#lang ${l}`, active: l === dialect })),
		...allExamples.filter((e) => e.lang === dialect)
	]);
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
			(<code>lat?</code>, the metacircular <code>eval</code>) <em>and</em>
			<strong>integers</strong> (<code>+ - * &lt;= =</code>, kernel-proved) — so
			<code>len</code> mixes both. User definitions ride along as <em>hypotheses</em> —
			<code>definitions ⊢ program = value</code>. Limits: <code>defun</code> parameters are
			always list-valued (an <em>int-typed parameter</em> won't compile), and an integer
			can't be placed inside a list.
		</li>
		<li>
			<code>#lang sector</code> — pure McCarthy Lisp (no integers); <code>(+ 2 2)</code> is
			stuck, showing <code>sector ⊑ sector+int</code>.
		</li>
		<li>
			<code>#lang acl2</code> — an ACL2 slice over the value semantics:
			<code>defun</code> is admitted only if syntactically <em>structurally recursive</em>
			(a check, not a termination proof), and <code>defthm</code> proves
			<strong>ground goals only</strong>. A ground <code>(equal L R)</code> over quoted data,
			integer literals, and <code>car</code>/<code>cdr</code>/<code>cons</code>/<code>consp</code>/<code>equal</code>/<code>+</code>
			is proved via a <em>reified <code>Derivable_ACL2</code> certificate</em> plus a
			machine-checked <em>soundness metatheorem</em> — the stored theorem is the transported
			base-HOL model equation (<code>#show NAME</code> reveals it); other ground goals are
			driven to a bool literal by certified reduction. Goals with free variables are honestly
			rejected — <em>induction is not implemented</em>. ACL2 spellings: <code>equal</code>,
			ternary <code>if</code> (no <code>cond</code>),
			<code>consp</code>/<code>atom</code>/<code>endp</code>, <code>zp</code>/<code>natp</code>.
		</li>
	</ul>
	<p class="muted">
		<code>defun</code>s (and in <code>acl2</code>, <code>defthm</code>s) persist across cells
		(a per-tab server session). The relational dialects (<code>lisp</code>/<code>sector</code>)
		have no <code>defun</code> recursion yet — use <code>scheme</code> or <code>acl2</code> for
		that. Other directives: <code>#show EXPR</code>, <code>#help</code>.
	</p>
	<p>
		<strong>Examples</strong> — the buttons above the prompt: dialect tabs first (each an
		honest <code>#lang</code> cell — switching resets the session), then the current
		dialect's examples. All of them:
	</p>
	<ul class="examples-list">
		{#each allExamples as ex}
			<li>
				<span class="ex-lang">[{ex.lang}]</span> <span class="ex-title">{ex.title}</span> —
				<code>{ex.src}</code>
			</li>
		{/each}
	</ul>
{/snippet}

<main>
	<h1>lisp <span class="tag">type <code>#help</code> for docs</span></h1>
	<Repl {evalCell} {showCell} {onReset} {help} {examples} />
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
	:global(.widget .ex-lang) {
		color: var(--accent);
		font-size: 0.85em;
	}
</style>
