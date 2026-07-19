<script module lang="ts">
	import { DEFAULT_LANG } from '$lib/lispDialect';

	// The dialect the SERVER session is actually in, mirrored client-side by
	// observing evaluated cells. MODULE-level, like the transcript and the
	// session both describe: a remount that reset this to `lisp` would print a
	// prompt the live session doesn't agree with.
	//
	// It starts at the server's default (`lisp`) rather than `acl2` because a
	// fresh session IS in `lisp` until the opening `#lang acl2` cell lands — so
	// that cell is submitted under the `lisp>` prompt, which is the truth.
	let dialect = $state(DEFAULT_LANG);
</script>

<script lang="ts">
	// ACL2 demo — the ACL2 slice of covalence-lisp, on the RUNNING SERVER.
	//
	// There is no ACL2 endpoint: this is POST /api/lisp with a `#lang acl2` cell,
	// and that cell RESETS the server session. So it is never sent behind the
	// user's back — `openAcl2Session` puts it in the transcript as a real,
	// visible first cell with the server's real answer.
	import { untrack } from 'svelte';
	import Repl from '$lib/Repl.svelte';
	import { serverRepl } from '$lib/serverRepl';
	import { HealthPoll } from '$lib/repl/health.svelte';
	import { highlight as hl } from '$lib/repl/sexpr';
	import { transcriptFor } from '$lib/repl/transcripts.svelte';
	import { dialectAfter } from '$lib/lispDialect';
	import {
		ACL2_KEYWORDS,
		ACL2_SPECIAL_FORMS,
		openAcl2Session,
		type Acl2Example,
		type Acl2Group
	} from '$lib/acl2';
	import tour from '$lib/acl2Examples.json';

	/** The transcript store key — distinct from /lisp's, so the two pages keep
	 *  separate histories even though they ride the same endpoint. */
	const STORE_KEY = 'acl2';

	// TODO(cov:web.acl2-session-sharing, minor): `serverRepl` memoizes one session per ENDPOINT, so /acl2 and /lisp share a server session — opening this page resets the one /lisp's transcript describes. Key sessions by store instead.
	const server = serverRepl('/api/lisp', { show: true });
	const showCell = server.showCell;
	const transcript = transcriptFor(STORE_KEY);

	async function evalCell(src: string) {
		const r = await server.evalCell(src);
		const next = dialectAfter(src, r.ok, r.result);
		if (next) dialect = next;
		return r;
	}

	/**
	 * Reset = clear the transcript (done by `<Repl>` before this runs) and
	 * re-open the dialect. The re-opening `#lang acl2` cell IS the server-side
	 * reset, so `server.onReset()` is deliberately NOT also called: both are
	 * fire-and-forget POSTs to the same session, and a reset landing after the
	 * `#lang` would leave the session in `lisp` under an `acl2>` prompt.
	 */
	function onReset() {
		dialect = DEFAULT_LANG;
		void openAcl2Session(transcript, evalCell, `${DEFAULT_LANG}>`);
	}

	// Open the dialect once, on mount. Untracked: the call reads `dialect` and
	// the transcript's own length, and re-running on either would be a loop.
	// `openAcl2Session` is itself guarded (a live transcript means a live
	// session — remounting must not silently reset it).
	$effect(() => {
		untrack(() => void openAcl2Session(transcript, evalCell, `${dialect}>`));
	});

	const health = new HealthPoll();
	$effect(() => {
		health.start();
		return () => health.stop();
	});

	const highlight = (text: string) => hl(text, ACL2_KEYWORDS, { hashLinks: false });

	const GROUPS = tour as Acl2Group[];

	/**
	 * Run a tour example: its cells IN ORDER, each awaited, each a real cell in
	 * the transcript. Sequencing matters — a `defthm` whose goal mentions a
	 * `defun` needs that `defun` admitted first — and awaiting is what makes it
	 * work (`<Repl>`'s `run` ignores a submit while a cell is in flight).
	 */
	async function runExample(run: (src: string) => Promise<void>, ex: Acl2Example) {
		for (const cell of ex.cells) await run(cell);
	}
</script>

<svelte:head><title>acl2 — covalence</title></svelte:head>

<!-- Docs live in the `#help` widget; every button in it runs a real cell through
     the transcript. There is no privileged path that evaluates something the
     user could not type. -->
{#snippet help(run: (src: string) => Promise<void>)}
	<p>
		<strong>The ACL2 slice</strong> of covalence-lisp, evaluated on the native kernel. A guided
		tour — each button runs its cells, in order, as real cells:
	</p>
	<ol class="tour">
		{#each GROUPS as g (g.id)}
			<li>
				<div class="g-title">{g.title}</div>
				<p class="lead">{g.lead}</p>
				<div class="row">
					{#each g.examples as ex (ex.title)}
						<button
							data-testid="example-button"
							title={ex.cells.join('\n')}
							onclick={() => runExample(run, ex)}
						>
							{ex.title}
						</button>
					{/each}
				</div>
				<ul class="notes">
					{#each g.examples.filter((e) => e.note) as ex (ex.title)}
						<li><code>{ex.title}</code> — {ex.note}</li>
					{/each}
				</ul>
			</li>
		{/each}
	</ol>
	<p class="muted">
		Directives: <code>#show NAME</code> (print the stored theorem and which route proved it),
		<code>#book PATH</code> (run a <code>.lisp</code> book and print a per-event tally),
		<code>#lang NAME</code>, <code>#help</code>, <code>#reset</code>. Book paths resolve on the
		<em>server</em>, confined to its working directory. <code>defun</code>s and
		<code>defthm</code>s persist across cells; each cell is exactly one S-expression, and
		<strong>hovering a result</strong> shows the kernel sequent behind it.
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

<div class="acl2-page">
	<!-- The honesty story, always visible but deliberately three lines: the depth
	     belongs in `#help`, not in a wall of text above the prompt. -->
	<header class="lede">
		<h1>acl2</h1>
		<p>
			A <code>defthm</code> stored here is a <strong>transported base-HOL model equation</strong>
			— proved via a reified <code>Derivable_ACL2</code> certificate plus a machine-checked
			soundness metatheorem (or by certified kernel reduction, riding its <code>defun</code>
			equations as hypotheses). <code>#show NAME</code> prints it and says which route it took.
		</p>
		<p class="limits">
			Two hard limits, stated up front: <strong>defun</strong> is admitted by a
			<em>syntactic structural-recursion check</em> — not a termination proof, no measures — and
			<strong>defthm</strong> proves <em>ground goals only</em>. Free-variable goals need
			induction, which this slice does not implement, and are rejected rather than assumed.
		</p>
	</header>

	<Repl
		{evalCell}
		{showCell}
		{onReset}
		{help}
		{status}
		{highlight}
		specialForms={ACL2_SPECIAL_FORMS}
		storeKey={STORE_KEY}
		prompt="{dialect}>"
		placeholder="type a form, press Enter — #help for the guided tour"
	/>
</div>

<style>
	/* `ReplShell` is a `height: 100vh` column. Under the lede it has to give that
	   space back, or the nav + prose + REPL together scroll the whole page. The
	   override is page-scoped (`:global` inside `.acl2-page`), not a shared-file
	   edit — /lisp and /forsp still get the full-viewport shell. */
	.acl2-page {
		display: flex;
		flex-direction: column;
		height: 100%;
		min-height: 0;
	}
	/* `width: 100%` is load-bearing: `.app` carries `margin: 0 auto`, and an auto
	   cross-axis margin on a flex item suppresses the stretch, collapsing the
	   column to fit-content (a ~420px REPL misaligned under the 900px lede). */
	.acl2-page :global(.app) {
		flex: 1;
		width: 100%;
		height: auto;
		min-height: 0;
	}

	.lede {
		max-width: 900px;
		margin: 0 auto;
		padding: 0.9rem 1.5rem 0;
		flex-shrink: 0;
	}
	.lede h1 {
		font-family: var(--font-mono);
		font-size: 0.95rem;
		color: var(--accent);
		margin: 0 0 0.35rem;
		letter-spacing: 0.02em;
	}
	.lede p {
		margin: 0 0 0.35rem;
		font-size: 0.8rem;
		line-height: 1.55;
		color: var(--muted);
	}
	.lede p strong {
		color: var(--fg);
		font-weight: 600;
	}
	.lede .limits {
		padding-left: 0.6rem;
		border-left: 2px solid color-mix(in srgb, #e5484d 55%, transparent);
	}
	.lede code {
		font-family: var(--font-mono);
		font-size: 0.9em;
		background: var(--surface);
		border: 1px solid var(--border);
		border-radius: 3px;
		padding: 0 3px;
	}

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

	/* The help widget renders inside `<Repl>`, so its innards need `:global`
	   (the button/chip styling itself lives with the widget, in Repl.svelte). */
	:global(.widget p) {
		margin: 0 0 0.5rem;
	}
	:global(.widget .muted) {
		color: var(--muted);
	}
	:global(.widget ol.tour) {
		list-style: none;
		margin: 0 0 0.6rem;
		padding: 0;
	}
	:global(.widget ol.tour > li) {
		margin: 0 0 0.75rem;
		padding-left: 0.6rem;
		border-left: 1px solid var(--border);
	}
	:global(.widget .g-title) {
		color: var(--fg);
		font-weight: 600;
		margin-bottom: 0.2rem;
	}
	:global(.widget .lead) {
		color: var(--muted);
		margin: 0 0 0.35rem;
	}
	:global(.widget .row) {
		display: flex;
		flex-wrap: wrap;
		align-items: center;
		gap: 0.35rem;
	}
	:global(.widget ul.notes) {
		list-style: none;
		margin: 0.3rem 0 0;
		padding: 0;
		color: var(--muted);
		font-size: 0.92em;
	}
	:global(.widget ul.notes li) {
		margin: 0.1rem 0;
	}
</style>
