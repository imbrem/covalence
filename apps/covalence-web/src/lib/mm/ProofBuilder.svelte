<script lang="ts">
	// Backward proof builder — the LAMP editor, minimal but real.
	//
	// THE HONESTY ANCHOR (do not weaken): this component never decides that
	// anything is proved. Closing every leaf of the goal tree makes the tree
	// *closed*, which is a fact about the tree, not about provability — the
	// header says "closed, not yet checked" and stays that way. The single
	// place "proved" appears in the UI is behind a POST /verify that came back
	// `ok:true`, and it is rendered together with the conclusion that response
	// returned. `ok:false` errors are shown verbatim, in the checker's words.
	//
	// Two ways to close a goal:
	//   - apply an assertion backwards (POST /apply) — produces subgoals;
	//   - cite a literal RPN fragment — the only way to name a hypothesis
	//     label, since /apply matches assertions only. `$f` labels are always
	//     citable; a theorem's `$e` labels become citable when /verify is given
	//     that theorem's name, which is what the "frame" field below is for.
	import type { Hash, MmSearchHit, MmVerifyResponse } from 'covalence-client';
	import { client } from '$lib/api';
	import { renderMm } from '$lib/mmUnicode';
	import ProofSteps from './ProofSteps.svelte';
	import AssertionSearch from './AssertionSearch.svelte';
	import {
		applyChildren,
		assemble,
		newGoal,
		replaceGoal,
		substSubtree,
		treeStatus,
		type GoalNode
	} from './proofTree';

	interface Props {
		hash: Hash;
		user?: string;
		unicode: boolean;
		symbolMap: Record<string, string>;
		/** Statement to prefill the goal box with (from the selected theorem). */
		seedGoal?: string;
		/** Theorem whose frame the proof is written in — see the `frame` field. */
		seedTheorem?: string;
	}
	const { hash, user, unicode, symbolMap, seedGoal = '', seedTheorem = '' }: Props = $props();

	let goalInput = $state('');
	let frame = $state('');
	let root = $state<GoalNode | null>(null);
	/** Whole previous trees. Trees are rebuilt structurally on every edit, so an
	 * undo is just popping one — no inverse operations to get wrong. */
	let history = $state<GoalNode[]>([]);
	let selId = $state<number | null>(null);
	let applyErr = $state('');
	let applying = $state(false);
	let citeInput = $state('');
	let verifying = $state(false);
	let verifyRes = $state<MmVerifyResponse | null>(null);
	let verifyErr = $state('');
	let supplyInput = $state('');

	// Prefill from the page's current selection whenever it changes, but never
	// clobber a builder session in progress.
	$effect(() => {
		const g = seedGoal;
		if (root === null && g) {
			goalInput = g;
			frame = seedTheorem;
		}
	});

	const status = $derived(root ? treeStatus(root) : null);
	const selected = $derived.by(() => {
		if (!root || selId === null) return null;
		return find(root, selId);
	});
	const asm = $derived(root ? assemble(root) : null);

	function find(n: GoalNode, id: number): GoalNode | null {
		if (n.id === id) return n;
		if (n.step?.via !== 'apply') return null;
		for (const c of n.step.children) {
			const hit = find(c, id);
			if (hit) return hit;
		}
		return null;
	}

	/** Commit a new tree, pushing the old one onto the undo stack. Any edit
	 * invalidates the last /verify result — it was about a different proof. */
	function commit(next: GoalNode) {
		if (root) history = [...history, root];
		root = next;
		verifyRes = null;
		verifyErr = '';
	}

	function start() {
		const g = goalInput.trim();
		if (!g) return;
		const r = newGoal(g);
		root = r;
		history = [];
		selId = r.id;
		applyErr = '';
		verifyRes = null;
		verifyErr = '';
	}

	function reset() {
		root = null;
		history = [];
		selId = null;
		applyErr = '';
		verifyRes = null;
		verifyErr = '';
	}

	function undo() {
		const prev = history[history.length - 1];
		if (!prev) return;
		history = history.slice(0, -1);
		root = prev;
		verifyRes = null;
		verifyErr = '';
		// The selection may have pointed at a node that no longer exists.
		if (selId !== null && !find(prev, selId)) selId = prev.id;
	}

	async function applyLabel(hit: MmSearchHit) {
		const g = selected;
		if (!g || !root || g.expr === null) return;
		applying = true;
		applyErr = '';
		try {
			const res = await client.mmApply(hash, { goal: g.expr, label: hit.label }, { user });
			if (!res.ok) {
				// The server's own words — not a paraphrase.
				applyErr = res.error;
				return;
			}
			const next: GoalNode = {
				...g,
				expr: res.goal, // the server's normalized rendering
				step: {
					via: 'apply',
					label: res.label,
					kind: res.kind,
					subst: res.subst,
					unsolved: res.unsolved,
					children: applyChildren(res.floats, res.subgoals)
				}
			};
			commit(replaceGoal(root, g.id, next));
			// Move to the first remaining open child, if any, so the user can keep going.
			const firstOpen = next.step?.via === 'apply' ? next.step.children.find((c) => !c.step) : null;
			selId = firstOpen ? firstOpen.id : next.id;
		} catch (e) {
			applyErr = e instanceof Error ? e.message : String(e);
		} finally {
			applying = false;
		}
	}

	function cite() {
		const g = selected;
		if (!g || !root) return;
		const labels = citeInput.trim().split(/\s+/).filter(Boolean);
		if (labels.length === 0) return;
		commit(replaceGoal(root, g.id, { ...g, step: { via: 'cite', labels } }));
		citeInput = '';
	}

	/** Supply an expression for an unsolved float variable, propagating it into
	 * the sibling subgoals that mention it. */
	function supply() {
		const g = selected;
		if (!g || !root || g.origin.kind !== 'float') return;
		const expr = supplyInput.trim();
		if (!expr) return;
		const v = g.origin.var;
		const tc = g.origin.typecode;
		// Rewrite the whole tree (the variable is scoped to the application, but
		// rewriting globally is harmless — a solved var never reappears free).
		let next = substSubtree(root, v, expr);
		const target = find(next, g.id);
		if (target) {
			next = replaceGoal(next, g.id, { ...target, expr: `${tc} ${expr}`, unsolved: false });
		}
		commit(next);
		supplyInput = '';
	}

	async function check() {
		if (!root || !asm?.ok) return;
		verifying = true;
		verifyErr = '';
		verifyRes = null;
		try {
			const body = {
				steps: asm.steps,
				goal: root.expr ?? '',
				...(frame.trim() ? { theorem: frame.trim() } : {})
			};
			verifyRes = await client.mmVerify(hash, body, { user });
		} catch (e) {
			verifyErr = e instanceof Error ? e.message : String(e);
		} finally {
			verifying = false;
		}
	}

	const searchFn = (q: string) => client.mmSearch(hash, q, { limit: 40, user });
	const show = (s: string) => renderMm(s, unicode, symbolMap);
</script>

{#snippet goalTree(n: GoalNode, depth: number)}
	<div class="gn" style="padding-left:{depth * 0.9}rem">
		<button
			class="gn-row"
			class:sel={selId === n.id}
			class:open={n.step === null}
			class:unsolved={n.unsolved}
			data-testid="goal-node"
			onclick={() => (selId = n.id)}
		>
			<span class="gn-mark">{n.step === null ? '?' : '·'}</span>
			{#if n.origin.kind === 'essential'}
				<span class="gn-origin" title="essential hypothesis of the applied assertion"
					>{n.origin.hypLabel}</span
				>
			{:else if n.origin.kind === 'float'}
				<span class="gn-origin float" title="floating hypothesis — syntax obligation"
					>${n.origin.var}</span
				>
			{/if}
			<span class="gn-expr">
				{#if n.expr === null}
					<em class="unsolved-txt">unsolved — supply {n.origin.kind === 'float' ? n.origin.var : '?'}</em
					>
				{:else}
					{show(n.expr)}
				{/if}
			</span>
			{#if n.step?.via === 'apply'}
				<span class="gn-by">by {n.step.label}</span>
			{:else if n.step?.via === 'cite'}
				<span class="gn-by cite">cite {n.step.labels.join(' ')}</span>
			{/if}
		</button>
		{#if n.step?.via === 'apply'}
			{#each n.step.children as c (c.id)}
				{@render goalTree(c, depth + 1)}
			{/each}
		{/if}
	</div>
{/snippet}

<div class="builder" data-testid="proof-builder">
	{#if root === null}
		<p class="note">
			Build a proof backwards: state a goal, then apply assertions to it until no goal is left open.
			Nothing here claims a proof — <b>check with /verify</b> does: the Metamath checker replays
			your steps in Rust, then the HOL kernel re-derives the result as
			<code>⊢ Derivable ⌜S⌝</code>.
		</p>
		<div class="brow">
			<label class="fl">
				goal
				<input
					type="text"
					bind:value={goalInput}
					placeholder="|- t = t — rendered statement, first token is the typecode"
					spellcheck="false"
					data-testid="builder-goal-input"
				/>
			</label>
		</div>
		<div class="brow">
			<label class="fl narrow" title="theorem whose frame this proof is written in">
				frame
				<input
					type="text"
					bind:value={frame}
					placeholder="(optional) theorem name"
					spellcheck="false"
					data-testid="builder-frame-input"
				/>
			</label>
			<button class="primary" onclick={start} disabled={!goalInput.trim()}>Start</button>
		</div>
		<p class="note">
			<b>frame</b> names an existing theorem: its <code>$e</code> hypothesis labels become citable and
			its <code>$d</code> declarations available. Leave it empty for an empty frame — <code>$f</code>
			labels are citable either way.
		</p>
	{:else}
		<div class="bhead">
			<span class="goal-lbl">goal</span>
			<code class="goal-expr" data-testid="builder-goal">{show(root.expr ?? '')}</code>
			{#if frame.trim()}<span class="dim">in frame <b>{frame.trim()}</b></span>{/if}
			<span class="spacer"></span>
			<button class="copy" onclick={undo} disabled={history.length === 0}>undo</button>
			<button class="copy" onclick={reset}>new goal</button>
		</div>

		<!-- Tree bookkeeping only. "closed" ≠ "proved" and the wording must not
		     drift: the checker has not seen this proof yet. -->
		<div class="bstatus" data-testid="builder-status">
			{#if verifyRes?.ok}
				<!-- The one place the word may appear, and only because /verify said
				     so. `commit` clears verifyRes on every edit, so a non-null ok
				     result always belongs to the tree currently on screen. -->
				<span class="verified">verified by /verify</span>
				<span class="dim">· {status?.nodes} nodes</span>
			{:else if status?.closed}
				<span class="closed">closed, not yet checked</span>
				<span class="dim">· {status.nodes} nodes · no open goals</span>
			{:else}
				<span class="openc">{status?.open} open goal{status?.open === 1 ? '' : 's'}</span>
				<span class="dim">· {status?.nodes} nodes</span>
			{/if}
			<span class="spacer"></span>
			<button
				class="primary small"
				onclick={check}
				disabled={verifying || !asm?.ok}
				title={asm?.ok ? 'run the real checker' : 'close every goal first'}
				data-testid="verify-button"
			>
				{verifying ? 'checking…' : 'Check with /verify'}
			</button>
		</div>

		<div class="bpanes">
			<div class="btree" data-testid="goal-tree">
				{@render goalTree(root, 0)}
			</div>

			<div class="bwork">
				{#if selected === null}
					<p class="note">Select a goal in the tree.</p>
				{:else if selected.step !== null}
					<p class="note">
						This goal is closed
						{#if selected.step.via === 'apply'}by <code>{selected.step.label}</code>{:else}by citing
							<code>{selected.step.labels.join(' ')}</code>{/if}. Use <b>undo</b> to take it back.
					</p>
				{:else if selected.expr === null && selected.origin.kind === 'float'}
					<div class="flabel">
						supply <code>{selected.origin.var}</code> ({selected.origin.typecode})
					</div>
					<p class="note">
						The goal does not determine this variable — it occurs only in the assertion's
						hypotheses. That is normal. Give it an expression (no typecode) and it will be filled
						into the subgoals that mention it.
					</p>
					<div class="brow">
						<input
							type="text"
							bind:value={supplyInput}
							placeholder="expression for {selected.origin.var}, e.g. t = t"
							spellcheck="false"
							data-testid="supply-input"
							onkeydown={(e) => e.key === 'Enter' && supply()}
						/>
						<button class="primary small" onclick={supply} disabled={!supplyInput.trim()}>
							Supply
						</button>
					</div>
				{:else}
					<div class="flabel">working on</div>
					<pre class="mm sel-goal" data-testid="selected-goal">{show(selected.expr ?? '')}</pre>

					{#if applyErr}
						<!-- Verbatim server text. -->
						<p class="err" data-testid="apply-error">{applyErr}</p>
					{/if}

					<div class="flabel sub">apply an assertion</div>
					<!-- The debounce lives in the child, next to the search it throttles. -->
					<AssertionSearch
						search={searchFn}
						onpick={applyLabel}
						{unicode}
						{symbolMap}
						disabled={applying}
					/>

					<!-- TODO(cov:web.mm-hyp-label-picker, minor): Offer the in-scope $f/$e
					     labels as a pickable list. /search returns assertions only, so the
					     user currently has to know the hypothesis label to type it. -->
					<div class="flabel sub">or cite labels directly</div>
					<div class="brow">
						<input
							type="text"
							bind:value={citeInput}
							placeholder="RPN labels, e.g. tt  — for $f/$e hypotheses"
							spellcheck="false"
							data-testid="cite-input"
							onkeydown={(e) => e.key === 'Enter' && cite()}
						/>
						<button class="primary small" onclick={cite} disabled={!citeInput.trim()}>Cite</button>
					</div>
					<p class="note">
						<code>/apply</code> matches assertions only, so hypothesis labels are cited by hand. The
						fragment is inserted verbatim into the proof and stands or falls at <code>/verify</code>.
					</p>
				{/if}
			</div>
		</div>

		{#if asm}
			<div class="flabel sub">assembled proof (RPN)</div>
			{#if asm.ok}
				<pre class="mm rpn" data-testid="rpn-steps">{asm.steps.join(' ')}</pre>
			{:else}
				<p class="note">
					Not assemblable yet — <b>{asm.open.expr ?? 'an unsolved variable'}</b> is still open.
				</p>
			{/if}
		{/if}

		{#if verifyErr}
			<p class="err" data-testid="verify-result">request failed: {verifyErr}</p>
		{:else if verifyRes}
			{#if verifyRes.ok}
				<div class="vok" data-testid="verify-result">
					<span class="vbadge">verified by the Metamath checker</span>
					<code class="vconc" data-testid="verify-conclusion">{show(verifyRes.conclusion)}</code>
				</div>
				<p class="note">
					This is the conclusion <code>/verify</code> returned, replayed below — the only claim of
					provedness the <em>builder</em> makes, and it comes from <code>/verify</code>, never from
					this page's own bookkeeping.
				</p>
				<!-- TWO SEPARATE CLAIMS, and the UI must never merge them: the badge
				     above is the Rust Metamath replay; the block below is the HOL
				     kernel independently RE-DERIVING the result. The kernel is asked
				     only after the replay succeeds, and it can still decline — so
				     each outcome gets its own wording. Never show the derived text
				     for a failed or skipped derivation. -->
				{#if verifyRes.hol?.ok}
					<div class="hol-ok" data-testid="hol-result">
						<span class="vbadge kernel">re-derived in the HOL kernel</span>
						<!-- The theorem VERBATIM, hypotheses included. Rendering a
						     hypothesis-carrying theorem as `⊢ concl` would be a false
						     claim, so this is never reassembled client-side. -->
						<code class="vconc" data-testid="hol-thm">{verifyRes.hol.thm}</code>
					</div>
					<p class="note">
						The kernel did not take the Metamath checker's word for it: it replayed your proof
						against the <code>{verifyRes.hol.ruleSet}</code> rule set and
						<em>constructed</em> this theorem ({verifyRes.hol.elapsedMs.toFixed(1)}&thinsp;ms) — the
						same construct-don't-trust status an imported theorem has.
						{#if verifyRes.hol.hypCount > 0}
							It carries {verifyRes.hol.hypCount} hypothes{verifyRes.hol.hypCount === 1
								? 'is'
								: 'es'}, shown above the turnstile.
						{/if}
					</p>
				{:else if verifyRes.hol && verifyRes.hol.ok === false}
					<p class="note caveat" data-testid="hol-result">
						{#if verifyRes.hol.skipped}
							<strong>No kernel derivation was attempted</strong> ({verifyRes.hol.reason}). What
							you have is a Rust-checked Metamath derivation only.
						{:else}
							<strong>The kernel could not re-derive this</strong>: {verifyRes.hol.error}. The
							Metamath replay above stands on its own, but nothing here is a kernel theorem.
						{/if}
					</p>
				{/if}
				<ProofSteps steps={verifyRes.steps} {unicode} {symbolMap} resetKey={verifyRes.conclusion} />
			{:else}
				<!-- The checker's message, unedited. -->
				<p class="err" data-testid="verify-result">{verifyRes.error}</p>
			{/if}
		{/if}
	{/if}
</div>

<style>
	.builder {
		font-size: 0.8rem;
	}
	.brow {
		display: flex;
		gap: 0.5rem;
		align-items: center;
		margin: 0.4rem 0;
	}
	.brow input[type='text'] {
		flex: 1;
		padding: 0.4rem 0.5rem;
		border: 1px solid var(--border);
		border-radius: 5px;
		background: var(--code-bg);
		color: var(--fg);
		font-family: var(--font-mono);
		font-size: 0.78rem;
	}
	.fl {
		display: flex;
		align-items: center;
		gap: 0.4rem;
		flex: 1;
		font-size: 0.7rem;
		color: var(--muted);
		text-transform: uppercase;
		letter-spacing: 0.05em;
	}
	.fl.narrow {
		flex: none;
		width: 22rem;
	}
	.fl input {
		flex: 1;
	}
	button.primary {
		padding: 0.4rem 0.9rem;
		border: none;
		border-radius: 6px;
		background: var(--accent);
		color: #fff;
		font-weight: 600;
		cursor: pointer;
		white-space: nowrap;
		font-size: 0.78rem;
	}
	button.primary.small {
		padding: 0.3rem 0.6rem;
		font-size: 0.74rem;
	}
	button.primary:disabled {
		opacity: 0.5;
		cursor: default;
	}
	.copy {
		padding: 0.25rem 0.55rem;
		border: 1px solid var(--border);
		border-radius: 5px;
		background: var(--surface);
		color: var(--fg);
		cursor: pointer;
		font-size: 0.74rem;
	}
	.copy:hover:not(:disabled) {
		border-color: var(--accent);
	}
	.copy:disabled {
		opacity: 0.45;
		cursor: default;
	}
	.bhead,
	.bstatus {
		display: flex;
		align-items: center;
		gap: 0.5rem;
		flex-wrap: wrap;
		margin-bottom: 0.4rem;
	}
	.spacer {
		flex: 1;
	}
	.goal-lbl {
		font-size: 0.62rem;
		text-transform: uppercase;
		letter-spacing: 0.06em;
		color: var(--muted);
	}
	.goal-expr {
		font-size: 0.8rem;
		color: var(--fg);
	}
	.bstatus .closed {
		color: var(--warnc);
		font-weight: 600;
	}
	.bstatus .verified {
		color: var(--ok);
		font-weight: 700;
	}
	.bstatus .openc {
		color: var(--accent);
		font-weight: 600;
	}
	.dim {
		color: var(--muted);
	}
	.bpanes {
		display: grid;
		grid-template-columns: minmax(200px, 1fr) minmax(240px, 1.1fr);
		gap: 0.8rem;
	}
	.btree {
		border: 1px solid var(--border);
		border-radius: 6px;
		background: var(--code-bg);
		padding: 0.35rem 0.3rem;
		max-height: 22rem;
		overflow: auto;
		scrollbar-width: thin;
	}
	.gn-row {
		display: flex;
		align-items: baseline;
		gap: 0.4rem;
		width: 100%;
		text-align: left;
		padding: 0.18rem 0.35rem;
		border: none;
		border-radius: 4px;
		background: transparent;
		color: var(--fg);
		font-family: var(--font-mono);
		font-size: 0.75rem;
		cursor: pointer;
	}
	.gn-row:hover {
		background: rgba(124, 111, 247, 0.12);
	}
	.gn-row.sel {
		background: rgba(124, 111, 247, 0.24);
	}
	.gn-mark {
		flex: none;
		width: 0.9em;
		color: var(--muted);
	}
	.gn-row.open .gn-mark {
		color: var(--accent);
		font-weight: 700;
	}
	.gn-origin {
		flex: none;
		font-size: 0.66rem;
		color: var(--muted);
		border: 1px solid var(--border);
		border-radius: 3px;
		padding: 0 0.22rem;
	}
	.gn-origin.float {
		color: var(--warnc);
		border-color: rgba(251, 191, 36, 0.4);
	}
	.gn-expr {
		flex: 1;
		white-space: nowrap;
		overflow: hidden;
		text-overflow: ellipsis;
	}
	.gn-row.unsolved .gn-expr {
		color: var(--warnc);
	}
	.unsolved-txt {
		font-style: italic;
	}
	.gn-by {
		flex: none;
		font-size: 0.68rem;
		color: var(--ok);
	}
	.gn-by.cite {
		color: var(--accent);
	}
	.bwork {
		border: 1px solid var(--border);
		border-radius: 6px;
		padding: 0.5rem;
		background: var(--surface);
		max-height: 22rem;
		overflow-y: auto;
		scrollbar-width: thin;
	}
	.flabel {
		font-size: 0.65rem;
		text-transform: uppercase;
		letter-spacing: 0.06em;
		color: var(--muted);
		margin-bottom: 0.25rem;
	}
	.flabel.sub {
		margin-top: 0.7rem;
	}
	pre.mm {
		background: var(--code-bg);
		border: 1px solid var(--border);
		border-radius: 5px;
		padding: 0.4rem 0.5rem;
		font-family: var(--font-mono);
		font-size: 0.76rem;
		white-space: pre-wrap;
		word-break: break-word;
		margin: 0 0 0.3rem;
		color: var(--fg);
	}
	pre.rpn {
		color: var(--accent);
		max-height: 8rem;
		overflow-y: auto;
	}
	.note {
		font-size: 0.74rem;
		color: var(--muted);
		margin: 0.3rem 0;
		line-height: 1.45;
	}
	.note b,
	.dim b {
		color: var(--fg);
	}
	/* The verified badge is the weaker of the page's two trust claims (Rust
	   Metamath replay, not a HOL kernel theorem). Set off so it reads as part
	   of the result, not as fine print under it. */
	.note.caveat {
		border-left: 2px solid var(--warnc);
		padding: 0.35rem 0 0.35rem 0.55rem;
		margin-top: 0.45rem;
	}
	.note.caveat strong {
		color: var(--fg);
	}
	.err {
		font-size: 0.76rem;
		color: var(--bad);
		background: rgba(248, 113, 113, 0.08);
		border: 1px solid rgba(248, 113, 113, 0.3);
		border-radius: 5px;
		padding: 0.4rem 0.5rem;
		margin: 0.4rem 0;
		font-family: var(--font-mono);
		white-space: pre-wrap;
		word-break: break-word;
	}
	.vok,
	.hol-ok {
		display: flex;
		align-items: center;
		gap: 0.5rem;
		flex-wrap: wrap;
		margin: 0.4rem 0 0.2rem;
	}
	/* The kernel claim is the stronger of the two and reads as its own result,
	   not as a footnote to the Metamath badge above it. */
	.hol-ok {
		border-left: 2px solid var(--accent);
		padding-left: 0.55rem;
	}
	.vbadge.kernel {
		color: var(--accent);
		background: color-mix(in srgb, var(--accent) 14%, transparent);
		border-color: color-mix(in srgb, var(--accent) 40%, transparent);
	}
	.vbadge {
		font-size: 0.66rem;
		text-transform: uppercase;
		letter-spacing: 0.06em;
		font-weight: 700;
		color: var(--ok);
		background: rgba(74, 222, 128, 0.14);
		border: 1px solid rgba(74, 222, 128, 0.4);
		border-radius: 4px;
		padding: 0.12rem 0.4rem;
	}
	.vconc {
		font-size: 0.8rem;
		color: var(--fg);
	}
	code {
		font-family: var(--font-mono);
		background: var(--code-bg);
		border: 1px solid var(--border);
		padding: 0.03rem 0.22rem;
		border-radius: 3px;
		font-size: 0.9em;
	}
</style>
