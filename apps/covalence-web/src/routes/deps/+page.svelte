<script lang="ts">
	// DEPENDENCY-TREE page. Renders the CI-gated dep graph snapshot from
	// docs/deps/ (embedded at build time). Regenerate with `bun run deps`;
	// `bun run deps:check` fails CI if this data is stale.
	//
	//   graph.json  — internal covalence-* normal-dependency edges + a `tcb`
	//                  block (roots / workspace closure / external crates).
	//   groups.json — golden cross-group edges (the crate-hierarchy contract).
	//   graph.svg    — the pre-rendered Graphviz picture (raw-imported, inlined).
	import graph from '../../../../../docs/deps/graph.json';
	import groups from '../../../../../docs/deps/groups.json';
	import graphSvg from '../../../../../docs/deps/graph.svg?raw';

	type Edge = { from: string; to: string };
	const nodes: string[] = graph.nodes;
	const edges: Edge[] = graph.edges;
	const tcb = graph.tcb as {
		roots: string[];
		workspace: string[];
		external: string[];
	};

	// crates/ is hierarchical: app/ ffi/ kernel/ lang/ lib/ proof/ server/
	// store/ vcs/. We can't read the filesystem here, so infer a crate's group
	// from the golden group edges' vocabulary + a small prefix heuristic. The
	// authoritative per-crate group lives in docs/deps/graph.dot; for the
	// interactive filter we approximate by first dep-path token where known and
	// otherwise leave it "misc" — the SVG below is the authoritative picture.
	const GROUPS = [
		'app',
		'ffi',
		'kernel',
		'lang',
		'lib',
		'proof',
		'server',
		'store',
		'vcs',
	];

	// Heuristic crate→group map (display-only; the SVG is authoritative).
	// Derived from the crate-map skill's known placements.
	const GROUP_OF: Record<string, string> = {
		covalence: 'app',
		'covalence-cov': 'app',
		'covalence-repl': 'app',
		'covalence-shell': 'app',
		'covalence-tcb-db': 'app',
		'covalence-serve': 'server',
		'covalence-client': 'server',
		'covalence-lsp': 'server',
		'covalence-web-kernel': 'server',
		'covalence-pure': 'kernel',
		'covalence-pure-trusted': 'kernel',
		'covalence-pure-eval': 'kernel',
		'covalence-core': 'kernel',
		'covalence-hol': 'kernel',
		'covalence-hol-eval': 'kernel',
		'covalence-init': 'kernel',
		'covalence-kernel': 'kernel',
		'covalence-inductive': 'kernel',
		'covalence-metamath': 'proof',
		'covalence-alethe': 'proof',
		'covalence-lean': 'proof',
		'covalence-opentheory': 'proof',
		'covalence-spectec': 'proof',
		'covalence-smt': 'proof',
		'covalence-sat': 'proof',
		'covalence-egglog': 'proof',
		'covalence-haskell': 'lang',
		'covalence-forsp': 'lang',
		'covalence-grammar': 'lang',
		'covalence-sexp': 'lang',
		'covalence-parse': 'lang',
		'covalence-acset': 'lang',
		'covalence-arrow': 'lang',
		'covalence-graph': 'lang',
		'covalence-hash': 'lib',
		'covalence-types': 'lib',
		'covalence-rand': 'lib',
		'covalence-json': 'lib',
		'covalence-proto': 'lib',
		'covalence-crypto-sig': 'lib',
		'covalence-proptest': 'lib',
		'covalence-multiformat': 'lib',
		'covalence-llm': 'lib',
		'covalence-wasm': 'lib',
		'covalence-wasm-spec': 'lib',
		'covalence-wasm-build-guest': 'lib',
		'covalence-object': 'store',
		'covalence-store': 'store',
		'covalence-sqlite': 'store',
		'covalence-kv': 'store',
		'covalence-parquet': 'store',
		'covalence-wasm-store': 'store',
		'covalence-git': 'vcs',
		'covalence-fuse': 'vcs',
		'covalence-python': 'ffi',
		'covalence-core-test-guest': 'kernel',
	};

	function groupOf(n: string): string {
		return GROUP_OF[n] ?? 'misc';
	}

	const tcbSet = new Set(tcb.workspace);
	const rootSet = new Set(tcb.roots);

	// Filter state.
	let selectedGroup = $state<string>('all');
	let query = $state('');

	// Adjacency for the selected node's neighbourhood highlight.
	let focus = $state<string | null>(null);

	const outMap = new Map<string, string[]>();
	const inMap = new Map<string, string[]>();
	for (const e of edges) {
		if (!outMap.has(e.from)) outMap.set(e.from, []);
		outMap.get(e.from)!.push(e.to);
		if (!inMap.has(e.to)) inMap.set(e.to, []);
		inMap.get(e.to)!.push(e.from);
	}

	let visibleNodes = $derived.by(() => {
		const q = query.trim().toLowerCase();
		return nodes
			.filter((n) => selectedGroup === 'all' || groupOf(n) === selectedGroup)
			.filter((n) => q === '' || n.toLowerCase().includes(q))
			.sort();
	});

	let counts = $derived.by(() => {
		const c: Record<string, number> = { all: nodes.length };
		for (const g of [...GROUPS, 'misc']) c[g] = nodes.filter((n) => groupOf(n) === g).length;
		return c;
	});

	function depsOf(n: string): string[] {
		return (outMap.get(n) ?? []).slice().sort();
	}
	function usedBy(n: string): string[] {
		return (inMap.get(n) ?? []).slice().sort();
	}

	let view = $state<'list' | 'svg'>('list');
</script>

<svelte:head><title>dependency tree — covalence</title></svelte:head>

<main>
	<h1>dependency tree</h1>
	<p class="sub">
		Internal <code>covalence-*</code> dependency edges from
		<code>docs/deps/graph.json</code> (embedded at build time; regenerate with
		<code>bun run deps</code>, CI-gated by <code>bun run deps:check</code>).
		<strong>{nodes.length}</strong> crates, <strong>{edges.length}</strong> edges.
		The <span class="tcb-swatch"></span> highlighted crates are the trusted
		computing base closure (<code>{tcb.roots.join(', ')}</code>).
	</p>

	<div class="tabs">
		<button class:on={view === 'list'} onclick={() => (view = 'list')}>interactive list</button>
		<button class:on={view === 'svg'} onclick={() => (view = 'svg')}>graphviz svg</button>
	</div>

	{#if view === 'list'}
		<div class="controls">
			<div class="chips">
				<button class:on={selectedGroup === 'all'} onclick={() => (selectedGroup = 'all')}>
					all <em>{counts.all}</em>
				</button>
				{#each GROUPS as g}
					{#if counts[g] > 0}
						<button class:on={selectedGroup === g} onclick={() => (selectedGroup = g)}>
							{g} <em>{counts[g]}</em>
						</button>
					{/if}
				{/each}
				{#if counts.misc > 0}
					<button class:on={selectedGroup === 'misc'} onclick={() => (selectedGroup = 'misc')}>
						misc <em>{counts.misc}</em>
					</button>
				{/if}
			</div>
			<input placeholder="filter by name…" bind:value={query} spellcheck="false" />
		</div>

		<div class="grid">
			<ul class="node-list">
				{#each visibleNodes as n}
					<li>
						<button
							class="node"
							class:tcb={tcbSet.has(n)}
							class:root={rootSet.has(n)}
							class:focus={focus === n}
							onclick={() => (focus = focus === n ? null : n)}
						>
							<span class="grp">{groupOf(n)}</span>
							<span class="nm">{n}</span>
							<span class="deg">{depsOf(n).length}↓ {usedBy(n).length}↑</span>
						</button>
					</li>
				{/each}
				{#if visibleNodes.length === 0}
					<li class="empty">no crates match</li>
				{/if}
			</ul>

			<aside class="detail">
				{#if focus}
					<h3>{focus} <span class="grp">{groupOf(focus)}</span></h3>
					{#if rootSet.has(focus)}<p class="tcb-note">TCB root</p>
					{:else if tcbSet.has(focus)}<p class="tcb-note">in the TCB closure</p>{/if}
					<h4>depends on ({depsOf(focus).length})</h4>
					<ul class="rel">
						{#each depsOf(focus) as d}
							<li><button onclick={() => (focus = d)}>{d}</button></li>
						{/each}
						{#if depsOf(focus).length === 0}<li class="empty">— none —</li>{/if}
					</ul>
					<h4>used by ({usedBy(focus).length})</h4>
					<ul class="rel">
						{#each usedBy(focus) as u}
							<li><button onclick={() => (focus = u)}>{u}</button></li>
						{/each}
						{#if usedBy(focus).length === 0}<li class="empty">— none —</li>{/if}
					</ul>
				{:else}
					<p class="hint">Select a crate to see its dependencies and dependents.</p>
					<h4>cross-group contract ({groups.groupEdges.length} golden edges)</h4>
					<pre class="group-edges">{groups.groupEdges.join('\n')}</pre>
				{/if}
			</aside>
		</div>
	{:else}
		<div class="svg-wrap">
			<!-- eslint-disable-next-line svelte/no-at-html-tags -->
			{@html graphSvg}
		</div>
	{/if}
</main>

<style>
	main {
		max-width: 72rem;
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
		margin: 0.4rem 0 1rem;
		line-height: 1.5;
	}
	code {
		background: var(--surface);
		border: 1px solid var(--border);
		border-radius: 3px;
		padding: 0 3px;
		font-size: 0.8em;
	}
	.tcb-swatch {
		display: inline-block;
		width: 0.7em;
		height: 0.7em;
		border-radius: 2px;
		background: color-mix(in srgb, var(--accent) 45%, transparent);
		vertical-align: middle;
	}
	.tabs,
	.chips {
		display: flex;
		gap: 0.35rem;
		flex-wrap: wrap;
	}
	.tabs {
		margin-bottom: 1rem;
	}
	button {
		font: inherit;
		color: var(--muted);
		background: var(--surface);
		border: 1px solid var(--border);
		border-radius: 5px;
		padding: 0.2rem 0.6rem;
		cursor: pointer;
	}
	button:hover {
		color: var(--fg);
	}
	button.on {
		color: var(--fg);
		border-color: var(--accent);
		background: color-mix(in srgb, var(--accent) 18%, transparent);
	}
	.controls {
		display: flex;
		justify-content: space-between;
		gap: 1rem;
		align-items: flex-start;
		margin-bottom: 0.75rem;
		flex-wrap: wrap;
	}
	.chips em {
		font-style: normal;
		opacity: 0.6;
		font-size: 0.8em;
	}
	.controls input {
		font: inherit;
		color: var(--fg);
		background: var(--surface);
		border: 1px solid var(--border);
		border-radius: 5px;
		padding: 0.25rem 0.6rem;
		min-width: 12rem;
	}
	.grid {
		display: grid;
		grid-template-columns: minmax(0, 1.4fr) minmax(0, 1fr);
		gap: 1rem;
		align-items: start;
	}
	.node-list {
		list-style: none;
		display: flex;
		flex-direction: column;
		gap: 2px;
	}
	.node {
		display: flex;
		align-items: baseline;
		gap: 0.6rem;
		width: 100%;
		text-align: left;
		background: transparent;
		border: 1px solid transparent;
		border-radius: 5px;
		padding: 0.25rem 0.5rem;
	}
	.node:hover {
		background: var(--surface);
	}
	.node.focus {
		border-color: var(--accent);
		background: color-mix(in srgb, var(--accent) 12%, transparent);
	}
	.node.tcb .nm {
		color: color-mix(in srgb, var(--accent) 70%, var(--fg));
	}
	.node.root .nm {
		font-weight: 700;
		color: var(--accent);
	}
	.node .grp {
		font-size: 0.7rem;
		text-transform: uppercase;
		letter-spacing: 0.04em;
		color: var(--muted);
		min-width: 3.5rem;
	}
	.node .nm {
		flex: 1;
	}
	.node .deg {
		font-size: 0.72rem;
		color: var(--muted);
	}
	.detail {
		position: sticky;
		top: 1rem;
		border: 1px solid var(--border);
		border-radius: 8px;
		padding: 0.75rem 1rem;
		background: var(--surface);
		min-height: 12rem;
	}
	.detail h3 {
		font-size: 1rem;
		margin-bottom: 0.25rem;
	}
	.detail h3 .grp,
	.detail h4 {
		font-size: 0.75rem;
		color: var(--muted);
		text-transform: uppercase;
		letter-spacing: 0.03em;
		font-weight: 600;
	}
	.detail h4 {
		margin: 0.75rem 0 0.25rem;
	}
	.tcb-note {
		display: inline-block;
		font-size: 0.72rem;
		color: var(--accent);
		border: 1px solid var(--accent);
		border-radius: 4px;
		padding: 0 4px;
		margin-bottom: 0.25rem;
	}
	.rel {
		list-style: none;
		display: flex;
		flex-direction: column;
		gap: 1px;
	}
	.rel button {
		background: transparent;
		border: none;
		padding: 0.1rem 0.25rem;
		color: var(--fg);
		text-align: left;
	}
	.rel button:hover {
		color: var(--accent);
		text-decoration: underline;
	}
	.empty,
	.hint {
		color: var(--muted);
		font-size: 0.8rem;
		font-style: italic;
		padding: 0.25rem 0;
	}
	.group-edges {
		font-size: 0.72rem;
		color: var(--muted);
		white-space: pre;
		overflow-x: auto;
		line-height: 1.4;
	}
	.svg-wrap {
		border: 1px solid var(--border);
		border-radius: 8px;
		padding: 1rem;
		background: #ffffff;
		overflow: auto;
	}
	.svg-wrap :global(svg) {
		max-width: 100%;
		height: auto;
	}
</style>
