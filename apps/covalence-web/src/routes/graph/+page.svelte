<script lang="ts">
	import {
		GraphView,
		decodeGraph,
		decodeStringDiagram,
		decodeLabelList,
		decodeKindFlags,
		resolveDiagram,
		diagramFromGraphOnly,
		hexToBytes,
		hexOf,
		magicOf,
		type ResolvedDiagram,
	} from 'covalence-ui';

	let topologyHex = $state('');
	let labelsHex = $state('');
	let kindsHex = $state('');
	let diagramHex = $state('');

	type ParseResult = { diagram: ResolvedDiagram | null; info: string | null; error: string | null };

	let parseResult = $derived.by((): ParseResult => {
		// Priority order: composite > topology + overlays.
		const dh = diagramHex.trim();
		if (dh !== '') return parseComposite(dh);
		const th = topologyHex.trim();
		if (th !== '') return parseTopology(th);
		return { diagram: null, info: null, error: null };
	});

	function parseComposite(hex: string): ParseResult {
		try {
			const sd = decodeStringDiagram(hexToBytes(hex));
			// No store wired up in this static demo; require all overlays inline.
			return {
				diagram: null,
				info: `string-diagram (graph=${hexOf(sd.graph).slice(0, 16)}…) — paste topology + overlays separately to render`,
				error: null,
			};
		} catch (e) {
			return { diagram: null, info: null, error: (e as Error).message };
		}
	}

	function parseTopology(hex: string): ParseResult {
		try {
			const bytes = hexToBytes(hex);
			const magic = magicOf(bytes);
			if (magic !== 'graph') {
				return { diagram: null, info: null, error: `expected COVG topology, got ${magic ?? 'unknown'}` };
			}
			const graph = decodeGraph(bytes);
			const labels = labelsHex.trim() ? decodeLabelList(hexToBytes(labelsHex)) : null;
			const kinds = kindsHex.trim()
				? decodeKindFlags(hexToBytes(kindsHex))
				: { kinds: new Array(graph.nodes.length).fill('pure') as ('pure' | 'ordered')[] };
			if (labels && labels.labels.length !== graph.nodes.length) {
				return { diagram: null, info: null, error: 'labels length ≠ node count' };
			}
			if (kinds.kinds.length !== graph.nodes.length) {
				return { diagram: null, info: null, error: 'kind-flags length ≠ node count' };
			}
			const diagram: ResolvedDiagram = labels || kindsHex.trim()
				? { graph, labels, kinds }
				: diagramFromGraphOnly(graph);
			return { diagram, info: null, error: null };
		} catch (e) {
			return { diagram: null, info: null, error: (e as Error).message };
		}
	}

	let diagram = $derived(parseResult.diagram);
	let info = $derived(parseResult.info);
	let error = $derived(parseResult.error);
</script>

<svelte:head><title>covalence — graph</title></svelte:head>

<main>
	<header>
		<h1>cov:graph viewer</h1>
		<p>
			Paste canonical hex bytes for a <code>COVG</code> topology blob and (optionally) <code>LBLS</code>
			labels and <code>KFLG</code> kind-flags overlays. Or paste a full <code>SDGM</code>
			string-diagram composite to inspect its references.
		</p>
	</header>

	<section class="controls">
		<label class="field">
			<span>topology (COVG)</span>
			<textarea bind:value={topologyHex} rows="4" spellcheck="false" placeholder="hex bytes"></textarea>
		</label>
		<label class="field">
			<span>labels (LBLS, optional)</span>
			<textarea bind:value={labelsHex} rows="2" spellcheck="false" placeholder="hex bytes"></textarea>
		</label>
		<label class="field">
			<span>kind-flags (KFLG, optional)</span>
			<textarea bind:value={kindsHex} rows="2" spellcheck="false" placeholder="hex bytes"></textarea>
		</label>
		<label class="field">
			<span>or — full string-diagram composite (SDGM)</span>
			<textarea bind:value={diagramHex} rows="2" spellcheck="false" placeholder="hex bytes"></textarea>
		</label>
		<div class="row">
			<button onclick={() => { topologyHex = labelsHex = kindsHex = diagramHex = ''; }}>Clear</button>
		</div>
	</section>

	{#if error}
		<p class="err">decode error: {error}</p>
	{/if}
	{#if info}
		<p class="info-line">{info}</p>
	{/if}

	{#if diagram}
		<section class="info">
			<dl>
				<dt>nodes</dt><dd>{diagram.graph.nodes.length}</dd>
				<dt>edges</dt><dd>{diagram.graph.edges.length}</dd>
				<dt>labels</dt><dd>{diagram.labels ? 'present' : 'none'}</dd>
			</dl>
		</section>
		<section class="view">
			<GraphView {diagram} />
		</section>
	{/if}
</main>

<style>
	main {
		max-width: 900px;
		margin: 24px auto;
		padding: 0 16px;
		font-family: system-ui, -apple-system, BlinkMacSystemFont, sans-serif;
	}
	header h1 {
		margin: 0 0 4px 0;
		font-size: 18px;
		font-weight: 600;
	}
	header p {
		color: #5b6a85;
		font-size: 13px;
		margin: 0 0 16px;
	}
	code {
		font-family: ui-monospace, SFMono-Regular, Menlo, monospace;
		font-size: 12px;
		background: #eef1f7;
		padding: 1px 4px;
		border-radius: 3px;
	}
	.field {
		display: block;
		margin-bottom: 8px;
	}
	.field span {
		display: block;
		font-size: 12px;
		font-weight: 600;
		color: #5b6a85;
		margin-bottom: 2px;
	}
	textarea {
		width: 100%;
		font-family: ui-monospace, SFMono-Regular, Menlo, monospace;
		font-size: 12px;
		padding: 8px;
		border: 1px solid #d8dbe2;
		border-radius: 4px;
		box-sizing: border-box;
	}
	.row {
		display: flex;
		gap: 8px;
		margin-top: 6px;
	}
	button {
		font: inherit;
		padding: 4px 10px;
		border: 1px solid #d8dbe2;
		background: #ffffff;
		border-radius: 4px;
		cursor: pointer;
	}
	button:hover {
		background: #eef1f7;
	}
	.err {
		color: #b00020;
		font-family: ui-monospace, SFMono-Regular, Menlo, monospace;
		font-size: 12px;
	}
	.info-line {
		color: #5b6a85;
		font-family: ui-monospace, SFMono-Regular, Menlo, monospace;
		font-size: 12px;
	}
	.info dl {
		display: flex;
		gap: 16px;
		font-size: 13px;
		color: #5b6a85;
		margin: 16px 0 8px 0;
	}
	.info dt {
		font-weight: 600;
		margin-right: 4px;
	}
	.info dd {
		margin: 0;
	}
	.view {
		margin-top: 8px;
	}
</style>
