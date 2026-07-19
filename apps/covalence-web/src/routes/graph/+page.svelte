<script lang="ts">
	// cov:graph VIEWER. Decodes the canonical `cov:graph` blob family in the
	// browser (`packages/covalence-ui`'s decoders mirror the Rust encoders in
	// `crates/lib/graph`) and renders the result.
	//
	//   COVG topology  (+ LBLS labels, KFLG kind-flags overlays)  →  GraphView
	//   SDGM composite (references a COVG by hash + two overlay slots)
	//
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
		type StringDiagram
	} from 'covalence-ui';
	import '$lib/kernelPages.css';

	// A REAL sample, not hand-written bytes: emitted by `crates/lib/graph`'s
	// own encoders (`Graph::to_bytes`, `LabelList::to_bytes`,
	// `KindFlags::to_bytes`, `StringDiagramBuilder::build`) for a 4-node
	// source → split → (sink, tap) pipeline, and verified to round-trip through
	// the decoders on this page. Hand-written bytes would rot silently the
	// moment the wire format moved; these are reproducible from the encoder.
	const SAMPLE = {
		topology:
			'434f56470104010101036f75740003000102696e0102026c6f01020268690001000202696e0001000202696e0003000001000101020001020300',
		labels: '4c424c5301040106736f75726365010573706c6974010473696e6b0103746170',
		kinds: '4b464c47010406',
		diagram:
			'5344474d010ae42441962e85dcc7d06220da604f6c77966030971c25837d787aacfc648e72029e3e728f5451f39390ce9a7af6fce53e5845b29820232f31ef9743630a43e4af57f4abcf7cbbba794776d43908460aebc5215b95a69f83e432c5f34386584d2d'
	};

	let topologyHex = $state(SAMPLE.topology);
	let labelsHex = $state(SAMPLE.labels);
	let kindsHex = $state(SAMPLE.kinds);
	let diagramHex = $state('');

	type ParseResult = {
		diagram: ResolvedDiagram | null;
		info: string | null;
		/** Overlay slot hashes bound by magic rather than verified. See below. */
		unverified: string[];
		error: string | null;
	};
	const empty: ParseResult = { diagram: null, info: null, unverified: [], error: null };

	let parseResult = $derived.by((): ParseResult => {
		// Priority order: composite > topology + overlays.
		const dh = diagramHex.trim();
		if (dh !== '') return parseComposite(dh);
		const th = topologyHex.trim();
		if (th !== '') return parseTopology(th);
		return empty;
	});

	/** Decode whatever overlay hex the user supplied, keyed by its magic. */
	function pastedOverlays(): Map<string, Uint8Array> {
		const out = new Map<string, Uint8Array>();
		for (const hex of [labelsHex, kindsHex]) {
			const t = hex.trim();
			if (!t) continue;
			const bytes = hexToBytes(t);
			const m = magicOf(bytes);
			if (m === 'label-list' || m === 'kind-flags') out.set(m, bytes);
		}
		return out;
	}

	/**
	 * An SDGM composite names its overlays BY HASH. This page is a static demo
	 * with no content store, and there is no BLAKE3 hasher in the bundle, so a
	 * hash slot cannot be looked up or verified here.
	 *
	 * HONESTY INVARIANT: a hash slot is served from the pasted overlay of the
	 * matching magic and that slot's hash is recorded in `unverified`, which the
	 * page reports prominently. Uniform/absent slots need no lookup and are
	 * fully resolved, so they are NOT reported as unverified. Nothing here
	 * claims a binding it actually checked.
	 *
	 * SKELETON(cov:web.graph-overlay-store, minor): no content store or hasher
	 * client-side, so SDGM hash slots cannot be resolved or verified by hash.
	 */
	function parseComposite(hex: string): ParseResult {
		try {
			const sd: StringDiagram = decodeStringDiagram(hexToBytes(hex));
			const th = topologyHex.trim();
			if (!th) {
				return {
					...empty,
					info: `SDGM composite referencing graph ${hexOf(sd.graph).slice(0, 16)}… — paste that COVG topology above to render it.`
				};
			}
			const bytes = hexToBytes(th);
			if (magicOf(bytes) !== 'graph') {
				return { ...empty, error: `topology box does not hold a COVG blob` };
			}
			const graph = decodeGraph(bytes);
			const overlays = pastedOverlays();
			const unverified: string[] = [];
			const diagram = resolveDiagram(sd, graph, (h) => {
				// Matching the requested hash against the diagram's own labels slot
				// tells us which overlay kind is wanted.
				const hex32 = hexOf(h);
				const isLabels = sd.labels.kind === 'hash' && hexOf(sd.labels.hash) === hex32;
				const bytes = overlays.get(isLabels ? 'label-list' : 'kind-flags') ?? null;
				if (bytes) unverified.push(hex32);
				return bytes;
			});
			return { diagram, info: null, unverified, error: null };
		} catch (e) {
			return { ...empty, error: (e as Error).message };
		}
	}

	function parseTopology(hex: string): ParseResult {
		try {
			const bytes = hexToBytes(hex);
			const magic = magicOf(bytes);
			if (magic !== 'graph') {
				return { ...empty, error: `expected COVG topology, got ${magic ?? 'unknown'}` };
			}
			const graph = decodeGraph(bytes);
			const labels = labelsHex.trim() ? decodeLabelList(hexToBytes(labelsHex)) : null;
			const kinds = kindsHex.trim()
				? decodeKindFlags(hexToBytes(kindsHex))
				: { kinds: new Array(graph.nodes.length).fill('pure') as ('pure' | 'ordered')[] };
			if (labels && labels.labels.length !== graph.nodes.length) {
				return { ...empty, error: 'labels length ≠ node count' };
			}
			if (kinds.kinds.length !== graph.nodes.length) {
				return { ...empty, error: 'kind-flags length ≠ node count' };
			}
			const diagram: ResolvedDiagram =
				labels || kindsHex.trim() ? { graph, labels, kinds } : diagramFromGraphOnly(graph);
			return { diagram, info: null, unverified: [], error: null };
		} catch (e) {
			return { ...empty, error: (e as Error).message };
		}
	}

	let diagram = $derived(parseResult.diagram);
	let info = $derived(parseResult.info);
	let error = $derived(parseResult.error);
	let unverified = $derived(parseResult.unverified);

	function loadSample() {
		topologyHex = SAMPLE.topology;
		labelsHex = SAMPLE.labels;
		kindsHex = SAMPLE.kinds;
		diagramHex = '';
	}
	function loadCompositeSample() {
		topologyHex = SAMPLE.topology;
		labelsHex = SAMPLE.labels;
		kindsHex = SAMPLE.kinds;
		diagramHex = SAMPLE.diagram;
	}
	function clearAll() {
		topologyHex = labelsHex = kindsHex = diagramHex = '';
	}
</script>

<svelte:head><title>covalence — graph</title></svelte:head>

<main class="demo-page">
	<h1>cov:graph viewer</h1>
	<p class="sub">
		Canonical hex bytes for a <code>COVG</code> topology blob and (optionally)
		<code>LBLS</code> labels and <code>KFLG</code> kind-flags overlays. Or a full
		<code>SDGM</code> string-diagram composite, which references a topology by hash
		plus two overlay slots. Decoded in your browser by the mirrors of the Rust
		encoders in <code>crates/lib/graph</code>.
	</p>

	<div class="examples">
		<button onclick={loadSample} data-testid="example-button">sample: topology + overlays</button>
		<button onclick={loadCompositeSample} data-testid="example-button">sample: SDGM composite</button
		>
		<button onclick={clearAll}>clear</button>
	</div>

	<section class="controls">
		<label class="field">
			<span>topology (COVG)</span>
			<textarea
				bind:value={topologyHex}
				rows="4"
				spellcheck="false"
				placeholder="hex bytes"
				data-testid="topology-input"
			></textarea>
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
			<textarea bind:value={diagramHex} rows="2" spellcheck="false" placeholder="hex bytes"
			></textarea>
		</label>
	</section>

	{#if error}
		<p class="err" data-testid="graph-error">decode error: {error}</p>
	{/if}
	{#if info}
		<p class="info-line">{info}</p>
	{/if}
	{#if unverified.length}
		<p class="warn">
			overlay slot{unverified.length === 1 ? '' : 's'}
			{unverified.map((h) => h.slice(0, 12) + '…').join(', ')} bound from the pasted overlays
			<strong>by magic, not verified by hash</strong> — this page has no content store or hasher.
		</p>
	{/if}

	{#if diagram}
		<section class="info">
			<dl>
				<dt>nodes</dt>
				<dd data-testid="node-count">{diagram.graph.nodes.length}</dd>
				<dt>edges</dt>
				<dd data-testid="edge-count">{diagram.graph.edges.length}</dd>
				<dt>labels</dt>
				<dd>{diagram.labels ? 'present' : 'none'}</dd>
			</dl>
		</section>
		<!-- The decode above is ours and total; the RENDER is a third-party
		     component (`covalence-ui` → `@xyflow/svelte`) fed bytes a stranger
		     pasted. A boundary keeps a renderer crash from white-screening the
		     whole page: the decode summary is real information and must survive
		     it. -->
		<svelte:boundary>
			<section class="view" data-testid="graph-view">
				<GraphView {diagram} />
			</section>
			{#snippet failed(error)}
				<p class="err" data-testid="graph-render-error">
					the renderer failed: {(error as Error)?.message ?? String(error)} — the blob above
					decoded fine ({diagram?.graph.nodes.length} nodes, {diagram?.graph.edges.length} edges);
					it is the diagram view that could not mount.
				</p>
			{/snippet}
		</svelte:boundary>
	{/if}
</main>

<style>
	/* Page-specific only; shell/example/code chrome is shared — see
	   `$lib/kernelPages.css`. This page used to hardcode a light-only palette
	   (#5b6a85 / #eef1f7 / #d8dbe2 / #b00020) and `system-ui`, so it ignored the
	   site theme entirely. */
	.field {
		display: block;
		margin-bottom: 0.5rem;
	}
	.field span {
		display: block;
		font-size: 0.72rem;
		font-weight: 600;
		text-transform: uppercase;
		letter-spacing: 0.04em;
		color: var(--muted);
		margin-bottom: 0.2rem;
	}
	textarea {
		width: 100%;
		font-family: var(--font-mono);
		font-size: 0.75rem;
		line-height: 1.5;
		padding: 0.5rem;
		color: var(--fg);
		background: var(--surface);
		border: 1px solid var(--border);
		border-radius: 6px;
		resize: vertical;
		word-break: break-all;
	}
	textarea:focus {
		outline: none;
		border-color: var(--accent);
	}
	.err,
	.info-line,
	.warn {
		font-size: 0.78rem;
		margin: 0.5rem 0;
		line-height: 1.5;
	}
	.info-line {
		color: var(--muted);
	}
	.warn {
		color: color-mix(in srgb, var(--accent) 65%, var(--fg));
	}
	.info dl {
		display: flex;
		gap: 1rem;
		font-size: 0.8rem;
		color: var(--muted);
		margin: 1rem 0 0.5rem;
	}
	.info dt {
		font-weight: 600;
		margin-right: 0.25rem;
	}
	.view {
		margin-top: 0.5rem;
		border: 1px solid var(--border);
		border-radius: 8px;
		overflow: hidden;
	}
</style>
