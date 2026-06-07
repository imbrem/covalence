<script lang="ts">
	import { detectImageMime } from './detect.js';
	import GraphView from '../graph/GraphView.svelte';
	import GraphDagView from '../graph/GraphDagView.svelte';
	import {
		decodeGraph,
		decodeStringDiagram,
		decodeLabelList,
		decodeKindFlags,
		resolveDiagram,
		hexOf,
	} from '../graph/decode.js';
	import type { Graph, ResolvedDiagram, Hash } from '../graph/types.js';

	/**
	 * Resolve a keyed identity to its content bytes. The string-diagram
	 * branch uses this to walk slot references — the resolver typically
	 * does a two-step `lookup_tag → get_blob` against the kernel.
	 */
	export type BlobResolver = (hash: Hash) => Promise<Uint8Array | null>;

	// Tag strings — keep in sync with `*_HASH_CTX` constants in
	// crates/covalence-graph. These are BLAKE3 derivation contexts that
	// double as tag registry keys.
	const TAG_GRAPH_ORDERED = 'cov:graph@0.1.0 ordered';
	const TAG_STRING_DIAGRAM = 'cov:graph@0.1.0 string-diagram';
	const TAG_LABEL_LIST = 'cov:graph@0.1.0 label-list';
	const TAG_KIND_FLAGS = 'cov:graph@0.1.0 kind-flags';

	interface Props {
		hash: string;
		data: Uint8Array;
		mode: 'graph' | 'text' | 'hex' | 'image';
		/** Resolver used by string-diagram rendering to fetch the
		 *  underlying graph and overlay bytes from referenced hashes. */
		resolver?: BlobResolver;
		/** Tag of a keyed identity; required for graph-mode rendering.
		 *  Without a tag, graph mode reports the blob as un-renderable. */
		tag?: string;
	}

	let { hash, data, mode, resolver, tag }: Props = $props();

	type GraphState =
		| { kind: 'idle' }
		| { kind: 'loading' }
		| { kind: 'dag'; graph: Graph }
		| { kind: 'diagram'; diagram: ResolvedDiagram }
		| { kind: 'overlay'; what: string; count: number }
		| { kind: 'err'; message: string };

	let graphState = $state<GraphState>({ kind: 'idle' });
	/** Generation counter: invalidates older promises when inputs change. */
	let renderGen = 0;

	$effect(() => {
		if (mode !== 'graph') {
			graphState = { kind: 'idle' };
			return;
		}
		if (data.length === 0) {
			// Real bytes haven't arrived yet — wait for the next effect tick.
			graphState = { kind: 'loading' };
			return;
		}
		if (!tag) {
			graphState = {
				kind: 'err',
				message: 'blob is not registered with a tag (graph view requires tag dispatch)',
			};
			return;
		}
		const myGen = ++renderGen;
		graphState = { kind: 'loading' };
		void renderByTag(tag, data, resolver).then((s) => {
			if (myGen === renderGen) graphState = s;
		});
	});

	async function renderByTag(
		tag: string,
		bytes: Uint8Array,
		fetcher: BlobResolver | undefined,
	): Promise<GraphState> {
		try {
			switch (tag) {
				case TAG_GRAPH_ORDERED:
					return { kind: 'dag', graph: decodeGraph(bytes) };
				case TAG_STRING_DIAGRAM:
					return await renderStringDiagram(bytes, fetcher);
				case TAG_LABEL_LIST: {
					const ll = decodeLabelList(bytes);
					return { kind: 'overlay', what: 'label-list', count: ll.labels.length };
				}
				case TAG_KIND_FLAGS: {
					const kf = decodeKindFlags(bytes);
					return { kind: 'overlay', what: 'kind-flags', count: kf.kinds.length };
				}
				default:
					return { kind: 'err', message: `no renderer for tag '${tag}'` };
			}
		} catch (e) {
			return { kind: 'err', message: (e as Error).message };
		}
	}

	async function renderStringDiagram(
		bytes: Uint8Array,
		fetcher: BlobResolver | undefined,
	): Promise<GraphState> {
		if (!fetcher) {
			return {
				kind: 'err',
				message: 'string-diagram references external blobs but no resolver is configured',
			};
		}
		const sd = decodeStringDiagram(bytes);

		// Memoise the fetcher so repeated slot lookups don't refetch.
		const cache = new Map<string, Uint8Array>();
		async function fetchOnce(h: Hash): Promise<Uint8Array | null> {
			const key = hexOf(h);
			const cached = cache.get(key);
			if (cached) return cached;
			const fetched = await fetcher(h);
			if (fetched) cache.set(key, fetched);
			return fetched;
		}

		const graphBytes = await fetchOnce(sd.graph);
		if (!graphBytes) {
			return { kind: 'err', message: `graph blob ${hexOf(sd.graph)} not found` };
		}
		const graph = decodeGraph(graphBytes);

		// Eagerly fetch any overlay slots that are real hash references.
		const overlayMap = new Map<string, Uint8Array>();
		for (const slot of [sd.labels, sd.kinds]) {
			if (slot.kind === 'hash') {
				const bytes = await fetchOnce(slot.hash);
				if (bytes) overlayMap.set(hexOf(slot.hash), bytes);
			}
		}
		const diagram = resolveDiagram(sd, graph, (h) => overlayMap.get(hexOf(h)) ?? null);
		return { kind: 'diagram', diagram };
	}

	// --- Text / hex / image modes (unchanged from before) ---

	let textLines = $derived(new TextDecoder('utf-8', { fatal: false }).decode(data).split('\n'));
	let hexLines = $derived(buildHexDump(data));

	let imageUrl = $derived.by(() => {
		if (mode !== 'image') return '';
		const mime = detectImageMime(data);
		if (!mime) return '';
		if (typeof URL === 'undefined' || typeof Blob === 'undefined') return '';
		return URL.createObjectURL(new Blob([data], { type: mime }));
	});

	$effect(() => {
		const url = imageUrl;
		return () => {
			if (url) URL.revokeObjectURL(url);
		};
	});

	function buildHexDump(bytes: Uint8Array): string[] {
		const lines: string[] = [];
		for (let off = 0; off < bytes.length; off += 16) {
			const slice = bytes.subarray(off, Math.min(off + 16, bytes.length));
			const offset = off.toString(16).padStart(8, '0');
			const hex: string[] = [];
			for (let i = 0; i < 16; i++) {
				hex.push(i < slice.length ? slice[i].toString(16).padStart(2, '0') : '  ');
			}
			let ascii = '';
			for (let i = 0; i < slice.length; i++) {
				const b = slice[i];
				ascii += b >= 0x20 && b <= 0x7e ? String.fromCharCode(b) : '.';
			}
			lines.push(`${offset}  ${hex.slice(0, 8).join(' ')}  ${hex.slice(8).join(' ')}  |${ascii}|`);
		}
		return lines;
	}
</script>

<div class="blob-viewer">
	{#if mode === 'graph'}
		{#if graphState.kind === 'dag'}
			<GraphDagView graph={graphState.graph} />
		{:else if graphState.kind === 'diagram'}
			<GraphView diagram={graphState.diagram} />
		{:else if graphState.kind === 'overlay'}
			<div class="graph-fallback">
				{graphState.what} overlay ({graphState.count} entries) — view alongside a string-diagram to render.
			</div>
		{:else if graphState.kind === 'err'}
			<div class="graph-fallback">graph view: {graphState.message}</div>
		{:else if graphState.kind === 'loading'}
			<div class="graph-fallback">resolving overlays…</div>
		{:else}
			<div class="graph-fallback">waiting for blob…</div>
		{/if}
	{:else if mode === 'image'}
		{#if imageUrl}
			<div class="image-view">
				<img src={imageUrl} alt={`blob ${hash.slice(0, 12)}`} />
			</div>
		{:else}
			<div class="image-fallback">not a recognised image format</div>
		{/if}
	{:else if mode === 'text'}
		<pre class="text-view"><code>{#each textLines as line, i}<span class="line-num">{(i + 1).toString().padStart(4, ' ')}</span>  {line}
{/each}</code></pre>
	{:else}
		<pre class="hex-view"><code>{#each hexLines as line}{line}
{/each}</code></pre>
	{/if}
</div>

<style>
	.blob-viewer {
		width: 100%;
		overflow-x: auto;
	}

	pre {
		margin: 0;
		font-family: var(--font-mono, monospace);
		font-size: 0.875rem;
		line-height: 1.5;
		color: var(--fg, #e0e0e0);
	}

	.line-num {
		color: var(--muted, #888);
		user-select: none;
	}

	.hex-view {
		color: var(--muted, #888);
	}

	.image-view {
		display: flex;
		justify-content: center;
		padding: 1rem 0;
	}

	.image-view img {
		max-width: 100%;
		height: auto;
		background-image:
			linear-gradient(45deg, #2a2a2a 25%, transparent 25%),
			linear-gradient(-45deg, #2a2a2a 25%, transparent 25%),
			linear-gradient(45deg, transparent 75%, #2a2a2a 75%),
			linear-gradient(-45deg, transparent 75%, #2a2a2a 75%);
		background-size: 16px 16px;
		background-position: 0 0, 0 8px, 8px -8px, -8px 0;
	}

	.image-fallback,
	.graph-fallback {
		color: var(--muted, #888);
		text-align: center;
		padding: 2rem;
	}
</style>
