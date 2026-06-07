<script lang="ts">
	import { GraphView, decodeGraph, hexToBytes, type Graph } from 'covalence-ui';

	let input = $state('');

	let parseResult = $derived.by((): { graph: Graph | null; error: string | null } => {
		const trimmed = input.trim();
		if (trimmed === '') return { graph: null, error: null };
		try {
			return { graph: decodeGraph(hexToBytes(trimmed)), error: null };
		} catch (e) {
			return { graph: null, error: (e as Error).message };
		}
	});
	let graph = $derived(parseResult.graph);
	let error = $derived(parseResult.error);

	function loadExample() {
		// Quick demo built by hand to match what
		// `crates/covalence-graph/tests` produces. Easier to regenerate from
		// Python: covalence.Graph then .to_bytes().hex().
		input = EXAMPLE_HEX;
	}

	// Smoke example regenerated via covalence-python:
	//   #0 init      (ordered) out
	//   #1 split     (pure)    1 input  + 2 outputs (fan-out)
	//   #2 transform (ordered) 1 input  + 1 output
	//   #3 verify    (pure)    2 inputs + 1 output  (fan-in)
	//   #4 commit    (ordered) 1 input
	const EXAMPLE_HEX =
		'434f5647010501010101016f000104696e6974000300010169010101610101016200010573706c69' +
		'740102000101690102016f0001097472616e73666f726d000300010161000201620103016f000106' +
		'766572696679010100030169000106636f6d6d6974050000010001010200010203000201030103020400';
</script>

<svelte:head><title>covalence — graph</title></svelte:head>

<main>
	<header>
		<h1>cov:graph viewer</h1>
		<p>
			Paste the canonical bytes (hex) of a <code>cov:graph@0.1.0</code> object — magic
			<code>COVG</code>, version 1. Nodes flow top-to-bottom; consecutive
			<span class="ordered">ordered</span>
			nodes share a red state wire.
		</p>
	</header>

	<section class="controls">
		<textarea
			bind:value={input}
			placeholder="paste canonical-bytes hex here (or use the example)"
			rows="6"
			spellcheck="false"
		></textarea>
		<div class="row">
			<button onclick={loadExample}>Load example</button>
			<button onclick={() => { input = ''; }}>Clear</button>
		</div>
	</section>

	{#if error}
		<p class="err">decode error: {error}</p>
	{/if}

	{#if graph}
		<section class="info">
			<dl>
				<dt>nodes</dt><dd>{graph.nodes.length}</dd>
				<dt>edges</dt><dd>{graph.edges.length}</dd>
				<dt>version</dt><dd>{graph.version}</dd>
			</dl>
		</section>
		<section class="view">
			<GraphView {graph} />
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
	.ordered {
		color: #d04040;
		font-weight: 600;
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
