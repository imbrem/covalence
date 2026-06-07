<script lang="ts">
	import {
		SvelteFlow,
		Background,
		Controls,
		type Node,
		type Edge,
	} from '@xyflow/svelte';
	import '@xyflow/svelte/dist/style.css';
	import type { Graph } from './types.js';
	import DagNode from './DagNode.svelte';
	import { layeredDagLayout } from './dagLayout.js';

	/**
	 * Plain DAG rendering: dots and lines. Use this when the blob is a
	 * topology-only `COVG` — no labels, no per-node Pure/Ordered, no
	 * string-diagram semantics to convey.
	 */
	interface Props {
		graph: Graph;
	}
	let { graph }: Props = $props();

	const nodeTypes = { dag: DagNode };

	let nodes = $state<Node[]>([]);
	let edges = $state<Edge[]>([]);

	$effect(() => {
		const { positions } = layeredDagLayout(graph);
		nodes = graph.nodes.map((node, i) => ({
			id: `n${i}`,
			type: 'dag',
			position: positions[i] ?? { x: 0, y: i * 80 },
			data: {
				id: i,
				label: `#${i}`,
				in: node.ports.filter((p) => p.kind === 'input').length,
				out: node.ports.filter((p) => p.kind === 'output').length,
			},
			draggable: true,
		}));

		// Collapse multi-edges (multiple wires between the same pair of nodes)
		// into a single visible line. Per-port detail isn't meaningful in a
		// plain DAG view.
		const seen = new Set<string>();
		const distinctEdges: Edge[] = [];
		for (const e of graph.edges) {
			const key = `${e.fromNode}->${e.toNode}`;
			if (seen.has(key)) continue;
			seen.add(key);
			distinctEdges.push({
				id: key,
				source: `n${e.fromNode}`,
				target: `n${e.toNode}`,
				sourceHandle: 's',
				targetHandle: 't',
				// With layered layout, smoothstep gives clean orthogonal
				// routing between ranks; the default bezier is also fine
				// but smoothstep is a more standard DAG look.
				type: 'smoothstep',
				style: 'stroke: #1c2233; stroke-width: 1.5;',
			});
		}
		edges = distinctEdges;
	});
</script>

<div class="graph-view">
	<SvelteFlow
		{nodeTypes}
		bind:nodes
		bind:edges
		fitView
		minZoom={0.2}
		maxZoom={3}
		proOptions={{ hideAttribution: true }}
	>
		<Background />
		<Controls />
	</SvelteFlow>
</div>

<style>
	.graph-view {
		width: 100%;
		height: 600px;
		background: #ffffff;
		border: 1px solid #d8dbe2;
		border-radius: 6px;
	}
	.graph-view :global(.svelte-flow__edge-path) {
		stroke: #1c2233;
	}
	.graph-view :global(.svelte-flow__attribution) {
		display: none;
	}
	/* Strip Svelte Flow's default node chrome so the dot is the only
	   thing the user sees — no box, no border, no background. */
	.graph-view :global(.svelte-flow__node-dag) {
		padding: 0 !important;
		border: 0 !important;
		background: transparent !important;
		border-radius: 0 !important;
		box-shadow: none !important;
		width: auto !important;
		height: auto !important;
	}
	.graph-view :global(.svelte-flow__node-dag.selected) {
		box-shadow: 0 0 0 2px #1c223333 !important;
		border-radius: 50% !important;
	}
</style>
