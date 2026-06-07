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
	import StringDiagramNode from './StringDiagramNode.svelte';

	interface Props {
		graph: Graph;
	}
	let { graph }: Props = $props();

	const ROW_H = 130;
	const COL_X = 60;

	const nodeTypes = { stringDiagram: StringDiagramNode };

	let nodes = $state<Node[]>([]);
	let edges = $state<Edge[]>([]);

	$effect(() => {
		const orderedIds: number[] = [];
		nodes = graph.nodes.map((node, i) => {
			if (node.kind === 'ordered') orderedIds.push(i);
			const inputs = node.ports
				.map((p, idx) => ({ p, idx }))
				.filter(({ p }) => p.kind === 'input')
				.map(({ p, idx }) => ({ idx, name: p.name }));
			const outputs = node.ports
				.map((p, idx) => ({ p, idx }))
				.filter(({ p }) => p.kind === 'output')
				.map(({ p, idx }) => ({ idx, name: p.name }));
			return {
				id: `n${i}`,
				type: 'stringDiagram',
				position: { x: COL_X, y: i * ROW_H },
				data: {
					label: node.label && node.label.length > 0 ? node.label : `#${i}`,
					kind: node.kind,
					inputs,
					outputs,
				},
				draggable: true,
			};
		});

		const dataEdges: Edge[] = graph.edges.map((e, i) => ({
			id: `e${i}`,
			source: `n${e.fromNode}`,
			target: `n${e.toNode}`,
			sourceHandle: `out-${e.fromPort}`,
			targetHandle: `in-${e.toPort}`,
			type: 'default',
			style: 'stroke: #1c2233; stroke-width: 1.5;',
		}));

		const stateEdges: Edge[] = [];
		for (let i = 1; i < orderedIds.length; i++) {
			const from = orderedIds[i - 1];
			const to = orderedIds[i];
			stateEdges.push({
				id: `s${from}-${to}`,
				source: `n${from}`,
				target: `n${to}`,
				sourceHandle: 'state-out',
				targetHandle: 'state-in',
				type: 'default',
				style: 'stroke: #c43030; stroke-width: 1.5; stroke-dasharray: 5 4;',
			});
		}
		edges = [...dataEdges, ...stateEdges];
	});
</script>

<div class="graph-view">
	<SvelteFlow
		{nodeTypes}
		bind:nodes
		bind:edges
		fitView
		minZoom={0.2}
		maxZoom={2}
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
	.graph-view :global(.svelte-flow__handle) {
		width: 8px;
		height: 8px;
		background: #1c2233;
		border: none;
	}
	.graph-view :global(.svelte-flow__edge-path) {
		stroke: #1c2233;
	}
	.graph-view :global(.svelte-flow__attribution) {
		display: none;
	}
</style>
