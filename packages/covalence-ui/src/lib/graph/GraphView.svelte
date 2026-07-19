<script lang="ts">
	import {
		SvelteFlow,
		Background,
		Controls,
		type Node,
		type Edge,
	} from '@xyflow/svelte';
	import '@xyflow/svelte/dist/style.css';
	import type { ResolvedDiagram } from './types.js';
	import { DEFAULT_LAYOUT, layoutDiagram } from './layout.js';
	import StringDiagramNode from './StringDiagramNode.svelte';
	import StateAnchorNode from './StateAnchorNode.svelte';
	import CurvyEdge from './CurvyEdge.svelte';

	interface Props {
		diagram: ResolvedDiagram;
	}
	let { diagram }: Props = $props();

	const nodeTypes = { stringDiagram: StringDiagramNode, stateAnchor: StateAnchorNode };
	const edgeTypes = { curvy: CurvyEdge };

	let nodes = $state<Node[]>([]);
	let edges = $state<Edge[]>([]);

	// State-handle geometry: StringDiagramNode's state handles are 8×8
	// with `left: -10px` so their visual centers sit at (box.x - 6,
	// box.y) and (box.x - 6, box.y + h). The anchor nodes are also 8×8;
	// we position them so their bottom-center (head) or top-center
	// (tail) lines up exactly with the box state-handle center.
	// Same stub length layoutDiagram used for the head/tail state segments —
	// the anchors have to land on the ends of the stubs it drew.
	const STUB_LEN = DEFAULT_LAYOUT.stateStubLen;
	const ANCHOR_SIZE = 8;
	// anchor.x = box.x - 6 (target handle center x) - ANCHOR_SIZE/2.
	const ANCHOR_X_OFFSET = -6 - ANCHOR_SIZE / 2; // = -10

	$effect(() => {
		const laid = layoutDiagram(diagram);
		const orderedIds: number[] = [];
		for (let i = 0; i < diagram.kinds.kinds.length; i++) {
			if (diagram.kinds.kinds[i] === 'ordered') orderedIds.push(i);
		}

		const realNodes: Node[] = laid.boxes.map((box) => ({
			id: `n${box.id}`,
			type: 'stringDiagram',
			position: { x: box.x, y: box.y },
			data: {
				label: box.label,
				kind: box.kind,
				inputs: box.inputs.map((p) => ({ idx: p.portIdx, name: p.name })),
				outputs: box.outputs.map((p) => ({ idx: p.portIdx, name: p.name })),
			},
			draggable: true,
		}));

		const anchorNodes: Node[] = [];
		if (orderedIds.length > 0) {
			const firstBox = laid.boxes[orderedIds[0]];
			const lastBox = laid.boxes[orderedIds[orderedIds.length - 1]];
			anchorNodes.push({
				id: 'state-head',
				type: 'stateAnchor',
				position: {
					x: firstBox.x + ANCHOR_X_OFFSET,
					// anchor.bottom-center y = firstBox.y - STUB_LEN
					// anchor.y = firstBox.y - STUB_LEN - ANCHOR_SIZE
					y: firstBox.y - STUB_LEN - ANCHOR_SIZE,
				},
				data: { role: 'head' },
				draggable: false,
				selectable: false,
			});
			anchorNodes.push({
				id: 'state-tail',
				type: 'stateAnchor',
				position: {
					x: lastBox.x + ANCHOR_X_OFFSET,
					// anchor.top-center y = lastBox.y + lastBox.h + STUB_LEN
					y: lastBox.y + lastBox.h + STUB_LEN,
				},
				data: { role: 'tail' },
				draggable: false,
				selectable: false,
			});
		}
		nodes = [...realNodes, ...anchorNodes];

		const dataEdges: Edge[] = diagram.graph.edges.map((e, i) => {
			const fromBox = laid.boxes[e.fromNode];
			const sourcePort = fromBox.outputs.find((p) => p.portIdx === e.fromPort);
			const centerX = fromBox.x + fromBox.w / 2;
			const side: 'left' | 'right' =
				sourcePort && sourcePort.x < centerX ? 'left' : 'right';
			return {
				id: `e${i}`,
				source: `n${e.fromNode}`,
				target: `n${e.toNode}`,
				sourceHandle: `out-${e.fromPort}`,
				targetHandle: `in-${e.toPort}`,
				type: 'curvy',
				data: { side },
				style: 'stroke: #1c2233; stroke-width: 1.5;',
			};
		});

		const stateStyle = 'stroke: #c43030; stroke-width: 1.5; stroke-dasharray: 5 4;';
		const stateEdges: Edge[] = [];
		if (orderedIds.length > 0) {
			// Head stub: anchor → first ordered.
			stateEdges.push({
				id: 's-head',
				source: 'state-head',
				target: `n${orderedIds[0]}`,
				sourceHandle: 'state-out',
				targetHandle: 'state-in',
				type: 'straight',
				style: stateStyle,
			});
			// Segments between consecutive ordered nodes.
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
					style: stateStyle,
				});
			}
			// Tail stub: last ordered → anchor.
			stateEdges.push({
				id: 's-tail',
				source: `n${orderedIds[orderedIds.length - 1]}`,
				target: 'state-tail',
				sourceHandle: 'state-out',
				targetHandle: 'state-in',
				type: 'straight',
				style: stateStyle,
			});
		}
		edges = [...dataEdges, ...stateEdges];
	});
</script>

<div class="graph-view">
	<SvelteFlow
		{nodeTypes}
		{edgeTypes}
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
