<script lang="ts">
	import { Handle, Position, type NodeProps } from '@xyflow/svelte';

	type DiagramNodeData = {
		label: string;
		kind: 'pure' | 'ordered';
		inputs: { idx: number; name: string }[];
		outputs: { idx: number; name: string }[];
	};

	let { data }: NodeProps & { data: DiagramNodeData } = $props();

	// Evenly distribute n handles across the data area. Symmetric padding
	// at both ends so layout doesn't drift toward one side regardless of
	// whether the node is pure or ordered (the state handle lives outside
	// the box on the left, not in the data area).
	function slot(i: number, n: number): string {
		const pad = 8;
		const usable = 100 - 2 * pad;
		const frac = (i + 1) / (n + 1);
		return `${pad + usable * frac}%`;
	}
</script>

<div class="diagram-node" class:ordered={data.kind === 'ordered'}>
	<!-- State thread: lives OUTSIDE the box on the left edge so it
	     doesn't shift the data port distribution. Only rendered for
	     ordered nodes. -->
	{#if data.kind === 'ordered'}
		<Handle
			type="target"
			position={Position.Top}
			id="state-in"
			class="state-handle"
			style="left: -10px;"
		/>
	{/if}

	<!-- Data input handles (top edge). -->
	{#each data.inputs as input, i (input.idx)}
		<Handle
			type="target"
			position={Position.Top}
			id={`in-${input.idx}`}
			style={`left: ${slot(i, data.inputs.length)};`}
		/>
	{/each}

	<span class="label">{data.label}</span>

	<!-- Data output handles (bottom edge). -->
	{#each data.outputs as output, i (output.idx)}
		<Handle
			type="source"
			position={Position.Bottom}
			id={`out-${output.idx}`}
			style={`left: ${slot(i, data.outputs.length)};`}
		/>
	{/each}

	{#if data.kind === 'ordered'}
		<Handle
			type="source"
			position={Position.Bottom}
			id="state-out"
			class="state-handle"
			style="left: -10px;"
		/>
	{/if}
</div>

<style>
	.diagram-node {
		font-family: ui-monospace, SFMono-Regular, Menlo, monospace;
		font-size: 12px;
		padding: 10px 14px;
		min-width: 130px;
		text-align: center;
		background: #ffffff;
		color: #1c2233;
		border: 1.25px solid #1c2233;
		border-radius: 4px;
		position: relative;
	}
	.label {
		font-weight: 500;
	}
	/* State-thread handles: dashed red, sitting just outside the box
	   on its left edge. Background transparent so the dashed border is
	   the only thing visible. */
	.diagram-node :global(.state-handle) {
		background: transparent;
		border: 1.5px dashed #c43030;
		width: 8px;
		height: 8px;
	}
</style>
