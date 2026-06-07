<script lang="ts">
	import { Handle, Position, type NodeProps } from '@xyflow/svelte';

	type DiagramNodeData = {
		label: string;
		kind: 'pure' | 'ordered';
		inputs: { idx: number; name: string }[];
		outputs: { idx: number; name: string }[];
	};

	let { data }: NodeProps & { data: DiagramNodeData } = $props();

	// Distribute n handles evenly across an edge — gives slots at
	// 1/(n+1), 2/(n+1), … n/(n+1). For ordered nodes we reserve a
	// leftmost slot for the state handle, so data handles start at
	// about 20% from the left.
	function slot(i: number, n: number, leftPad: number): string {
		const usable = 100 - leftPad;
		const frac = (i + 1) / (n + 1);
		return `${leftPad + usable * frac}%`;
	}
	let dataLeftPad = $derived(data.kind === 'ordered' ? 18 : 8);
</script>

<div class="diagram-node" class:ordered={data.kind === 'ordered'}>
	<!-- State thread (top): only on ordered nodes. Targets get a
		 dashed red marker via edge styling. -->
	{#if data.kind === 'ordered'}
		<Handle
			type="target"
			position={Position.Top}
			id="state-in"
			style="left: 10px; background: transparent; border: 1.5px dashed #c43030;"
		/>
	{/if}

	<!-- Data input handles (top edge). -->
	{#each data.inputs as input, i (input.idx)}
		<Handle
			type="target"
			position={Position.Top}
			id={`in-${input.idx}`}
			style={`left: ${slot(i, data.inputs.length, dataLeftPad)};`}
		/>
	{/each}

	<span class="label">{data.label}</span>

	<!-- Data output handles (bottom edge). -->
	{#each data.outputs as output, i (output.idx)}
		<Handle
			type="source"
			position={Position.Bottom}
			id={`out-${output.idx}`}
			style={`left: ${slot(i, data.outputs.length, dataLeftPad)};`}
		/>
	{/each}

	{#if data.kind === 'ordered'}
		<Handle
			type="source"
			position={Position.Bottom}
			id="state-out"
			style="left: 10px; background: transparent; border: 1.5px dashed #c43030;"
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
	}
	.label {
		font-weight: 500;
	}
</style>
