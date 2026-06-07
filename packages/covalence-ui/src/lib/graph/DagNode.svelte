<script lang="ts">
	import { Handle, Position, type NodeProps } from '@xyflow/svelte';

	/** Plain DAG node: a small filled circle with the node id as a tooltip. */
	type DagNodeData = { id: number; label: string; in: number; out: number };
	let { data }: NodeProps & { data: DagNodeData } = $props();
</script>

<div class="dag-node" title={`#${data.id} (in:${data.in} out:${data.out})`}>
	<Handle type="target" position={Position.Top} id="t" class="dag-handle" />
	<span class="id">{data.id}</span>
	<Handle type="source" position={Position.Bottom} id="s" class="dag-handle" />
</div>

<style>
	.dag-node {
		width: 22px;
		height: 22px;
		border-radius: 50%;
		background: #1c2233;
		color: #ffffff;
		display: flex;
		align-items: center;
		justify-content: center;
		font-family: ui-monospace, SFMono-Regular, Menlo, monospace;
		font-size: 10px;
		border: 1px solid #1c2233;
		cursor: default;
	}
	.id {
		user-select: none;
	}
	.dag-node :global(.dag-handle) {
		width: 6px;
		height: 6px;
		background: transparent;
		border: none;
	}
</style>
