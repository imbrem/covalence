<script lang="ts">
	import { Handle, Position, type NodeProps } from '@xyflow/svelte';

	/**
	 * Invisible 8×8 anchor for state-thread stubs above the first
	 * ordered node and below the last ordered node. Sized and positioned
	 * so the handle's connection point lines up exactly with the
	 * StringDiagramNode's state-handle visual center (also 8×8 with
	 * `left: -10px`).
	 */
	type AnchorData = { role: 'head' | 'tail' };
	let { data }: NodeProps & { data: AnchorData } = $props();
</script>

<div class="state-anchor">
	{#if data.role === 'head'}
		<Handle type="source" position={Position.Bottom} id="state-out" class="anchor-handle" />
	{:else}
		<Handle type="target" position={Position.Top} id="state-in" class="anchor-handle" />
	{/if}
</div>

<style>
	.state-anchor {
		width: 8px;
		height: 8px;
		opacity: 0;
		pointer-events: none;
	}
	.state-anchor :global(.anchor-handle) {
		background: transparent;
		border: none;
		width: 8px;
		height: 8px;
	}
</style>
