<script lang="ts">
	import { BaseEdge, type EdgeProps } from '@xyflow/svelte';
	import { DEFAULT_LAYOUT } from './layout.js';

	/**
	 * String-diagram edge: bezier with a horizontal bulge so wires
	 * spanning multiple rows curl around intervening boxes instead of
	 * passing through them.
	 *
	 * `data.side` ('left' | 'right') picks which side the bulge goes;
	 * the parent component picks it based on the source port's
	 * position relative to the box center, so edges from rightward
	 * ports naturally exit to the right.
	 */
	type Side = 'left' | 'right';
	type CurvyData = { side: Side };

	let {
		id,
		sourceX,
		sourceY,
		targetX,
		targetY,
		markerEnd,
		style,
		data,
	}: EdgeProps & { data?: CurvyData } = $props();

	// Row/box geometry is read off DEFAULT_LAYOUT rather than restated here:
	// GraphView lays every diagram out with the default opts, so these are the
	// same numbers the boxes were placed with. Edges get only endpoint coords
	// from svelte-flow, so the geometry has to be recovered, not threaded.
	const { rowH: ROW_H, boxH: BOX_H } = DEFAULT_LAYOUT;

	function curvyPath(): string {
		const dy = Math.abs(targetY - sourceY);
		const rowsSpan = Math.round((dy + BOX_H) / ROW_H);
		const intermediates = Math.max(0, rowsSpan - 1);
		// Big enough to clear a default-width (DEFAULT_LAYOUT.boxW) box plus
		// margin; scales with how many boxes we need to skip. Tuned, not
		// derived — a wider boxW would want a matching retune.
		const bulge =
			intermediates > 0 ? 110 + (intermediates - 1) * 50 : Math.max(20, dy * 0.25);
		const sign = data?.side === 'left' ? -1 : 1;
		const hx = bulge * sign;
		const cp1x = sourceX + hx;
		const cp1y = sourceY + dy * 0.35;
		const cp2x = targetX + hx;
		const cp2y = targetY - dy * 0.35;
		return `M ${sourceX},${sourceY} C ${cp1x},${cp1y} ${cp2x},${cp2y} ${targetX},${targetY}`;
	}

	let edgePath = $derived(curvyPath());
</script>

<BaseEdge {id} path={edgePath} {markerEnd} {style} />
