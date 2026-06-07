<script lang="ts">
	import { BaseEdge, type EdgeProps } from '@xyflow/svelte';

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

	// Layout constants must match LayoutOpts so we can identify how many
	// intermediate boxes the edge passes over. Kept here as constants
	// rather than threaded through props since they're already implicit
	// in the diagram's geometry.
	const ROW_H = 130;
	const BOX_H = 50;

	function curvyPath(): string {
		const dy = Math.abs(targetY - sourceY);
		const rowsSpan = Math.round((dy + BOX_H) / ROW_H);
		const intermediates = Math.max(0, rowsSpan - 1);
		// Big enough to clear a 180-wide box plus margin; scales with
		// how many boxes we need to skip.
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
