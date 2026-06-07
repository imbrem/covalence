/**
 * Simple layered layout for DAG visualisation.
 *
 * Algorithm: longest-path ranking via Kahn's topological sort. Nodes
 * with no incoming edges go in rank 0; every other node sits one rank
 * below the rank of its highest-ranked predecessor. Within each rank,
 * nodes are distributed evenly around the column centre.
 *
 * Used by `GraphDagView` to give a more standard interactive DAG look
 * than the single-column layout the string-diagram view uses. Nodes
 * remain draggable in Svelte Flow — these positions are just the
 * initial placement.
 */

import type { Graph } from './types.js';

export interface DagLayoutOpts {
	/** Horizontal spacing between sibling nodes in the same rank. */
	colW: number;
	/** Vertical spacing between ranks. */
	rowH: number;
	/** X coordinate of the column centre. */
	centerX: number;
	/** Top margin. */
	startY: number;
}

export const DEFAULT_DAG_LAYOUT: DagLayoutOpts = {
	colW: 90,
	rowH: 110,
	centerX: 280,
	startY: 40,
};

export interface DagLayoutResult {
	positions: { x: number; y: number }[];
	rankOf: number[];
}

export function layeredDagLayout(graph: Graph, opts: DagLayoutOpts = DEFAULT_DAG_LAYOUT): DagLayoutResult {
	const n = graph.nodes.length;
	if (n === 0) return { positions: [], rankOf: [] };

	// Build successor list and in-degree, skipping self-loops.
	const inDeg = new Array<number>(n).fill(0);
	const succ: number[][] = Array.from({ length: n }, () => []);
	for (const e of graph.edges) {
		if (e.fromNode === e.toNode) continue;
		succ[e.fromNode].push(e.toNode);
		inDeg[e.toNode]++;
	}

	// Kahn's topological sort. Longest-path rank = max over predecessors.
	const rank = new Array<number>(n).fill(0);
	const remaining = inDeg.slice();
	const queue: number[] = [];
	for (let i = 0; i < n; i++) {
		if (remaining[i] === 0) queue.push(i);
	}
	while (queue.length > 0) {
		const v = queue.shift()!;
		for (const u of succ[v]) {
			if (rank[u] < rank[v] + 1) rank[u] = rank[v] + 1;
			remaining[u]--;
			if (remaining[u] === 0) queue.push(u);
		}
	}
	// Cycle fallback: any node we couldn't reach (remaining > 0) goes
	// one rank below whatever we've placed so far. Insertion order
	// breaks ties.
	let maxRank = 0;
	for (let i = 0; i < n; i++) maxRank = Math.max(maxRank, rank[i]);
	for (let i = 0; i < n; i++) {
		if (remaining[i] > 0) rank[i] = ++maxRank;
	}

	// Group by rank, preserving insertion order within each rank for
	// determinism (no crossing minimisation yet — fine for small graphs).
	const byRank = new Map<number, number[]>();
	for (let i = 0; i < n; i++) {
		const r = rank[i];
		const list = byRank.get(r);
		if (list) list.push(i);
		else byRank.set(r, [i]);
	}

	const positions: { x: number; y: number }[] = new Array(n);
	const ranks = [...byRank.keys()].sort((a, b) => a - b);
	for (const r of ranks) {
		const ids = byRank.get(r)!;
		const totalW = (ids.length - 1) * opts.colW;
		const startX = opts.centerX - totalW / 2;
		for (let i = 0; i < ids.length; i++) {
			positions[ids[i]] = { x: startX + i * opts.colW, y: opts.startY + r * opts.rowH };
		}
	}
	return { positions, rankOf: rank };
}
