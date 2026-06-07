/**
 * Layout for the string-diagram view.
 *
 * Convention: **top-to-bottom**, like a page of text. NodeId N is
 * placed in lane N reading downward. Inputs always sit on the top
 * edge of each box; outputs always on the bottom. Wires flow
 * top→bottom, from an output port to an input port.
 *
 * Ordered nodes carry an implicit **state thread**: a dashed red
 * "state in" port on the top edge (leftmost slot) and "state out"
 * on the bottom edge. Consecutive ordered nodes (in insertion
 * order) are linked by a dashed red wire between their state ports.
 * The first ordered node gets a short stub coming in from above,
 * and the last one a stub going out below — the dashed red wire
 * is the only visual indicator of statefulness.
 */

import type { Graph, GraphNode } from './types.js';

export interface LayoutOpts {
	boxW: number;
	boxH: number;
	dataPortMinSep: number;
	rowH: number;
	marginX: number;
	marginY: number;
	stateStubLen: number;
	stateSlotPad: number;
}

export const DEFAULT_LAYOUT: LayoutOpts = {
	boxW: 180,
	boxH: 50,
	dataPortMinSep: 36,
	rowH: 130,
	marginX: 60,
	marginY: 60,
	stateStubLen: 36,
	stateSlotPad: 22,
};

export interface NodeBox {
	id: number;
	x: number;
	y: number;
	w: number;
	h: number;
	inputs: PortAnchor[];
	outputs: PortAnchor[];
	stateIn: { x: number; y: number } | null;
	stateOut: { x: number; y: number } | null;
	kind: 'pure' | 'ordered';
	label: string;
}

export interface PortAnchor {
	nodeId: number;
	portIdx: number;
	x: number;
	y: number;
	name: string;
	typeId: bigint;
}

export interface StateSegment {
	kind: 'segment' | 'head' | 'tail';
	from: { x: number; y: number };
	to: { x: number; y: number };
}

export interface LaidOutGraph {
	boxes: NodeBox[];
	width: number;
	height: number;
	stateSegments: StateSegment[];
}

function labelFor(node: GraphNode, id: number): string {
	if (node.label && node.label.length > 0) return node.label;
	const p = node.payload;
	if (p.length > 0 && p.length <= 24) {
		try {
			const s = new TextDecoder('utf-8', { fatal: true }).decode(p);
			if (/^[\x20-\x7e]+$/.test(s)) return s;
		} catch {
			// fall through
		}
	}
	return `#${id}`;
}

export function layoutGraph(graph: Graph, opts: LayoutOpts = DEFAULT_LAYOUT): LaidOutGraph {
	const boxes: NodeBox[] = [];

	for (let i = 0; i < graph.nodes.length; i++) {
		const node = graph.nodes[i];
		const inputs = node.ports.filter((p) => p.kind === 'input');
		const outputs = node.ports.filter((p) => p.kind === 'output');
		const isOrdered = node.kind === 'ordered';

		// Reserve the leftmost slot on each edge for the state port,
		// when this node is ordered.
		const dataPortCount = Math.max(inputs.length, outputs.length, 1);
		const dataAreaMin = dataPortCount * opts.dataPortMinSep + 32;
		const baseW = isOrdered ? dataAreaMin + opts.stateSlotPad : dataAreaMin;
		const w = Math.max(opts.boxW, baseW);
		const h = opts.boxH;

		const x = opts.marginX;
		const y = opts.marginY + i * opts.rowH;

		const dataLeftEdge = isOrdered ? x + opts.stateSlotPad : x;
		const dataAreaW = w - (isOrdered ? opts.stateSlotPad : 0);

		const box: NodeBox = {
			id: i,
			x,
			y,
			w,
			h,
			inputs: [],
			outputs: [],
			stateIn: isOrdered ? { x: x + opts.stateSlotPad / 2, y } : null,
			stateOut: isOrdered ? { x: x + opts.stateSlotPad / 2, y: y + h } : null,
			kind: node.kind,
			label: labelFor(node, i),
		};

		let inI = 0;
		let outI = 0;
		for (let pi = 0; pi < node.ports.length; pi++) {
			const port = node.ports[pi];
			if (port.kind === 'input') {
				const slot = (inI + 1) / (inputs.length + 1);
				box.inputs.push({
					nodeId: i,
					portIdx: pi,
					x: dataLeftEdge + slot * dataAreaW,
					y,
					name: port.name,
					typeId: port.typeId,
				});
				inI++;
			} else {
				const slot = (outI + 1) / (outputs.length + 1);
				box.outputs.push({
					nodeId: i,
					portIdx: pi,
					x: dataLeftEdge + slot * dataAreaW,
					y: y + h,
					name: port.name,
					typeId: port.typeId,
				});
				outI++;
			}
		}

		boxes.push(box);
	}

	// State wire: stub above first ordered, beziers between consecutive,
	// stub below last ordered.
	const orderedIds: number[] = [];
	for (let i = 0; i < graph.nodes.length; i++) {
		if (graph.nodes[i].kind === 'ordered') orderedIds.push(i);
	}
	const stateSegments: StateSegment[] = [];
	if (orderedIds.length > 0) {
		const firstBox = boxes[orderedIds[0]];
		if (firstBox.stateIn) {
			stateSegments.push({
				kind: 'head',
				from: { x: firstBox.stateIn.x, y: firstBox.stateIn.y - opts.stateStubLen },
				to: firstBox.stateIn,
			});
		}
		for (let i = 1; i < orderedIds.length; i++) {
			const a = boxes[orderedIds[i - 1]];
			const b = boxes[orderedIds[i]];
			if (a.stateOut && b.stateIn) {
				stateSegments.push({ kind: 'segment', from: a.stateOut, to: b.stateIn });
			}
		}
		const lastBox = boxes[orderedIds[orderedIds.length - 1]];
		if (lastBox.stateOut) {
			stateSegments.push({
				kind: 'tail',
				from: lastBox.stateOut,
				to: { x: lastBox.stateOut.x, y: lastBox.stateOut.y + opts.stateStubLen },
			});
		}
	}

	const maxBoxW = boxes.reduce((m, b) => Math.max(m, b.w), opts.boxW);
	const width = opts.marginX * 2 + maxBoxW;
	const lastH = boxes.length > 0 ? boxes[boxes.length - 1].h : 0;
	const height =
		boxes.length > 0 ? opts.marginY * 2 + (boxes.length - 1) * opts.rowH + lastH : opts.marginY * 2;
	return { boxes, width, height, stateSegments };
}
