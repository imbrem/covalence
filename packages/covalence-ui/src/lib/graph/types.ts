/**
 * TypeScript mirrors of the `covalence-graph` Rust types. The shape
 * matches what `Graph.snapshot()` returns from the Python binding
 * AND what the canonical-byte decoder produces.
 *
 * Magic "COVG", version 1.
 */

export type PortKind = 'input' | 'output';
export type NodeKind = 'pure' | 'ordered';

export interface GraphPort {
	name: string;
	/** Opaque u64. Graph only checks equality. */
	typeId: bigint;
	kind: PortKind;
}

export interface GraphNode {
	kind: NodeKind;
	/** Optional free-form label. Preferred over payload for display. */
	label: string | null;
	ports: GraphPort[];
	/** Opaque payload bytes. */
	payload: Uint8Array;
}

export interface GraphEdge {
	fromNode: number;
	fromPort: number;
	toNode: number;
	toPort: number;
}

export interface Graph {
	version: number;
	nodes: GraphNode[];
	edges: GraphEdge[];
}
