/**
 * TypeScript mirrors of the Rust types in `crates/lib/graph`.
 *
 * Three layers, matching the Rust split:
 * - `Graph` / `GraphNode` / `GraphPort` / `GraphEdge` : pure topology.
 *   Wire format magic "COVG".
 * - `LabelList`, `KindFlags` : independent overlay blobs.
 *   Wire format magics "LBLS", "KFLG".
 * - `StringDiagram` : a composite of (graph hash, labels slot, kinds slot).
 *   Wire format magic "SDGM". Slots are 32-byte fields; an all-zero slot
 *   means "absent" and a `0xFF`-prefixed slot encodes a uniform sentinel
 *   (all-pure or all-ordered).
 * - `ResolvedDiagram` : the rendering input — a graph with overlays inlined.
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

// --------- Overlays ---------

export interface LabelList {
	labels: (string | null)[];
}

export interface KindFlags {
	kinds: NodeKind[];
}

// --------- StringDiagram ---------

/** A 32-byte content hash. */
export type Hash = Uint8Array;

export type SlotRef =
	| { kind: 'absent' }
	| { kind: 'uniform'; tag: 'all-pure' | 'all-ordered' }
	| { kind: 'hash'; hash: Hash };

export interface StringDiagram {
	/** Ordered-domain hash of the underlying topology. */
	graph: Hash;
	labels: SlotRef;
	kinds: SlotRef;
}

// --------- Resolved view consumed by the renderer ---------

export interface ResolvedDiagram {
	graph: Graph;
	labels: LabelList | null;
	kinds: KindFlags;
}
