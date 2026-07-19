/**
 * Decoders for the `cov:graph` blob family. Mirrors of the Rust
 * canonical-byte encoders in `crates/lib/graph`.
 *
 * Magics: `COVG` (graph topology), `LBLS` (label-list overlay),
 * `KFLG` (kind-flags overlay), `SDGM` (string-diagram composite).
 *
 * Consumers should generally compose `decodeStringDiagram` with an
 * overlay lookup function and then `resolveDiagram` to get a
 * `ResolvedDiagram` ready for the renderer.
 */

import type {
	Graph,
	GraphEdge,
	GraphNode,
	GraphPort,
	HashBytes,
	KindFlags,
	LabelList,
	NodeKind,
	PortKind,
	ResolvedDiagram,
	SlotRef,
	StringDiagram,
} from './types.js';

export const GRAPH_MAGIC = new Uint8Array([0x43, 0x4f, 0x56, 0x47]); // "COVG"
export const LABEL_LIST_MAGIC = new Uint8Array([0x4c, 0x42, 0x4c, 0x53]); // "LBLS"
export const KIND_FLAGS_MAGIC = new Uint8Array([0x4b, 0x46, 0x4c, 0x47]); // "KFLG"
export const STRING_DIAGRAM_MAGIC = new Uint8Array([0x53, 0x44, 0x47, 0x4d]); // "SDGM"

const SENTINEL_TAG_PREFIX = 0xff;
const SENTINEL_ALL_PURE = 1;
const SENTINEL_ALL_ORDERED = 2;

class Cursor {
	pos = 0;
	constructor(public data: Uint8Array) {}

	take(n: number): Uint8Array {
		if (this.data.length - this.pos < n) {
			throw new Error(
				`truncated: wanted ${n} bytes at offset ${this.pos}, only ${this.data.length - this.pos} left`,
			);
		}
		const out = this.data.subarray(this.pos, this.pos + n);
		this.pos += n;
		return out;
	}

	readU32(): number {
		let result = 0;
		let shift = 0;
		while (this.pos < this.data.length) {
			const byte = this.data[this.pos++];
			if (shift >= 32) throw new Error('LEB128 u32 overflow');
			result |= (byte & 0x7f) << shift;
			if ((byte & 0x80) === 0) return result >>> 0;
			shift += 7;
		}
		throw new Error('LEB128 truncated');
	}

	readU64(): bigint {
		let result = 0n;
		let shift = 0n;
		while (this.pos < this.data.length) {
			const byte = this.data[this.pos++];
			if (shift >= 64n) throw new Error('LEB128 u64 overflow');
			result |= BigInt(byte & 0x7f) << shift;
			if ((byte & 0x80) === 0) return result;
			shift += 7n;
		}
		throw new Error('LEB128 truncated');
	}
}

function startsWith(data: Uint8Array, magic: Uint8Array, offset = 0): boolean {
	if (data.length < magic.length + offset) return false;
	for (let i = 0; i < magic.length; i++) {
		if (data[i + offset] !== magic[i]) return false;
	}
	return true;
}

function expectMagic(c: Cursor, magic: Uint8Array, label: string): number {
	const got = c.take(4);
	for (let i = 0; i < magic.length; i++) {
		if (got[i] !== magic[i]) {
			throw new Error(`bad ${label} magic: got ${Array.from(got).join(',')}`);
		}
	}
	return c.take(1)[0];
}

function parsePortKind(b: number): PortKind {
	if (b === 0) return 'input';
	if (b === 1) return 'output';
	throw new Error(`bad port-kind byte: ${b}`);
}

// ---------- Graph topology ----------

export function decodeGraph(data: Uint8Array): Graph {
	const c = new Cursor(data);
	const version = expectMagic(c, GRAPH_MAGIC, 'graph');
	if (version !== 1) throw new Error(`unsupported graph version: ${version}`);
	const nodeCount = c.readU32();
	const nodes: GraphNode[] = [];
	for (let n = 0; n < nodeCount; n++) {
		const portCount = c.readU32();
		const ports: GraphPort[] = [];
		for (let p = 0; p < portCount; p++) {
			const portKind = parsePortKind(c.take(1)[0]);
			const typeId = c.readU64();
			const nameLen = c.readU32();
			const name = new TextDecoder('utf-8', { fatal: true }).decode(c.take(nameLen));
			ports.push({ name, typeId, kind: portKind });
		}
		const payloadLen = c.readU32();
		const payload = new Uint8Array(c.take(payloadLen));
		nodes.push({ ports, payload });
	}
	const edgeCount = c.readU32();
	const edges: GraphEdge[] = [];
	for (let e = 0; e < edgeCount; e++) {
		edges.push({
			fromNode: c.readU32(),
			fromPort: c.readU32(),
			toNode: c.readU32(),
			toPort: c.readU32(),
		});
	}
	if (c.pos < data.length) {
		throw new Error(`trailing bytes: ${data.length - c.pos} extra after graph encoding`);
	}
	return { version, nodes, edges };
}

// ---------- LabelList ----------

export function decodeLabelList(data: Uint8Array): LabelList {
	const c = new Cursor(data);
	const version = expectMagic(c, LABEL_LIST_MAGIC, 'label-list');
	if (version !== 1) throw new Error(`unsupported label-list version: ${version}`);
	const count = c.readU32();
	const labels: (string | null)[] = [];
	for (let i = 0; i < count; i++) {
		const presence = c.take(1)[0];
		if (presence === 0) {
			labels.push(null);
		} else if (presence === 1) {
			const len = c.readU32();
			labels.push(new TextDecoder('utf-8', { fatal: true }).decode(c.take(len)));
		} else {
			throw new Error(`bad label-presence byte: ${presence}`);
		}
	}
	if (c.pos < data.length) {
		throw new Error(`trailing bytes: ${data.length - c.pos} extra after label-list`);
	}
	return { labels };
}

// ---------- KindFlags ----------

export function decodeKindFlags(data: Uint8Array): KindFlags {
	const c = new Cursor(data);
	const version = expectMagic(c, KIND_FLAGS_MAGIC, 'kind-flags');
	if (version !== 1) throw new Error(`unsupported kind-flags version: ${version}`);
	const count = c.readU32();
	const bytes = Math.ceil(count / 8);
	const bits = c.take(bytes);
	if (c.pos < data.length) {
		throw new Error(`trailing bytes: ${data.length - c.pos} extra after kind-flags`);
	}
	const kinds: NodeKind[] = [];
	for (let i = 0; i < count; i++) {
		const set = (bits[i >> 3] & (1 << (i & 7))) !== 0;
		kinds.push(set ? 'ordered' : 'pure');
	}
	return { kinds };
}

// ---------- StringDiagram refs ----------

function decodeSlot(buf: Uint8Array): SlotRef {
	if (buf.every((b) => b === 0)) return { kind: 'absent' };
	if (buf[0] === SENTINEL_TAG_PREFIX) {
		const tag = buf[1];
		for (let i = 2; i < buf.length; i++) {
			if (buf[i] !== 0) throw new Error('slot sentinel has non-zero trailing bytes');
		}
		if (tag === SENTINEL_ALL_PURE) return { kind: 'uniform', tag: 'all-pure' };
		if (tag === SENTINEL_ALL_ORDERED) return { kind: 'uniform', tag: 'all-ordered' };
		throw new Error(`bad slot sentinel tag: ${tag}`);
	}
	return { kind: 'hash', hash: new Uint8Array(buf) };
}

export function decodeStringDiagram(data: Uint8Array): StringDiagram {
	const c = new Cursor(data);
	const version = expectMagic(c, STRING_DIAGRAM_MAGIC, 'string-diagram');
	if (version !== 1) throw new Error(`unsupported string-diagram version: ${version}`);
	const graph: HashBytes = new Uint8Array(c.take(32));
	const slotCount = c.readU32();
	if (slotCount < 2) throw new Error(`string-diagram needs ≥2 slots, got ${slotCount}`);
	const labels = decodeSlot(c.take(32));
	const kinds = decodeSlot(c.take(32));
	for (let i = 2; i < slotCount; i++) c.take(32);
	if (c.pos < data.length) {
		throw new Error(`trailing bytes: ${data.length - c.pos} extra after string-diagram`);
	}
	return { graph, labels, kinds };
}

// ---------- Magic sniffing ----------

export function magicOf(data: Uint8Array): 'graph' | 'label-list' | 'kind-flags' | 'string-diagram' | null {
	if (startsWith(data, GRAPH_MAGIC)) return 'graph';
	if (startsWith(data, LABEL_LIST_MAGIC)) return 'label-list';
	if (startsWith(data, KIND_FLAGS_MAGIC)) return 'kind-flags';
	if (startsWith(data, STRING_DIAGRAM_MAGIC)) return 'string-diagram';
	return null;
}

// ---------- Resolution ----------

/** Look up an overlay blob by its 32-byte hash. */
export type OverlayResolver = (hash: HashBytes) => Uint8Array | null;

function kindsFromSlot(slot: SlotRef, n: number, resolver: OverlayResolver): KindFlags {
	if (slot.kind === 'absent') {
		return { kinds: new Array(n).fill('pure') as NodeKind[] };
	}
	if (slot.kind === 'uniform') {
		const v: NodeKind = slot.tag === 'all-ordered' ? 'ordered' : 'pure';
		return { kinds: new Array(n).fill(v) as NodeKind[] };
	}
	const bytes = resolver(slot.hash);
	if (!bytes) throw new Error(`kind-flags overlay not found: ${hexOf(slot.hash)}`);
	const kf = decodeKindFlags(bytes);
	if (kf.kinds.length !== n) {
		throw new Error(`kind-flags length ${kf.kinds.length} ≠ graph nodes ${n}`);
	}
	return kf;
}

function labelsFromSlot(slot: SlotRef, n: number, resolver: OverlayResolver): LabelList | null {
	if (slot.kind === 'absent' || slot.kind === 'uniform') return null;
	const bytes = resolver(slot.hash);
	if (!bytes) throw new Error(`label-list overlay not found: ${hexOf(slot.hash)}`);
	const ll = decodeLabelList(bytes);
	if (ll.labels.length !== n) {
		throw new Error(`label-list length ${ll.labels.length} ≠ graph nodes ${n}`);
	}
	return ll;
}

/**
 * Resolve a string diagram against a graph and an overlay resolver.
 * The graph hash on the diagram is *not* re-verified here — callers are
 * expected to fetch the graph by the same hash referenced in the diagram.
 */
export function resolveDiagram(
	diagram: StringDiagram,
	graph: Graph,
	resolver: OverlayResolver,
): ResolvedDiagram {
	const n = graph.nodes.length;
	return {
		graph,
		labels: labelsFromSlot(diagram.labels, n, resolver),
		kinds: kindsFromSlot(diagram.kinds, n, resolver),
	};
}

/** A convenience resolver from a `Map<hex, bytes>`. */
export function mapResolver(map: Map<string, Uint8Array>): OverlayResolver {
	return (h: HashBytes) => map.get(hexOf(h)) ?? null;
}

/** Wrap a topology-only graph as a default-rendered diagram. */
export function diagramFromGraphOnly(graph: Graph): ResolvedDiagram {
	return {
		graph,
		labels: null,
		kinds: { kinds: new Array(graph.nodes.length).fill('pure') as NodeKind[] },
	};
}

// ---------- Misc ----------

/** Parse a hex string (whitespace allowed) into bytes. */
export function hexToBytes(hex: string): Uint8Array {
	const clean = hex.replace(/\s+/g, '').replace(/^0x/, '');
	if (clean.length % 2 !== 0) throw new Error('odd-length hex');
	const out = new Uint8Array(clean.length / 2);
	for (let i = 0; i < out.length; i++) {
		const v = parseInt(clean.substring(i * 2, i * 2 + 2), 16);
		if (Number.isNaN(v)) throw new Error(`bad hex at byte ${i}: ${clean.substring(i * 2, i * 2 + 2)}`);
		out[i] = v;
	}
	return out;
}

export function hexOf(bytes: Uint8Array): string {
	let s = '';
	for (let i = 0; i < bytes.length; i++) {
		s += bytes[i].toString(16).padStart(2, '0');
	}
	return s;
}
