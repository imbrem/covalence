/**
 * Decoder for the `covalence-graph` canonical byte format. Mirror of
 * `Graph::from_bytes` in `crates/covalence-graph/src/lib.rs`.
 *
 * Format (v1, see Rust crate's `to_bytes` doc-comment):
 *   "COVG" + version=1 + LEB128 node-count
 *   per node: kind-byte, LEB128 port-count, ports, LEB128 payload-len, payload
 *   per port: kind-byte, LEB128 u64 type-id, LEB128 name-len, utf-8 name
 *   LEB128 edge-count
 *   per edge: LEB128 from-node, from-port, to-node, to-port (u32)
 */

import type { Graph, GraphEdge, GraphNode, GraphPort, NodeKind, PortKind } from './types.js';

export const CANONICAL_MAGIC = new Uint8Array([0x43, 0x4f, 0x56, 0x47]); // "COVG"
export const CANONICAL_VERSION = 1;

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

function parsePortKind(b: number): PortKind {
	if (b === 0) return 'input';
	if (b === 1) return 'output';
	throw new Error(`bad port-kind byte: ${b}`);
}

function parseNodeKind(b: number): NodeKind {
	if (b === 0) return 'pure';
	if (b === 1) return 'ordered';
	throw new Error(`bad node-kind byte: ${b}`);
}

export function decodeGraph(data: Uint8Array): Graph {
	const c = new Cursor(data);
	const magic = c.take(4);
	if (magic.some((b, i) => b !== CANONICAL_MAGIC[i])) {
		throw new Error(`bad magic: expected "COVG", got ${Array.from(magic).join(',')}`);
	}
	const version = c.take(1)[0];
	if (version !== CANONICAL_VERSION) {
		throw new Error(`unsupported version: ${version} (this build understands v${CANONICAL_VERSION})`);
	}
	const nodeCount = c.readU32();
	const nodes: GraphNode[] = [];
	for (let n = 0; n < nodeCount; n++) {
		const kind = parseNodeKind(c.take(1)[0]);
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
		const payload = new Uint8Array(c.take(payloadLen)); // copy out of subarray
		const labelPresent = c.take(1)[0];
		let label: string | null = null;
		if (labelPresent === 1) {
			const labelLen = c.readU32();
			label = new TextDecoder('utf-8', { fatal: true }).decode(c.take(labelLen));
		} else if (labelPresent !== 0) {
			throw new Error(`bad label-present byte: ${labelPresent}`);
		}
		nodes.push({ kind, label, ports, payload });
	}
	const edgeCount = c.readU32();
	const edges: GraphEdge[] = [];
	for (let e = 0; e < edgeCount; e++) {
		const fromNode = c.readU32();
		const fromPort = c.readU32();
		const toNode = c.readU32();
		const toPort = c.readU32();
		edges.push({ fromNode, fromPort, toNode, toPort });
	}
	if (c.pos < data.length) {
		throw new Error(`trailing bytes: ${data.length - c.pos} extra bytes after canonical encoding`);
	}
	return { version, nodes, edges };
}

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
