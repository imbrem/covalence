import { describe, it, expect } from 'vitest';
import {
	decodeGraph,
	decodeStringDiagram,
	decodeLabelList,
	decodeKindFlags,
	resolveDiagram,
	hexToBytes,
	hexOf,
	GRAPH_MAGIC,
	LABEL_LIST_MAGIC,
	KIND_FLAGS_MAGIC,
	STRING_DIAGRAM_MAGIC,
	magicOf,
} from './decode.js';
import type { HashBytes } from './types.js';

describe('magic sniffing', () => {
	it('recognises every graph-family magic', () => {
		expect(magicOf(GRAPH_MAGIC)).toBe('graph');
		expect(magicOf(LABEL_LIST_MAGIC)).toBe('label-list');
		expect(magicOf(KIND_FLAGS_MAGIC)).toBe('kind-flags');
		expect(magicOf(STRING_DIAGRAM_MAGIC)).toBe('string-diagram');
		expect(magicOf(new Uint8Array([0, 1, 2, 3]))).toBeNull();
	});
});

// Graph bytes built with the new pure-topology canonical encoding:
//   #0  one output  type 1
//   #1  one input type 1, one output type 2
//   #2  one input  type 2
// In LEB128 + utf-8:
//   "COVG" 01 03                  (3 nodes)
//   node 0: 01 01 01 6f 00 03 73 72 63                  ports=1, output "o" t=1, payload="src"
//   node 1: 02 00 01 69 01 01 01 6f 02 06 65 66 66 65 63 74   ports=2, payload="effect"
//   node 2: 01 00 01 69 02 04 73 69 6e 6b               ports=1, input "i" t=2, payload="sink"
// Edges: 02 ...
// Easier to construct programmatically here than maintain a hex fixture:

function buildExampleGraphBytes(): Uint8Array {
	const out: number[] = [];
	out.push(...Array.from(GRAPH_MAGIC));
	out.push(1); // version
	out.push(3); // node count
	// node 0
	out.push(1); // 1 port
	out.push(1); // output kind
	out.push(1); // type id (LEB128 u64, single byte)
	out.push(1, 0x6f); // name "o"
	out.push(3, 0x73, 0x72, 0x63); // payload "src"
	// node 1
	out.push(2); // 2 ports
	out.push(0, 1, 1, 0x69); // input "i", type 1
	out.push(1, 2, 1, 0x6f); // output "o", type 2
	out.push(6, 0x65, 0x66, 0x66, 0x65, 0x63, 0x74); // payload "effect"
	// node 2
	out.push(1);
	out.push(0, 2, 1, 0x69); // input "i", type 2
	out.push(4, 0x73, 0x69, 0x6e, 0x6b); // payload "sink"
	// edges
	out.push(2); // 2 edges
	out.push(0, 0, 1, 0); // 0:0 -> 1:0
	out.push(1, 1, 2, 0); // 1:1 -> 2:0
	return new Uint8Array(out);
}

describe('decodeGraph', () => {
	it('decodes the example graph', () => {
		const g = decodeGraph(buildExampleGraphBytes());
		expect(g.version).toBe(1);
		expect(g.nodes).toHaveLength(3);
		expect(g.edges).toHaveLength(2);
		expect(g.nodes[0].ports[0].kind).toBe('output');
		expect(g.nodes[1].ports[1].name).toBe('o');
		expect(g.edges[1]).toEqual({ fromNode: 1, fromPort: 1, toNode: 2, toPort: 0 });
	});

	it('rejects bad magic', () => {
		const bad = hexToBytes('4e4f504501' + '00'.repeat(20));
		expect(() => decodeGraph(bad)).toThrow(/bad graph magic/);
	});

	it('rejects truncated input', () => {
		expect(() => decodeGraph(hexToBytes('434f56'))).toThrow(/truncated/);
	});

	it('hexToBytes handles whitespace and 0x prefix', () => {
		const a = hexToBytes('0x434f');
		expect(Array.from(a)).toEqual([0x43, 0x4f]);
		const b = hexToBytes('43 4f');
		expect(Array.from(b)).toEqual([0x43, 0x4f]);
	});
});

describe('decodeLabelList', () => {
	it('roundtrips presence flags and UTF-8 strings', () => {
		// "LBLS" 01 03   N=3
		//  01 03 "abc"   present
		//  00            absent
		//  01 02 "de"    present
		const bytes = new Uint8Array([
			...LABEL_LIST_MAGIC,
			1,
			3,
			1, 3, 0x61, 0x62, 0x63,
			0,
			1, 2, 0x64, 0x65,
		]);
		const ll = decodeLabelList(bytes);
		expect(ll.labels).toEqual(['abc', null, 'de']);
	});

	it('rejects unsupported version', () => {
		const bytes = new Uint8Array([...LABEL_LIST_MAGIC, 99, 0]);
		expect(() => decodeLabelList(bytes)).toThrow(/unsupported label-list version/);
	});
});

describe('decodeKindFlags', () => {
	it('unpacks bits LSB-first', () => {
		// 4 nodes, pattern 1011 (#0 ordered, #1 ordered, #2 pure, #3 ordered)
		// bits byte = 0b00001011 = 0x0b
		const bytes = new Uint8Array([...KIND_FLAGS_MAGIC, 1, 4, 0x0b]);
		const kf = decodeKindFlags(bytes);
		expect(kf.kinds).toEqual(['ordered', 'ordered', 'pure', 'ordered']);
	});

	it('handles uniform-pure', () => {
		// 5 nodes, all pure → 0x00
		const bytes = new Uint8Array([...KIND_FLAGS_MAGIC, 1, 5, 0x00]);
		expect(decodeKindFlags(bytes).kinds).toEqual(['pure', 'pure', 'pure', 'pure', 'pure']);
	});
});

describe('decodeStringDiagram', () => {
	function makeSlotBytes(values: number[]): Uint8Array {
		const buf = new Uint8Array(32);
		values.forEach((v, i) => (buf[i] = v));
		return buf;
	}

	function makeStringDiagramBytes(
		graphHash: Uint8Array,
		labelsSlot: Uint8Array,
		kindsSlot: Uint8Array,
	): Uint8Array {
		const out = new Uint8Array(5 + 32 + 1 + 64);
		out.set(STRING_DIAGRAM_MAGIC, 0);
		out[4] = 1; // version
		out.set(graphHash, 5);
		out[5 + 32] = 2; // slot count LEB128 = 2
		out.set(labelsSlot, 5 + 32 + 1);
		out.set(kindsSlot, 5 + 32 + 1 + 32);
		return out;
	}

	it('decodes absent + sentinel + hash slots', () => {
		const graphHash = new Uint8Array(32).fill(0xa1);
		const absent = makeSlotBytes([]);
		const allOrdered = makeSlotBytes([0xff, 2]);
		const sd = decodeStringDiagram(makeStringDiagramBytes(graphHash, absent, allOrdered));
		expect(Array.from(sd.graph)).toEqual(Array.from(graphHash));
		expect(sd.labels).toEqual({ kind: 'absent' });
		expect(sd.kinds).toEqual({ kind: 'uniform', tag: 'all-ordered' });
	});

	it('rejects non-zero trailing bytes in a sentinel slot', () => {
		const graphHash = new Uint8Array(32).fill(1);
		const bogus = makeSlotBytes([0xff, 1, 5]);
		const absent = makeSlotBytes([]);
		expect(() => decodeStringDiagram(makeStringDiagramBytes(graphHash, bogus, absent))).toThrow(
			/non-zero trailing/,
		);
	});
});

describe('resolveDiagram', () => {
	it('inflates uniform-ordered into per-node kinds', () => {
		const graph = decodeGraph(buildExampleGraphBytes());
		const resolved = resolveDiagram(
			{
				graph: new Uint8Array(32),
				labels: { kind: 'absent' },
				kinds: { kind: 'uniform', tag: 'all-ordered' },
			},
			graph,
			() => null,
		);
		expect(resolved.kinds.kinds).toEqual(['ordered', 'ordered', 'ordered']);
		expect(resolved.labels).toBeNull();
	});

	it('looks up label-list and kind-flags hashes', () => {
		const graph = decodeGraph(buildExampleGraphBytes());
		const labels = new Uint8Array([...LABEL_LIST_MAGIC, 1, 3,
			1, 1, 0x61, 1, 1, 0x62, 1, 1, 0x63]);
		const kinds = new Uint8Array([...KIND_FLAGS_MAGIC, 1, 3, 0b001]);
		const labelHash: HashBytes = new Uint8Array(32).fill(0x10);
		const kindsHash: HashBytes = new Uint8Array(32).fill(0x20);
		const store = new Map<string, Uint8Array>([
			[hexOf(labelHash), labels],
			[hexOf(kindsHash), kinds],
		]);
		const resolved = resolveDiagram(
			{
				graph: new Uint8Array(32),
				labels: { kind: 'hash', hash: labelHash },
				kinds: { kind: 'hash', hash: kindsHash },
			},
			graph,
			(h) => store.get(hexOf(h)) ?? null,
		);
		expect(resolved.labels?.labels).toEqual(['a', 'b', 'c']);
		expect(resolved.kinds.kinds).toEqual(['ordered', 'pure', 'pure']);
	});
});
