// covalence-ui — Shared Svelte 5 component library
export { registerViewer, getViewer } from './viewers/index.js';
export type { ViewerDescriptor } from './viewers/index.js';
export { detectImageMime, isLikelyText, detectBlobMode } from './viewers/index.js';
export type { HighlightFn, HighlightResult, LanguageOption } from './viewers/index.js';

export { default as GraphView } from './graph/GraphView.svelte';
export {
	decodeGraph,
	decodeStringDiagram,
	decodeLabelList,
	decodeKindFlags,
	resolveDiagram,
	diagramFromGraphOnly,
	mapResolver,
	magicOf,
	hexToBytes,
	hexOf,
} from './graph/decode.js';
export type {
	Graph,
	GraphNode,
	GraphPort,
	GraphEdge,
	NodeKind,
	PortKind,
	HashBytes,
	/** @deprecated Use `HashBytes` — see `graph/types.ts`. */
	Hash,
	LabelList,
	KindFlags,
	SlotRef,
	StringDiagram,
	ResolvedDiagram,
} from './graph/types.js';
