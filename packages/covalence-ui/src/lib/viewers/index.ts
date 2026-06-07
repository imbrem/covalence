import { registerViewer } from './registry.js';
import TreeViewer from './TreeViewer.svelte';
import BlobViewer from './BlobViewer.svelte';
import { detectBlobMode } from './detect.js';

registerViewer({
	kinds: ['tree'],
	label: 'Tree',
	component: TreeViewer,
});

registerViewer({
	kinds: ['blob'],
	label: 'Blob',
	modes: ['graph', 'text', 'hex', 'image'],
	autoMode: detectBlobMode,
	component: BlobViewer,
});

export { registerViewer, getViewer } from './registry.js';
export type { ViewerDescriptor } from './registry.js';
export { detectImageMime, isLikelyText, detectBlobMode } from './detect.js';
