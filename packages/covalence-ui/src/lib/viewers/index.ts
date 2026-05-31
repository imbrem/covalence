import { registerViewer } from './registry.js';
import TreeViewer from './TreeViewer.svelte';
import BlobViewer from './BlobViewer.svelte';

/** Heuristic: is the data likely UTF-8 text? */
function isLikelyText(data: Uint8Array): boolean {
	// Empty → text
	if (data.length === 0) return true;
	// Check first 8KB for null bytes or excessive non-UTF8
	const check = Math.min(data.length, 8192);
	let nonPrintable = 0;
	for (let i = 0; i < check; i++) {
		const b = data[i];
		if (b === 0) return false; // null byte → binary
		if (b < 0x20 && b !== 0x09 && b !== 0x0a && b !== 0x0d) nonPrintable++;
	}
	return nonPrintable / check < 0.1;
}

registerViewer({
	kinds: ['tree'],
	label: 'Tree',
	component: TreeViewer,
});

registerViewer({
	kinds: ['blob'],
	label: 'Blob',
	modes: ['text', 'hex'],
	autoMode: (data) => isLikelyText(data) ? 'text' : 'hex',
	component: BlobViewer,
});

export { registerViewer, getViewer } from './registry.js';
export type { ViewerDescriptor } from './registry.js';
