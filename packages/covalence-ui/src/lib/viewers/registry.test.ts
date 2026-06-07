import { describe, it, expect } from 'vitest';
import { getViewer } from './index.js';

const PNG_HEADER = new Uint8Array([0x89, 0x50, 0x4e, 0x47, 0x0d, 0x0a, 0x1a, 0x0a]);

describe('blob viewer registration', () => {
	it('registers a viewer for the "blob" kind exposing graph/text/hex/image modes', () => {
		const viewer = getViewer('blob');
		expect(viewer).toBeDefined();
		expect(viewer!.modes).toEqual(['graph', 'text', 'hex', 'image']);
	});

	it('auto-selects image mode for PNG bytes', () => {
		const viewer = getViewer('blob');
		expect(viewer?.autoMode?.(PNG_HEADER)).toBe('image');
	});

	it('auto-selects text mode for UTF-8 source', () => {
		const viewer = getViewer('blob');
		expect(viewer?.autoMode?.(new TextEncoder().encode('(module)'))).toBe('text');
	});

	it('auto-selects hex mode for arbitrary binary', () => {
		const viewer = getViewer('blob');
		const bin = new Uint8Array([0x01, 0x02, 0x03, 0x04, 0x05, 0xff]);
		expect(viewer?.autoMode?.(bin)).toBe('hex');
	});

	it('returns a viewer for the "tree" kind without modes', () => {
		const viewer = getViewer('tree');
		expect(viewer).toBeDefined();
		expect(viewer!.modes).toBeUndefined();
	});

	it('returns undefined for unknown kinds', () => {
		expect(getViewer('nonexistent')).toBeUndefined();
	});
});
