import { describe, it, expect, beforeEach, afterEach, vi } from 'vitest';
import { render, cleanup } from '@testing-library/svelte';
import BlobViewer from './BlobViewer.svelte';

const PNG_BYTES = new Uint8Array([
	0x89, 0x50, 0x4e, 0x47, 0x0d, 0x0a, 0x1a, 0x0a,
	0x00, 0x00, 0x00, 0x0d, 0x49, 0x48, 0x44, 0x52,
]);

const DUMMY_HASH = 'a'.repeat(64);

beforeEach(() => {
	if (!globalThis.URL.createObjectURL) {
		globalThis.URL.createObjectURL = vi.fn(() => 'blob:mock-url');
		globalThis.URL.revokeObjectURL = vi.fn();
	}
});

afterEach(() => {
	cleanup();
	vi.restoreAllMocks();
});

describe('BlobViewer', () => {
	it('renders text mode with line numbers', () => {
		const data = new TextEncoder().encode('hello\nworld');
		const { container } = render(BlobViewer, {
			props: { hash: DUMMY_HASH, data, mode: 'text' },
		});
		const pre = container.querySelector('pre.text-view');
		expect(pre).not.toBeNull();
		const text = pre!.textContent ?? '';
		expect(text).toContain('hello');
		expect(text).toContain('world');
		const lineNums = container.querySelectorAll('.line-num');
		expect(lineNums.length).toBeGreaterThanOrEqual(2);
	});

	it('renders hex mode with offset, hex bytes, and ASCII sidebar', () => {
		const data = new Uint8Array([0xde, 0xad, 0xbe, 0xef, 0x41]);
		const { container } = render(BlobViewer, {
			props: { hash: DUMMY_HASH, data, mode: 'hex' },
		});
		const pre = container.querySelector('pre.hex-view');
		expect(pre).not.toBeNull();
		const text = pre!.textContent ?? '';
		expect(text).toContain('00000000');
		expect(text).toContain('de ad be ef');
		expect(text).toContain('|....A|');
	});

	it('renders an <img> with a blob URL when mode=image and PNG bytes are provided', () => {
		const createSpy = vi.spyOn(URL, 'createObjectURL').mockReturnValue('blob:test-png');
		const { container } = render(BlobViewer, {
			props: { hash: DUMMY_HASH, data: PNG_BYTES, mode: 'image' },
		});
		const img = container.querySelector('img');
		expect(img).not.toBeNull();
		expect(img!.getAttribute('src')).toBe('blob:test-png');
		expect(img!.getAttribute('alt')).toContain(DUMMY_HASH.slice(0, 12));
		expect(createSpy).toHaveBeenCalledOnce();
		const blobArg = createSpy.mock.calls[0][0] as Blob;
		expect(blobArg.type).toBe('image/png');
	});

	it('shows a fallback message in image mode when bytes are not a recognised image', () => {
		const data = new TextEncoder().encode('plain text, not an image');
		const { container } = render(BlobViewer, {
			props: { hash: DUMMY_HASH, data, mode: 'image' },
		});
		expect(container.querySelector('img')).toBeNull();
		const fallback = container.querySelector('.image-fallback');
		expect(fallback).not.toBeNull();
		expect(fallback!.textContent).toContain('not a recognised image');
	});

	it('revokes the object URL when the component unmounts', () => {
		const revokeSpy = vi.spyOn(URL, 'revokeObjectURL').mockImplementation(() => {});
		vi.spyOn(URL, 'createObjectURL').mockReturnValue('blob:to-revoke');
		const { unmount } = render(BlobViewer, {
			props: { hash: DUMMY_HASH, data: PNG_BYTES, mode: 'image' },
		});
		unmount();
		expect(revokeSpy).toHaveBeenCalledWith('blob:to-revoke');
	});
});
