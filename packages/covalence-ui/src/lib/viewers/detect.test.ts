import { describe, it, expect } from 'vitest';
import { detectImageMime, isLikelyText, detectBlobMode, isCovGraph } from './detect.js';

const COVG_V1_PREFIX = new Uint8Array([0x43, 0x4f, 0x56, 0x47, 0x01]);

const PNG_HEADER = new Uint8Array([0x89, 0x50, 0x4e, 0x47, 0x0d, 0x0a, 0x1a, 0x0a]);
const JPEG_HEADER = new Uint8Array([0xff, 0xd8, 0xff, 0xe0]);
const GIF87A = new Uint8Array([...new TextEncoder().encode('GIF87a')]);
const GIF89A = new Uint8Array([...new TextEncoder().encode('GIF89a')]);

function webpBytes(): Uint8Array {
	const out = new Uint8Array(16);
	out.set([0x52, 0x49, 0x46, 0x46], 0);
	out.set([0, 0, 0, 0], 4);
	out.set([0x57, 0x45, 0x42, 0x50], 8);
	return out;
}

describe('detectImageMime', () => {
	it('returns image/png for a PNG header', () => {
		const data = new Uint8Array(PNG_HEADER.length + 8);
		data.set(PNG_HEADER);
		expect(detectImageMime(data)).toBe('image/png');
	});

	it('returns image/jpeg for a JPEG header', () => {
		expect(detectImageMime(JPEG_HEADER)).toBe('image/jpeg');
	});

	it('returns image/gif for both GIF87a and GIF89a', () => {
		expect(detectImageMime(GIF87A)).toBe('image/gif');
		expect(detectImageMime(GIF89A)).toBe('image/gif');
	});

	it('returns image/webp only when the RIFF tag is WEBP', () => {
		expect(detectImageMime(webpBytes())).toBe('image/webp');
		const wrongTag = webpBytes();
		wrongTag[8] = 0x57;
		wrongTag[9] = 0x41;
		wrongTag[10] = 0x56;
		wrongTag[11] = 0x45;
		expect(detectImageMime(wrongTag)).toBeNull();
	});

	it('returns null for plain text', () => {
		const data = new TextEncoder().encode('hello world');
		expect(detectImageMime(data)).toBeNull();
	});

	it('returns null for empty input', () => {
		expect(detectImageMime(new Uint8Array())).toBeNull();
	});

	it('rejects PNG-like prefix that is too short', () => {
		expect(detectImageMime(PNG_HEADER.subarray(0, 4))).toBeNull();
	});
});

describe('isLikelyText', () => {
	it('treats an empty blob as text', () => {
		expect(isLikelyText(new Uint8Array())).toBe(true);
	});

	it('treats ASCII as text', () => {
		expect(isLikelyText(new TextEncoder().encode('(module)\n'))).toBe(true);
	});

	it('rejects data containing a NUL byte', () => {
		const data = new Uint8Array([0x68, 0x69, 0x00, 0x21]);
		expect(isLikelyText(data)).toBe(false);
	});

	it('rejects binary data with many non-printable bytes', () => {
		const data = new Uint8Array(64);
		for (let i = 0; i < data.length; i++) data[i] = i + 1;
		expect(isLikelyText(data)).toBe(false);
	});
});

describe('detectBlobMode', () => {
	it('picks image for PNG bytes', () => {
		expect(detectBlobMode(PNG_HEADER)).toBe('image');
	});

	it('picks text for ASCII', () => {
		expect(detectBlobMode(new TextEncoder().encode('hello'))).toBe('text');
	});

	it('picks hex for non-image binary data', () => {
		const data = new Uint8Array([0xde, 0xad, 0xbe, 0xef, 0x00, 0x01, 0x02]);
		expect(detectBlobMode(data)).toBe('hex');
	});

	it('picks graph when blob starts with COVG v1 magic', () => {
		const data = new Uint8Array([...COVG_V1_PREFIX, 0]);
		expect(detectBlobMode(data)).toBe('graph');
	});
});

describe('isCovGraph', () => {
	it('accepts COVG v1', () => {
		expect(isCovGraph(COVG_V1_PREFIX)).toBe(true);
	});

	it('rejects truncated magic', () => {
		expect(isCovGraph(new Uint8Array([0x43, 0x4f, 0x56]))).toBe(false);
	});

	it('rejects wrong magic', () => {
		expect(isCovGraph(new Uint8Array([0x43, 0x4f, 0x56, 0x48, 0x01]))).toBe(false);
	});

	it('rejects unsupported version', () => {
		expect(isCovGraph(new Uint8Array([0x43, 0x4f, 0x56, 0x47, 0x02]))).toBe(false);
	});
});
