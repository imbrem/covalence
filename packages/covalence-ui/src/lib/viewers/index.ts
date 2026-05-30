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

export type MediaCategory = 'image' | 'audio' | 'video' | 'pdf';

/** Detect media type from magic bytes. Returns null if not a recognized media format. */
export function detectMedia(data: Uint8Array): { category: MediaCategory; mime: string } | null {
	if (data.length < 4) return null;

	const u32 = (o: number) => data.length > o + 3
		? (data[o] << 24 | data[o+1] << 16 | data[o+2] << 8 | data[o+3])
		: 0;

	// PDF: %PDF
	if (data[0] === 0x25 && data[1] === 0x50 && data[2] === 0x44 && data[3] === 0x46)
		return { category: 'pdf', mime: 'application/pdf' };

	// PNG
	if (u32(0) === 0x89504E47) return { category: 'image', mime: 'image/png' };
	// JPEG
	if (data[0] === 0xFF && data[1] === 0xD8 && data[2] === 0xFF)
		return { category: 'image', mime: 'image/jpeg' };
	// GIF
	if (u32(0) === 0x47494638) return { category: 'image', mime: 'image/gif' };
	// BMP
	if (data[0] === 0x42 && data[1] === 0x4D) return { category: 'image', mime: 'image/bmp' };
	// TIFF (little-endian or big-endian)
	if ((data[0] === 0x49 && data[1] === 0x49 && data[2] === 0x2A && data[3] === 0x00) ||
		(data[0] === 0x4D && data[1] === 0x4D && data[2] === 0x00 && data[3] === 0x2A))
		return { category: 'image', mime: 'image/tiff' };
	// ICO
	if (data[0] === 0x00 && data[1] === 0x00 && data[2] === 0x01 && data[3] === 0x00)
		return { category: 'image', mime: 'image/x-icon' };

	// RIFF container: WebP, WAV, AVI
	if (u32(0) === 0x52494646 && data.length >= 12) {
		const sub = u32(8);
		if (sub === 0x57454250) return { category: 'image', mime: 'image/webp' };
		if (sub === 0x57415645) return { category: 'audio', mime: 'audio/wav' };
		if (sub === 0x41564920) return { category: 'video', mime: 'video/avi' };
	}

	// FLAC
	if (u32(0) === 0x664C6143) return { category: 'audio', mime: 'audio/flac' };
	// OGG (could be audio or video — default to audio, browser handles both)
	if (u32(0) === 0x4F676753) return { category: 'audio', mime: 'audio/ogg' };
	// MIDI
	if (u32(0) === 0x4D546864) return { category: 'audio', mime: 'audio/midi' };
	// MP3: ID3 tag
	if (data[0] === 0x49 && data[1] === 0x44 && data[2] === 0x33)
		return { category: 'audio', mime: 'audio/mpeg' };
	// MP3: sync word
	if (data[0] === 0xFF && (data[1] & 0xE0) === 0xE0)
		return { category: 'audio', mime: 'audio/mpeg' };

	// EBML (WebM/Matroska)
	if (u32(0) === 0x1A45DFA3) return { category: 'video', mime: 'video/webm' };

	// ISO BMFF / ftyp box (MP4, M4A, AVIF, etc.)
	if (data.length >= 12 && u32(4) === 0x66747970) {
		const brand = u32(8);
		// AVIF
		if (brand === 0x61766966) return { category: 'image', mime: 'image/avif' };
		// HEIF/HEIC
		if (brand === 0x68656963 || brand === 0x6D696631)
			return { category: 'image', mime: 'image/heic' };
		// M4A audio
		if (brand === 0x4D344120) return { category: 'audio', mime: 'audio/mp4' };
		// Default: MP4 video
		return { category: 'video', mime: 'video/mp4' };
	}

	return null;
}

/** All blob display modes. */
export const BLOB_MODES = ['text', 'hex', 'image', 'audio', 'video', 'pdf'] as const;
export type BlobMode = (typeof BLOB_MODES)[number];

registerViewer({
	kinds: ['tree'],
	label: 'Tree',
	component: TreeViewer,
});

registerViewer({
	kinds: ['blob'],
	label: 'Blob',
	modes: ['text', 'hex', 'image', 'audio', 'video', 'pdf'],
	autoMode(data) {
		const media = detectMedia(data);
		if (media) return media.category;
		return isLikelyText(data) ? 'text' : 'hex';
	},
	component: BlobViewer,
});

export { registerViewer, getViewer } from './registry.js';
export type { ViewerDescriptor } from './registry.js';
