/** Magic-byte sniffing for blob viewers. */

function startsWith(data: Uint8Array, magic: readonly number[]): boolean {
	if (data.length < magic.length) return false;
	for (let i = 0; i < magic.length; i++) {
		if (data[i] !== magic[i]) return false;
	}
	return true;
}

const PNG = [0x89, 0x50, 0x4e, 0x47, 0x0d, 0x0a, 0x1a, 0x0a] as const;
const JPEG = [0xff, 0xd8, 0xff] as const;
const GIF87A = [0x47, 0x49, 0x46, 0x38, 0x37, 0x61] as const;
const GIF89A = [0x47, 0x49, 0x46, 0x38, 0x39, 0x61] as const;
const RIFF = [0x52, 0x49, 0x46, 0x46] as const;
const WEBP = [0x57, 0x45, 0x42, 0x50] as const;

/**
 * Return a MIME type if the byte stream starts with a recognised image
 * magic, else null. Recognises PNG, JPEG, GIF87a/89a, and WebP.
 */
export function detectImageMime(data: Uint8Array): string | null {
	if (startsWith(data, PNG)) return 'image/png';
	if (startsWith(data, JPEG)) return 'image/jpeg';
	if (startsWith(data, GIF87A) || startsWith(data, GIF89A)) return 'image/gif';
	if (data.length >= 12 && startsWith(data, RIFF)) {
		for (let i = 0; i < WEBP.length; i++) {
			if (data[8 + i] !== WEBP[i]) return null;
		}
		return 'image/webp';
	}
	return null;
}

/**
 * Heuristic: is the data likely UTF-8 text? Checks the first 8 KiB for
 * NUL bytes and excessive non-printable characters.
 */
export function isLikelyText(data: Uint8Array): boolean {
	if (data.length === 0) return true;
	const check = Math.min(data.length, 8192);
	let nonPrintable = 0;
	for (let i = 0; i < check; i++) {
		const b = data[i];
		if (b === 0) return false;
		if (b < 0x20 && b !== 0x09 && b !== 0x0a && b !== 0x0d) nonPrintable++;
	}
	return nonPrintable / check < 0.1;
}

/**
 * Pick a default display mode for a raw blob *without* tag information.
 * Tag-aware callers should set mode='graph' directly from the tag string.
 */
export function detectBlobMode(data: Uint8Array): 'image' | 'text' | 'hex' {
	if (detectImageMime(data)) return 'image';
	if (isLikelyText(data)) return 'text';
	return 'hex';
}
