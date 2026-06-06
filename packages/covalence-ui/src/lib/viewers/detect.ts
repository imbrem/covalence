/** Magic-byte sniffing for blob viewers. */

const PNG_MAGIC = [0x89, 0x50, 0x4e, 0x47, 0x0d, 0x0a, 0x1a, 0x0a];
const JPEG_MAGIC = [0xff, 0xd8, 0xff];
const GIF87A_MAGIC = [0x47, 0x49, 0x46, 0x38, 0x37, 0x61];
const GIF89A_MAGIC = [0x47, 0x49, 0x46, 0x38, 0x39, 0x61];
const WEBP_RIFF = [0x52, 0x49, 0x46, 0x46];
const WEBP_TAG = [0x57, 0x45, 0x42, 0x50];

function startsWith(data: Uint8Array, magic: number[]): boolean {
	if (data.length < magic.length) return false;
	for (let i = 0; i < magic.length; i++) {
		if (data[i] !== magic[i]) return false;
	}
	return true;
}

/**
 * Return a MIME type if the byte stream starts with a recognised image
 * magic, else null. Recognises PNG, JPEG, GIF87a/89a, and WebP.
 */
export function detectImageMime(data: Uint8Array): string | null {
	if (startsWith(data, PNG_MAGIC)) return 'image/png';
	if (startsWith(data, JPEG_MAGIC)) return 'image/jpeg';
	if (startsWith(data, GIF87A_MAGIC) || startsWith(data, GIF89A_MAGIC)) return 'image/gif';
	if (data.length >= 12 && startsWith(data, WEBP_RIFF)) {
		for (let i = 0; i < WEBP_TAG.length; i++) {
			if (data[8 + i] !== WEBP_TAG[i]) return null;
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

/** Pick a default display mode given raw blob bytes. */
export function detectBlobMode(data: Uint8Array): 'image' | 'text' | 'hex' {
	if (detectImageMime(data)) return 'image';
	if (isLikelyText(data)) return 'text';
	return 'hex';
}
