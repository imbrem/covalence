<script lang="ts">
	import { detectImageMime } from './detect.js';

	interface Props {
		hash: string;
		data: Uint8Array;
		mode: 'text' | 'hex' | 'image';
	}

	let { hash, data, mode }: Props = $props();

	let textContent = $derived(new TextDecoder('utf-8', { fatal: false }).decode(data));

	let textLines = $derived(textContent.split('\n'));

	let hexLines = $derived(buildHexDump(data));

	let imageUrl = $derived.by(() => {
		if (mode !== 'image') return '';
		const mime = detectImageMime(data);
		if (!mime) return '';
		if (typeof URL === 'undefined' || typeof Blob === 'undefined') return '';
		return URL.createObjectURL(new Blob([data], { type: mime }));
	});

	$effect(() => {
		const url = imageUrl;
		return () => {
			if (url) URL.revokeObjectURL(url);
		};
	});

	function buildHexDump(bytes: Uint8Array): string[] {
		const lines: string[] = [];
		for (let off = 0; off < bytes.length; off += 16) {
			const slice = bytes.subarray(off, Math.min(off + 16, bytes.length));
			const offset = off.toString(16).padStart(8, '0');

			const hexParts: string[] = [];
			for (let i = 0; i < 16; i++) {
				if (i < slice.length) {
					hexParts.push(slice[i].toString(16).padStart(2, '0'));
				} else {
					hexParts.push('  ');
				}
			}
			const hexLeft = hexParts.slice(0, 8).join(' ');
			const hexRight = hexParts.slice(8).join(' ');

			let ascii = '';
			for (let i = 0; i < slice.length; i++) {
				const b = slice[i];
				ascii += (b >= 0x20 && b <= 0x7e) ? String.fromCharCode(b) : '.';
			}

			lines.push(`${offset}  ${hexLeft}  ${hexRight}  |${ascii}|`);
		}
		return lines;
	}
</script>

<div class="blob-viewer">
	{#if mode === 'image'}
		{#if imageUrl}
			<div class="image-view">
				<img src={imageUrl} alt={`blob ${hash.slice(0, 12)}`} />
			</div>
		{:else}
			<div class="image-fallback">not a recognised image format</div>
		{/if}
	{:else if mode === 'text'}
		<pre class="text-view"><code>{#each textLines as line, i}<span class="line-num">{(i + 1).toString().padStart(4, ' ')}</span>  {line}
{/each}</code></pre>
	{:else}
		<pre class="hex-view"><code>{#each hexLines as line}{line}
{/each}</code></pre>
	{/if}
</div>

<style>
	.blob-viewer {
		width: 100%;
		overflow-x: auto;
	}

	pre {
		margin: 0;
		font-family: var(--font-mono, monospace);
		font-size: 0.875rem;
		line-height: 1.5;
		color: var(--fg, #e0e0e0);
	}

	.line-num {
		color: var(--muted, #888);
		user-select: none;
	}

	.hex-view {
		color: var(--muted, #888);
	}

	.image-view {
		display: flex;
		justify-content: center;
		padding: 1rem 0;
	}

	.image-view img {
		max-width: 100%;
		height: auto;
		background-image:
			linear-gradient(45deg, #2a2a2a 25%, transparent 25%),
			linear-gradient(-45deg, #2a2a2a 25%, transparent 25%),
			linear-gradient(45deg, transparent 75%, #2a2a2a 75%),
			linear-gradient(-45deg, transparent 75%, #2a2a2a 75%);
		background-size: 16px 16px;
		background-position: 0 0, 0 8px, 8px -8px, -8px 0;
	}

	.image-fallback {
		color: var(--muted, #888);
		text-align: center;
		padding: 2rem;
	}
</style>
