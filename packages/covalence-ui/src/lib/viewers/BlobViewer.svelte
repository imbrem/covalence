<script lang="ts">
	import { detectMedia, type BlobMode } from './index.js';
	import type { HighlightFn } from './highlight.js';

	interface Props {
		hash: string;
		data: Uint8Array;
		mode: BlobMode;
		language?: string | null;
		highlight?: HighlightFn;
	}

	let { hash, data, mode, language, highlight }: Props = $props();

	let textContent = $derived(new TextDecoder('utf-8', { fatal: false }).decode(data));

	let textLines = $derived(textContent.split('\n'));

	let lineNumWidth = $derived(Math.max(4, String(textLines.length).length));

	let highlighted = $derived.by(() => {
		if (!highlight || language === undefined) return null;
		return highlight(textContent, language);
	});

	let highlightedLines = $derived(highlighted ? highlighted.html.split('\n') : null);

	// Hex dump: offset | 16 hex bytes (8+8) | ASCII sidebar
	let hexLines = $derived(buildHexDump(data));

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

	// Object URL for media rendering — created from raw blob data
	let objectUrl: string | null = $state(null);
	let mediaMime: string = $state('application/octet-stream');

	$effect(() => {
		const media = detectMedia(data);
		const isMedia = mode === 'image' || mode === 'audio' || mode === 'video' || mode === 'pdf';
		if (isMedia && data.length > 0) {
			mediaMime = media?.mime ?? 'application/octet-stream';
			const blob = new Blob([data as BlobPart], { type: mediaMime });
			const url = URL.createObjectURL(blob);
			objectUrl = url;
			return () => URL.revokeObjectURL(url);
		} else {
			objectUrl = null;
		}
	});
</script>

<div class="blob-viewer">
	{#if mode === 'text'}
		{#if highlightedLines}
			<pre class="text-view highlighted"><code>{#each highlightedLines as line, i}<span class="line-num">{(i + 1).toString().padStart(lineNumWidth, ' ')}</span>  {@html line}
{/each}</code></pre>
		{:else}
			<pre class="text-view"><code>{#each textLines as line, i}<span class="line-num">{(i + 1).toString().padStart(lineNumWidth, ' ')}</span>  {line}
{/each}</code></pre>
		{/if}
	{:else if mode === 'hex'}
		<pre class="hex-view"><code>{#each hexLines as line}{line}
{/each}</code></pre>
	{:else if mode === 'image' && objectUrl}
		<div class="media-view">
			<img src={objectUrl} alt="blob {hash.slice(0, 12)}" />
		</div>
	{:else if mode === 'audio' && objectUrl}
		<div class="media-view">
			<audio controls src={objectUrl}>
				<track kind="captions" />
			</audio>
		</div>
	{:else if mode === 'video' && objectUrl}
		<div class="media-view">
			<video controls src={objectUrl}>
				<track kind="captions" />
			</video>
		</div>
	{:else if mode === 'pdf' && objectUrl}
		<div class="media-view pdf-view">
			<object data={objectUrl} type="application/pdf" title="PDF blob {hash.slice(0, 12)}">
				<p>PDF preview not supported in this browser.
					<a href={objectUrl} download="blob.pdf">Download PDF</a>
				</p>
			</object>
		</div>
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

	.media-view {
		display: flex;
		justify-content: center;
		align-items: center;
		padding: 1rem 0;
	}

	.media-view img {
		max-width: 100%;
		max-height: 80vh;
		object-fit: contain;
	}

	.media-view audio {
		width: 100%;
		max-width: 500px;
	}

	.media-view video {
		max-width: 100%;
		max-height: 80vh;
	}

	.pdf-view {
		display: block;
		height: 80vh;
	}

	.pdf-view object {
		width: 100%;
		height: 100%;
		border: none;
	}
</style>
