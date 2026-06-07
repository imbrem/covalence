<script lang="ts">
	import { page } from '$app/stores';
	import { client } from '$lib/api';
	import { getViewer, hexOf } from 'covalence-ui';
	import type { Hash } from 'covalence-ui';
	import type { ObjectInfoResponse, TreeEntry } from 'covalence-client';

	/**
	 * BlobViewer resolver: fetch the bytes a keyed identity names.
	 * Resolves the two-step `lookup_tag → get_blob` indirection that
	 * every graph-family reference uses — the slot hash is a keyed
	 * identity, not a direct content hash.
	 */
	async function resolver(h: Hash): Promise<Uint8Array | null> {
		const hex = hexOf(h);
		try {
			const info = await client.objectInfo(hex);
			if (!info?.contentHash) return null;
			const data = await client.getObjectBlob(info.contentHash);
			return data ?? null;
		} catch {
			return null;
		}
	}

	let hash = $derived($page.params.hash);

	// Fetch state
	let info: ObjectInfoResponse | null = $state(null);
	let loading = $state(true);
	let error: string | null = $state(null);

	// Viewer data
	let treeEntries: TreeEntry[] = $state([]);
	let blobData: Uint8Array = $state(new Uint8Array());
	let mode: string = $state('');
	/** Tag string when the hash is a keyed identity. Drives BlobViewer's
	 *  graph-mode dispatch. */
	let tag: string | undefined = $state(undefined);

	// Load object info + data whenever hash changes
	let lastHash = '';
	$effect(() => {
		const h = hash;
		if (h && h !== lastHash) {
			lastHash = h;
			loadObject(h);
		}
	});

	// Read fragment for mode override
	$effect(() => {
		if (typeof window !== 'undefined') {
			const frag = window.location.hash.slice(1);
			if (frag === 'text' || frag === 'hex' || frag === 'tree' || frag === 'graph' || frag === 'image') {
				mode = frag;
			}
		}
	});

	async function loadObject(h: string) {
		loading = true;
		error = null;
		info = null;

		try {
			const objInfo = await client.objectInfo(h);
			if (!objInfo) {
				error = 'Object not found';
				loading = false;
				return;
			}
			info = objInfo;

			// 'tagged' renders through the blob viewer with the tag
			// driving dispatch; we fetch by the underlying content hash
			// since the keyed hash isn't a content-store key.
			const viewerKind: 'tree' | 'blob' = objInfo.kind === 'tree' ? 'tree' : 'blob';
			const viewer = getViewer(viewerKind);
			if (!viewer) {
				error = `No viewer for kind "${objInfo.kind}"`;
				loading = false;
				return;
			}

			if (objInfo.kind === 'tree') {
				treeEntries = await client.treeLs(h);
				if (!mode) mode = 'tree';
			} else {
				// blob or tagged — both render through BlobViewer.
				const fetchHash =
					objInfo.kind === 'tagged' && objInfo.contentHash ? objInfo.contentHash : h;
				const data = await client.getObjectBlob(fetchHash);
				blobData = data ?? new Uint8Array();
				tag = objInfo.tag;
				if (tag) {
					// Keyed-identity tag overrides any magic sniffing.
					mode = 'graph';
				} else if (!mode && viewer.autoMode) {
					mode = viewer.autoMode(blobData);
				} else if (!mode) {
					mode = 'text';
				}
			}
		} catch (e) {
			error = e instanceof Error ? e.message : String(e);
		}
		loading = false;
	}

	let viewer = $derived(
		info ? getViewer(info.kind === 'tagged' ? 'blob' : info.kind) : undefined,
	);

	function setMode(m: string) {
		mode = m;
		if (typeof window !== 'undefined') {
			history.replaceState(null, '', `#${m}`);
		}
	}

	function formatSize(bytes: number): string {
		if (bytes < 1024) return `${bytes} B`;
		if (bytes < 1024 * 1024) return `${(bytes / 1024).toFixed(1)} KB`;
		return `${(bytes / (1024 * 1024)).toFixed(1)} MB`;
	}
</script>

<div class="viewer-page">
	<header class="viewer-header">
		<a href="/" class="back-link">&larr; REPL</a>
		<span class="hash-display">{hash.slice(0, 16)}&hellip;</span>
		{#if info}
			<span class="kind-badge">{info.kind}</span>
			<span class="size-label">{formatSize(info.size)}</span>
		{/if}
	</header>

	{#if viewer?.modes && viewer.modes.length > 1}
		<div class="mode-bar">
			{#each viewer.modes as m}
				<button
					class="mode-btn"
					class:active={mode === m}
					onclick={() => setMode(m)}
				>
					{m}
				</button>
			{/each}
		</div>
	{/if}

	<div class="viewer-content">
		{#if loading}
			<div class="status-msg">Loading&hellip;</div>
		{:else if error}
			<div class="status-msg error-msg">{error}</div>
		{:else if info?.kind === 'tree' && viewer}
			{@const TreeViewer = viewer.component}
			<TreeViewer {hash} entries={treeEntries} />
		{:else if (info?.kind === 'blob' || info?.kind === 'tagged') && viewer}
			{@const BlobViewer = viewer.component}
			<BlobViewer {hash} data={blobData} {mode} {resolver} {tag} />
		{:else if viewer}
			<div class="status-msg">Unsupported object kind: {info?.kind}</div>
		{/if}
	</div>
</div>

<style>
	.viewer-page {
		display: flex;
		flex-direction: column;
		height: 100vh;
		max-width: 900px;
		margin: 0 auto;
	}

	.viewer-header {
		display: flex;
		align-items: center;
		gap: 0.75rem;
		padding: 0.75rem 1.5rem;
		border-bottom: 1px solid var(--border);
		flex-shrink: 0;
	}

	.back-link {
		color: var(--accent);
		text-decoration: none;
		font-weight: 500;
	}

	.back-link:hover {
		text-decoration: underline;
	}

	.hash-display {
		font-family: var(--font-mono);
		font-size: 0.875rem;
		color: var(--muted);
	}

	.kind-badge {
		font-size: 0.7rem;
		color: var(--accent);
		border: 1px solid var(--accent);
		border-radius: 3px;
		padding: 0 5px;
		line-height: 1.5;
	}

	.size-label {
		font-size: 0.8rem;
		color: var(--muted);
		margin-left: auto;
	}

	.mode-bar {
		display: flex;
		gap: 0;
		padding: 0.5rem 1.5rem;
		border-bottom: 1px solid var(--border);
		flex-shrink: 0;
	}

	.mode-btn {
		background: transparent;
		border: 1px solid var(--border);
		color: var(--muted);
		padding: 0.25rem 0.75rem;
		font-family: var(--font-mono);
		font-size: 0.8rem;
		cursor: pointer;
	}

	.mode-btn:first-child {
		border-radius: 4px 0 0 4px;
	}

	.mode-btn:last-child {
		border-radius: 0 4px 4px 0;
	}

	.mode-btn + .mode-btn {
		border-left: none;
	}

	.mode-btn.active {
		background: var(--accent);
		border-color: var(--accent);
		color: #fff;
	}

	.viewer-content {
		flex: 1;
		overflow: auto;
		padding: 1rem 1.5rem;
	}

	.status-msg {
		color: var(--muted);
		text-align: center;
		padding: 2rem;
	}

	.error-msg {
		color: #f87171;
	}
</style>
