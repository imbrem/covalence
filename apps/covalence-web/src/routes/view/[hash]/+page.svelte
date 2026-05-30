<script lang="ts">
	import { page } from '$app/stores';
	import { client } from '$lib/api';
	import { getViewer, detectMedia } from 'covalence-ui';
	import type { HighlightFn } from 'covalence-ui';
	import type { ObjectInfoResponse, TreeEntry } from 'covalence-client';
	import '$lib/hljs-covalence.css';

	let hash = $derived($page.params.hash);

	// Fetch state
	let info: ObjectInfoResponse | null = $state(null);
	let loading = $state(true);
	let error: string | null = $state(null);

	// Viewer data
	let treeEntries: TreeEntry[] = $state([]);
	let blobData: Uint8Array = $state(new Uint8Array());
	let mode: string = $state('');

	// Syntax highlighting state
	let language: string | null | undefined = $state(undefined);
	let highlightFn: HighlightFn | undefined = $state(undefined);
	let langOptions: { id: string; name: string }[] = $state([]);

	// Load object info + data whenever hash changes
	let lastHash = '';
	$effect(() => {
		const h = hash;
		if (h && h !== lastHash) {
			lastHash = h;
			loadObject(h);
		}
	});

	// Read fragment for mode override — extended: #text, #text:rust, #text:auto, #text:plain
	const validModes = new Set(['text', 'hex', 'tree', 'image', 'audio', 'video', 'pdf']);
	$effect(() => {
		if (typeof window !== 'undefined') {
			const frag = window.location.hash.slice(1);
			if (validModes.has(frag)) {
				mode = frag;
			} else if (frag.startsWith('text:')) {
				mode = 'text';
				const langPart = frag.slice(5);
				if (langPart === 'auto') {
					language = null;
				} else if (langPart === 'plain') {
					language = 'plain';
				} else if (langPart) {
					language = langPart;
				}
			}
		}
	});

	// Lazy-load highlighter when entering text mode
	$effect(() => {
		if (mode === 'text' && !highlightFn) {
			initHighlighter();
		}
	});

	async function initHighlighter() {
		try {
			const mod = await import('$lib/highlighter');
			highlightFn = await mod.createHighlighter();
			langOptions = mod.getLanguageOptions();

			// If no language specified yet, try to auto-detect from content
			if (language === undefined && blobData.length > 0) {
				const suggested = mod.suggestLanguage(blobData);
				language = suggested; // null means auto-detect via hljs
			}
		} catch (e) {
			console.warn('Failed to load highlighter:', e);
		}
	}

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

			const viewer = getViewer(objInfo.kind);
			if (!viewer) {
				error = `No viewer for kind "${objInfo.kind}"`;
				loading = false;
				return;
			}

			if (objInfo.kind === 'tree') {
				treeEntries = await client.treeLs(h);
				if (!mode) mode = 'tree';
			} else if (objInfo.kind === 'blob') {
				const data = await client.getObjectBlob(h);
				blobData = data ?? new Uint8Array();
				if (!mode && viewer.autoMode) {
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

	let viewer = $derived(info ? getViewer(info.kind) : undefined);

	// Show text+hex always, plus the detected media mode (if any)
	let visibleModes = $derived.by(() => {
		if (info?.kind !== 'blob') return undefined;
		const media = detectMedia(blobData);
		if (media) return ['text', 'hex', media.category];
		return ['text', 'hex'];
	});

	function setMode(m: string) {
		mode = m;
		updateFragment();
	}

	function setLanguage(lang: string | null) {
		language = lang;
		updateFragment();
	}

	function updateFragment() {
		if (typeof window === 'undefined') return;

		if (mode === 'text' && language !== undefined) {
			let suffix: string;
			if (language === null) {
				suffix = 'auto';
			} else if (language === 'plain') {
				suffix = 'plain';
			} else {
				suffix = language;
			}
			history.replaceState(null, '', `#text:${suffix}`);
		} else {
			history.replaceState(null, '', `#${mode}`);
		}
	}

	function onLanguageSelect(e: Event) {
		const value = (e.target as HTMLSelectElement).value;
		if (value === '__auto__') {
			setLanguage(null);
		} else if (value === '__plain__') {
			setLanguage('plain');
		} else {
			setLanguage(value);
		}
	}

	/** Value for the select element given current language state. */
	let selectValue = $derived(
		language === undefined ? '__auto__'
		: language === null ? '__auto__'
		: language === 'plain' ? '__plain__'
		: language
	);

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

	{#if visibleModes && visibleModes.length > 1}
		<div class="mode-bar">
			<div class="mode-buttons">
				{#each visibleModes as m}
					<button
						class="mode-btn"
						class:active={mode === m}
						onclick={() => setMode(m)}
					>
						{m}
					</button>
				{/each}
			</div>
			{#if mode === 'text' && langOptions.length > 0}
				<select class="lang-picker" value={selectValue} onchange={onLanguageSelect}>
					<option value="__auto__">Auto-detect</option>
					<option value="__plain__">Plain text</option>
					{#each langOptions as opt}
						<option value={opt.id}>{opt.name}</option>
					{/each}
				</select>
			{/if}
		</div>
	{:else if viewer?.modes && viewer.modes.length > 1 && info?.kind !== 'blob'}
		<div class="mode-bar">
			<div class="mode-buttons">
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
		</div>
	{/if}

	<div class="viewer-content">
		{#if loading}
			<div class="status-msg">Loading&hellip;</div>
		{:else if error}
			<div class="status-msg error-msg">{error}</div>
		{:else if info?.kind === 'tree' && viewer}
			<svelte:component this={viewer.component} {hash} entries={treeEntries} />
		{:else if info?.kind === 'blob' && viewer}
			<svelte:component this={viewer.component} {hash} data={blobData} {mode} language={language} highlight={highlightFn} />
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
		align-items: center;
		gap: 0.75rem;
		padding: 0.5rem 1.5rem;
		border-bottom: 1px solid var(--border);
		flex-shrink: 0;
	}

	.mode-buttons {
		display: flex;
		gap: 0;
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

	.lang-picker {
		margin-left: auto;
		background: transparent;
		border: 1px solid var(--border);
		border-radius: 4px;
		color: var(--fg, #e0e0e0);
		font-family: var(--font-mono);
		font-size: 0.75rem;
		padding: 0.2rem 0.4rem;
		cursor: pointer;
	}

	.lang-picker option {
		background: var(--bg, #1a1a2e);
		color: var(--fg, #e0e0e0);
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
