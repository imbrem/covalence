<script lang="ts">
	import SourceTree from '$lib/SourceTree.svelte';
	import { highlightSource } from '$lib/sourceHighlighter';

	let { data } = $props();
	let highlighted = $derived(data.file ? highlightSource(data.file.content, data.file.language) : '');
	let lineCount = $derived(data.file ? data.file.content.split('\n').length : 0);
</script>

<svelte:head><title>{data.file ? `${data.file.path} · ` : ''}Covalence source</title></svelte:head>

<main>
	<aside>
		<div class="tree-head">
			<strong>repository</strong>
			<span>{data.files.length} files</span>
		</div>
		<SourceTree files={data.files} current={data.file?.path ?? null} />
	</aside>
	<section class="source">
		{#if data.file}
			<header>
				<h1>{data.file.path}</h1>
				<p>{data.file.language} · {data.file.lines} lines · {data.provider}</p>
			</header>
			<article aria-label={`Source for ${data.file.path}`}>
				<pre class="numbers">{#each Array(lineCount) as _, index}<a
							id={`L${index + 1}`}
							href={`#L${index + 1}`}
							aria-label={`Line ${index + 1}`}
						>{index + 1}</a>{/each}</pre>
				<pre class="code"><code class="hljs">{@html highlighted}</code></pre>
			</article>
		{:else}
			<div class="empty">
				<strong>Covalence source tree</strong>
				<p>Choose a tracked plaintext file from the repository tree.</p>
			</div>
		{/if}
	</section>
</main>

<style>
	main {
		display: grid;
		grid-template-columns: minmax(15rem, 22rem) minmax(0, 1fr);
		height: 100vh;
		padding-top: 2.35rem;
		overflow: hidden;
	}
	aside {
		overflow: auto;
		padding: 0 0.7rem 3rem;
		border-right: 1px solid var(--border);
		background: var(--surface);
	}
	.tree-head {
		position: sticky;
		z-index: 2;
		top: 0;
		display: flex;
		justify-content: space-between;
		padding: 0.8rem 0.35rem;
		background: var(--surface);
		font-size: 0.75rem;
	}
	.tree-head span { color: var(--muted); }
	.source { min-width: 0; overflow: auto; }
	header {
		position: sticky;
		z-index: 2;
		top: 0;
		padding: 0.8rem 1.25rem;
		border-bottom: 1px solid var(--border);
		background: color-mix(in srgb, var(--bg) 94%, transparent);
		backdrop-filter: blur(10px);
	}
	h1 { margin: 0; overflow-wrap: anywhere; font-size: 0.95rem; }
	p { margin: 0.25rem 0 0; color: var(--muted); font-size: 0.7rem; }
	article {
		display: grid;
		grid-template-columns: max-content max-content;
		min-width: max-content;
		padding: 0.75rem 0 4rem;
	}
	pre { margin: 0; font: 0.82rem/1.55 var(--font-mono); }
	.numbers {
		position: sticky;
		z-index: 1;
		left: 0;
		padding-right: 1rem;
		background: var(--bg);
	}
	.numbers a {
		display: block;
		width: 4rem;
		color: #626273;
		text-align: right;
		text-decoration: none;
		user-select: none;
		scroll-margin-top: 5rem;
	}
	.numbers a:hover, .numbers a:target { color: var(--accent); background: var(--surface); }
	.code { padding-right: 2rem; }
	code { display: block; color: var(--fg); font: inherit; white-space: pre; }
	.empty { display: grid; place-content: center; min-height: 70vh; color: var(--muted); text-align: center; }
	.empty strong { color: var(--fg); }

	:global(.hljs-keyword), :global(.hljs-selector-tag), :global(.hljs-built_in),
	:global(.hljs-type), :global(.hljs-title), :global(.hljs-section) { color: #7cc4f5; }
	:global(.hljs-string), :global(.hljs-regexp), :global(.hljs-addition) { color: #a8e6a3; }
	:global(.hljs-number), :global(.hljs-literal), :global(.hljs-symbol) { color: #f5c07c; }
	:global(.hljs-variable), :global(.hljs-template-variable), :global(.hljs-attr) { color: #c9a0f5; }
	:global(.hljs-comment), :global(.hljs-quote) { color: var(--muted); font-style: italic; }
	:global(.hljs-meta) { color: #f5c07c; }

	@media (max-width: 720px) {
		main { grid-template-columns: 12rem minmax(0, 1fr); }
	}
</style>
