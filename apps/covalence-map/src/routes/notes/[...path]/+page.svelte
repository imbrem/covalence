<script lang="ts">
	let { data } = $props();
</script>

<svelte:head><title>{data.title} · Covalence map</title></svelte:head>

<main>
	<a href="/">← map</a>
	<p class="path">{data.path}</p>
	<article>
		<pre>{data.content}</pre>
	</article>
</main>

<style>
	main {
		max-width: 68rem;
		margin: 2rem auto;
		padding: 0 1.25rem 5rem;
	}
	a { color: var(--accent); }
	.path { color: var(--muted); font-size: 0.8rem; margin: 1.5rem 0 0.5rem; }
	article {
		padding: 1.5rem;
		border: 1px solid var(--border);
		border-radius: 6px;
		background: var(--surface);
	}
	pre {
		margin: 0;
		white-space: pre-wrap;
		overflow-wrap: anywhere;
		font: 0.9rem/1.6 var(--font-mono);
	}
</style>
