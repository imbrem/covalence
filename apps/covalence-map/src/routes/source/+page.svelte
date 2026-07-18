<script lang="ts">
	let { data } = $props();
	let lines = $derived(data.file.content.split('\n'));
</script>

<svelte:head><title>{data.file.path} · Covalence map</title></svelte:head>

<main>
	<header>
		<a href="/">← map</a>
		<div>
			<h1>{data.file.path}</h1>
			<p>{data.file.language} · {data.file.lines} lines · {data.provider}</p>
		</div>
	</header>
	<article aria-label={`Source for ${data.file.path}`}>
		<pre>{#each lines as line, index}<span class="line" id={`L${index + 1}`}><a
						class="number"
						href={`#L${index + 1}`}
						aria-label={`Line ${index + 1}`}
					>{index + 1}</a><code>{line || ' '}</code></span>{/each}</pre>
	</article>
</main>

<style>
	main { min-height: 100vh; padding: 2.35rem 0 4rem; }
	header {
		position: sticky;
		z-index: 2;
		top: 2.35rem;
		display: flex;
		align-items: center;
		gap: 1.25rem;
		padding: 0.8rem 1.25rem;
		border-bottom: 1px solid var(--border);
		background: color-mix(in srgb, var(--bg) 94%, transparent);
		backdrop-filter: blur(10px);
	}
	header > div { min-width: 0; }
	h1 { margin: 0; overflow-wrap: anywhere; font-size: 0.95rem; }
	p { margin: 0.25rem 0 0; color: var(--muted); font-size: 0.7rem; }
	a { color: var(--accent); font-size: 0.8rem; white-space: nowrap; }
	article { overflow: auto; padding: 0.75rem 0; }
	pre { min-width: max-content; margin: 0; font: 0.82rem/1.55 var(--font-mono); }
	.line {
		display: block;
		min-height: 1.55em;
		padding-right: 1.25rem;
		scroll-margin-top: 6rem;
	}
	.line:target { background: color-mix(in srgb, var(--accent) 18%, transparent); }
	.number {
		display: inline-block;
		width: 5rem;
		padding-right: 1rem;
		color: #626273;
		text-align: right;
		text-decoration: none;
		user-select: none;
	}
	.line:hover { background: color-mix(in srgb, var(--surface) 70%, transparent); }
	.line:hover .number { color: var(--accent); }
	code { color: var(--fg); font: inherit; white-space: pre; }
</style>
