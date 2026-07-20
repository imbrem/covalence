<script lang="ts">
	import '../app.css';
	let { children } = $props();
</script>

<nav>
	<strong>covalence</strong>
	<a href="/?view=map" data-sveltekit-reload>map</a>
	<a href="/?view=history" data-sveltekit-reload>history</a>
	<a href="/?view=notes" data-sveltekit-reload>notes</a>
	<a href="/source" data-sveltekit-reload>source</a>
	<a href="/?view=terms" data-sveltekit-reload>terms</a>
	<a href="/?view=apis" data-sveltekit-reload>APIs</a>
</nav>

{@render children()}

<style>
	nav {
		position: fixed;
		z-index: 20;
		top: 0;
		left: 0;
		right: 0;
		display: flex;
		align-items: baseline;
		gap: 1rem;
		padding: 0.65rem 1rem;
		border-bottom: 1px solid var(--border);
		background: color-mix(in srgb, var(--surface) 88%, transparent);
		backdrop-filter: blur(12px);
		font-size: 0.8rem;
	}
	strong { color: var(--accent); }
	a {
		color: var(--muted);
		text-decoration: none;
	}
	a:hover { color: var(--fg); }
</style>
