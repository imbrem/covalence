<script lang="ts">
	import '../app.css';
	import { page } from '$app/stores';

	let { children } = $props();

	const links = [
		{ href: '/', label: 'repl' },
		{ href: '/deps', label: 'dep tree' },
		{ href: '/tcb', label: 'tcb audit' },
		{ href: '/haskell', label: 'haskell' },
		{ href: '/proofs', label: 'proof checker' },
		{ href: '/graph', label: 'graph viewer' },
		{ href: '/metamath', label: 'metamath' },
	];

	// Normalize trailing slash for active-link matching.
	let path = $derived($page.url.pathname.replace(/\/+$/, '') || '/');
</script>

<nav class="cov-nav">
	<span class="brand">covalence</span>
	{#each links as l}
		<a href={l.href} class:active={path === l.href} data-sveltekit-preload-data="hover">{l.label}</a>
	{/each}
</nav>

<div class="cov-body">
	{@render children()}
</div>

<style>
	.cov-nav {
		display: flex;
		align-items: center;
		gap: 0.25rem;
		padding: 0.4rem 1rem;
		border-bottom: 1px solid var(--border);
		background: var(--surface);
		font-family: var(--font-mono);
		font-size: 0.8rem;
		flex-wrap: wrap;
	}
	.cov-nav .brand {
		color: var(--accent);
		font-weight: 700;
		margin-right: 0.75rem;
		letter-spacing: 0.02em;
	}
	.cov-nav a {
		color: var(--muted);
		text-decoration: none;
		padding: 0.15rem 0.5rem;
		border-radius: 4px;
	}
	.cov-nav a:hover {
		color: var(--fg);
		background: color-mix(in srgb, var(--fg) 8%, transparent);
	}
	.cov-nav a.active {
		color: var(--fg);
		background: color-mix(in srgb, var(--accent) 22%, transparent);
	}
	/* The REPL route is height:100vh; give the nav its own space so both
	   fit in the viewport without the page scrolling as a whole. */
	.cov-body {
		height: calc(100vh - 2.2rem);
		overflow: auto;
	}
</style>
