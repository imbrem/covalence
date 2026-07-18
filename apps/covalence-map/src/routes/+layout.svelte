<script lang="ts">
	import '../app.css';
	let { children } = $props();
</script>

<nav>
	<strong>covalence map</strong>
	<span>notes · tasks · open work · source</span>
</nav>

{@render children()}

<style>
	nav {
		display: flex;
		align-items: baseline;
		gap: 1rem;
		padding: 0.65rem 1rem;
		border-bottom: 1px solid var(--border);
		background: var(--surface);
		font-size: 0.8rem;
	}
	strong { color: var(--accent); }
	span { color: var(--muted); }
</style>
