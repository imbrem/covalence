<script lang="ts">
	import { fetchApi } from '$lib/api';

	interface Info {
		version: string;
		cog_version: string;
		target: string;
		cwd: string;
	}

	let info: Info | null = $state(null);
	let error: string | null = $state(null);

	$effect(() => {
		fetchApi<Info>('/api/info')
			.then((data) => (info = data))
			.catch((e) => (error = e instanceof Error ? e.message : String(e)));
	});
</script>

<main>
	<h1>covalence</h1>

	{#if error}
		<p class="error">Failed to connect: {error}</p>
	{:else if info}
		<dl>
			<dt>version</dt>
			<dd>{info.version}</dd>
			<dt>cog version</dt>
			<dd>{info.cog_version}</dd>
			<dt>target</dt>
			<dd>{info.target}</dd>
			<dt>cwd</dt>
			<dd>{info.cwd}</dd>
		</dl>
	{:else}
		<p class="loading">connecting...</p>
	{/if}
</main>

<style>
	main {
		max-width: 600px;
		margin: 4rem auto;
		padding: 0 1.5rem;
	}

	h1 {
		font-size: 1.5rem;
		font-weight: 400;
		color: var(--accent);
		margin-bottom: 2rem;
	}

	dl {
		display: grid;
		grid-template-columns: auto 1fr;
		gap: 0.5rem 1.5rem;
	}

	dt {
		color: var(--muted);
	}

	dd {
		word-break: break-all;
	}

	.error {
		color: #f87171;
	}

	.loading {
		color: var(--muted);
	}
</style>
