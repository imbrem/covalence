<script lang="ts">
	import { fetchApi } from '$lib/api';

	interface Info {
		version: string;
		cog_version: string;
		target: string;
		cwd: string;
	}

	interface Health {
		status: string;
		version: string;
		cog_version: string;
		target: string;
		uptime_secs: number;
	}

	let info: Info | null = $state(null);
	let error: string | null = $state(null);

	/** Health poll interval in ms. Change this to adjust polling frequency. */
	const HEALTH_POLL_MS = 1000;

	let healthy = $state(false);
	let lastHealth: Health | null = $state(null);
	let connectedSince: number | null = $state(null);
	let connectedDuration = $state(0);
	let timer: ReturnType<typeof setTimeout> | null = null;
	let tickTimer: ReturnType<typeof setInterval> | null = null;

	$effect(() => {
		fetchApi<Info>('/api/info')
			.then((data) => {
				info = data;
				error = null;
			})
			.catch((e) => (error = e instanceof Error ? e.message : String(e)));
	});

	async function poll() {
		try {
			lastHealth = await fetchApi<Health>('/api/health');
			if (!healthy) {
				healthy = true;
				connectedSince = Date.now();
				startTick();
			}
			// Also refresh info on reconnect
			if (error) {
				try {
					info = await fetchApi<Info>('/api/info');
					error = null;
				} catch {}
			}
		} catch {
			if (healthy) {
				healthy = false;
				connectedSince = null;
				connectedDuration = 0;
				stopTick();
			}
		}
		timer = setTimeout(poll, HEALTH_POLL_MS);
	}

	function startTick() {
		stopTick();
		tickTimer = setInterval(() => {
			if (connectedSince != null) {
				connectedDuration = Math.floor((Date.now() - connectedSince) / 1000);
			}
		}, 1000);
	}

	function stopTick() {
		if (tickTimer != null) {
			clearInterval(tickTimer);
			tickTimer = null;
		}
	}

	function forcePing() {
		if (timer != null) clearTimeout(timer);
		poll();
	}

	function formatDuration(secs: number): string {
		const h = Math.floor(secs / 3600);
		const m = Math.floor((secs % 3600) / 60);
		const s = secs % 60;
		if (h > 0) return `${h}h ${m}m ${s}s`;
		if (m > 0) return `${m}m ${s}s`;
		return `${s}s`;
	}

	$effect(() => {
		poll();
		return () => {
			if (timer != null) clearTimeout(timer);
			stopTick();
		};
	});
</script>

<main>
	<h1>covalence</h1>

	{#if error && !info}
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

	<section class="health">
		<button class="health-dot" class:healthy class:unhealthy={!healthy} onclick={forcePing}
			title={healthy ? 'API connected — click to refresh' : 'API unreachable — click to retry'}
		></button>

		<span class="health-label">
			{#if healthy && lastHealth}
				connected {formatDuration(connectedDuration)} — server up {formatDuration(Math.floor(lastHealth.uptime_secs))}
			{:else}
				API unreachable
			{/if}
		</span>
	</section>
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

	.health {
		margin-top: 2rem;
		display: flex;
		align-items: center;
		gap: 0.75rem;
	}

	.health-dot {
		width: 12px;
		height: 12px;
		border-radius: 50%;
		border: none;
		cursor: pointer;
		padding: 0;
		flex-shrink: 0;
	}

	.health-dot.healthy {
		background: #4ade80;
		box-shadow: 0 0 6px #4ade8066;
	}

	.health-dot.unhealthy {
		background: #f87171;
		box-shadow: 0 0 6px #f8717166;
	}

	.health-label {
		font-size: 0.85rem;
		color: var(--muted);
	}
</style>
