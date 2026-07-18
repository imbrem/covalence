<script lang="ts">
	import { KnowledgeGraphView } from 'covalence-ui';

	type Kind = 'task' | 'todo' | 'term' | 'note' | 'file';
	type Mode = 'tasks' | 'neighborhood' | 'notes' | 'terms';
	type MapNode = {
		id: string;
		kind: Kind;
		title: string;
		status: string | null;
		path: string;
		words: number;
		updated: number;
	};
	type MapEdge = {
		source: string;
		predicate: string;
		target: string;
		detail: string | null;
	};

	let { data } = $props();
	let allNodes = $state<MapNode[]>(data.map.nodes);
	let allEdges = $state<MapEdge[]>(data.map.edges);
	let byId = $derived(new Map(allNodes.map((node) => [node.id, node])));
	let tasks = $derived(allNodes.filter((node) => node.kind === 'task'));
	let statuses = $derived(
		[
			...new Set(
				allNodes
					.filter((node) =>
						mode === 'tasks'
							? node.kind === 'task'
							: mode === 'notes'
								? node.kind === 'note'
								: mode === 'terms'
									? node.kind === 'term'
								: true,
					)
					.map((node) => node.status)
					.filter(Boolean),
			),
		].sort() as string[],
	);
	const kinds: Kind[] = ['task', 'todo', 'term', 'note', 'file'];

	let mode = $state<Mode>('tasks');
	let taskId = $state(allNodes.find((node) => node.kind === 'task')?.id ?? '');
	let query = $state('');
	let enabledKinds = $state<Kind[]>([...kinds]);
	let enabledStatuses = $state<string[]>([]);
	let selectedId = $state<string | null>(taskId || null);

	function toggle<T>(values: T[], value: T): T[] {
		return values.includes(value) ? values.filter((item) => item !== value) : [...values, value];
	}

	let baseIds = $derived.by(() => {
		const ids = new Set<string>();
		if (mode === 'tasks') {
			for (const node of tasks) ids.add(node.id);
		} else if (mode === 'neighborhood') {
			ids.add(taskId);
			for (const edge of allEdges) {
				if (edge.source === taskId) ids.add(edge.target);
				if (edge.target === taskId) ids.add(edge.source);
			}
		} else if (mode === 'notes') {
			for (const node of allNodes) {
				if (node.kind === 'note' || node.kind === 'file') ids.add(node.id);
			}
		} else {
			for (const node of allNodes) if (node.kind === 'term') ids.add(node.id);
			for (const edge of allEdges) {
				if (ids.has(edge.source)) ids.add(edge.target);
				if (ids.has(edge.target)) ids.add(edge.source);
			}
		}
		return ids;
	});

	let visibleNodes = $derived.by(() => {
		const q = query.trim().toLowerCase();
		return allNodes.filter((node) => {
			if (!baseIds.has(node.id) || !enabledKinds.includes(node.kind)) return false;
			if (enabledStatuses.length > 0 && !enabledStatuses.includes(node.status ?? '')) return false;
			return q === '' || `${node.title} ${node.path} ${node.id}`.toLowerCase().includes(q);
		});
	});

	let visibleIds = $derived(new Set(visibleNodes.map((node) => node.id)));
	let visibleEdges = $derived(
		allEdges.filter((edge) => {
			if (!visibleIds.has(edge.source) || !visibleIds.has(edge.target)) return false;
			if (mode === 'tasks') return ['depends-on', 'part-of'].includes(edge.predicate);
			if (mode === 'notes') {
				return ['links-to', 'documents', 'mentions'].includes(edge.predicate);
			}
			if (mode === 'terms') return ['defined-by', 'uses-term'].includes(edge.predicate);
			return true;
		}),
	);

	let selected = $derived(selectedId ? (byId.get(selectedId) ?? null) : null);
	let selectedEdges = $derived(
		selectedId
			? allEdges.filter((edge) => edge.source === selectedId || edge.target === selectedId)
			: [],
	);
	let visibleNotes = $derived(visibleNodes.filter((node) => node.kind === 'note'));
	let missingCount = $derived(visibleNodes.filter((node) => node.status === 'missing').length);

	function setMode(next: Mode) {
		mode = next;
		enabledStatuses = [];
		selectedId =
			next === 'neighborhood'
				? taskId
				: next === 'notes'
					? (allNodes.find((node) => node.kind === 'note')?.id ?? null)
					: next === 'terms'
						? (allNodes.find((node) => node.kind === 'term')?.id ?? null)
					: (tasks[0]?.id ?? null);
	}

	function selectTask(next: string) {
		taskId = next;
		selectedId = next;
	}
</script>

<svelte:head><title>Covalence map</title></svelte:head>

<main>
	<header>
		<div>
			<h1>Covalence map</h1>
			<p>
				Tasks, open work, notes, and code references loaded from
				<code>covalence-map.json</code>. Generate the local snapshot with
				<code>bun run notes</code>, or configure another data origin.
			</p>
		</div>
		<div class="totals">
			<strong>{visibleNodes.length}</strong> nodes ·
			<strong>{visibleEdges.length}</strong> edges ·
			<strong class:warning={missingCount > 0}>{missingCount}</strong> missing targets
		</div>
	</header>

	<section class="toolbar">
		<div class="tabs" aria-label="Map view">
			<button type="button" class:on={mode === 'tasks'} onclick={() => setMode('tasks')}>task DAG</button>
			<button type="button" class:on={mode === 'neighborhood'} onclick={() => setMode('neighborhood')}>
				task neighborhood
			</button>
			<button type="button" class:on={mode === 'notes'} onclick={() => setMode('notes')}>notes</button>
			<button type="button" class:on={mode === 'terms'} onclick={() => setMode('terms')}>terms</button>
		</div>

		{#if mode === 'neighborhood'}
			<label>
				task
				<select value={taskId} onchange={(event) => selectTask(event.currentTarget.value)}>
					{#each tasks as task}<option value={task.id}>{task.title}</option>{/each}
				</select>
			</label>
		{/if}

		<input bind:value={query} placeholder="search title, path, or id…" spellcheck="false" />

		<div class="filters">
			<span>kind</span>
			{#each kinds as kind}
				<button
					class="chip"
					class:on={enabledKinds.includes(kind)}
					onclick={() => (enabledKinds = toggle(enabledKinds, kind))}
				>{kind} <em>{allNodes.filter((node) => node.kind === kind).length}</em></button>
			{/each}
		</div>

		<div class="filters">
			<span>status</span>
			<button
				class="chip"
				class:on={enabledStatuses.length === 0}
				onclick={() => (enabledStatuses = [])}>all</button
			>
			{#each statuses as status}
				<button
					class="chip"
					class:on={enabledStatuses.includes(status)}
					onclick={() => (enabledStatuses = toggle(enabledStatuses, status))}
				>{status}</button>
			{/each}
		</div>
	</section>

	<div class="workspace">
		{#if mode === 'notes'}
			<section class="note-list" aria-label="Notes">
				{#each visibleNotes as note}
					<button
						class:selected={selectedId === note.id}
						title={note.title}
						onclick={() => (selectedId = note.id)}
					>
						<strong>{note.title}</strong>
						<span>{note.path}</span>
						<em>{note.status ?? 'no status'} · {note.words} words</em>
					</button>
				{/each}
			</section>
		{:else}
			<KnowledgeGraphView
			nodes={visibleNodes.map((node) => ({
				id: node.id,
				label: node.title,
				kind: node.kind,
				status: node.status,
			}))}
			edges={visibleEdges.map((edge, index) => ({
				id: `${edge.source}:${edge.predicate}:${edge.target}:${index}`,
				source: edge.source,
				target: edge.target,
				label: edge.predicate,
			}))}
			layout={mode === 'tasks' ? 'breadthfirst' : 'cose'}
			{selectedId}
			onselect={(id) => (selectedId = id)}
			/>
		{/if}

		<aside>
			{#if selected}
				<span class="kind">{selected.kind}</span>
				<h2>{selected.title}</h2>
				<dl>
					<dt>id</dt><dd>{selected.id}</dd>
					<dt>status</dt><dd class:warning={selected.status === 'missing'}>
						{selected.status ?? '—'}
					</dd>
					<dt>path</dt><dd>{selected.path}</dd>
					{#if selected.words > 0}<dt>words</dt><dd>{selected.words}</dd>{/if}
				</dl>
				{#if selected.kind === 'note' && selected.path.startsWith('notes/')}
					<a class="open-note" href={`/notes/${selected.path.slice('notes/'.length)}`}>
						open generated note page →
					</a>
				{/if}
				<h3>relationships ({selectedEdges.length})</h3>
				<ul>
					{#each selectedEdges as edge}
						{@const outgoing = edge.source === selected.id}
						{@const other = byId.get(outgoing ? edge.target : edge.source)}
						<li>
							<button onclick={() => (selectedId = other?.id ?? null)}>
								<span>{outgoing ? '→' : '←'} {edge.predicate}</span>
								<strong>{other?.title ?? (outgoing ? edge.target : edge.source)}</strong>
							</button>
						</li>
					{/each}
				</ul>
			{:else}
				<h2>Inspect the map</h2>
				<p>Select a node to see its status, source path, and all relationships.</p>
				<p><span class="missing-dot"></span> A red outline marks an unresolved note or code target.</p>
			{/if}
		</aside>
	</div>
</main>

<style>
	main {
		width: 100%;
		height: calc(100vh - 2.35rem);
		margin: 0;
		padding: 0.85rem 1rem 1rem;
		display: flex;
		flex-direction: column;
		overflow: hidden;
		font-family: var(--font-mono);
		color: var(--fg);
	}
	header {
		display: flex;
		justify-content: space-between;
		gap: 2rem;
		align-items: end;
		margin-bottom: 1rem;
	}
	h1 { margin: 0; font-size: 1.5rem; }
	header p { max-width: 52rem; color: var(--muted); font-size: 0.85rem; line-height: 1.5; }
	.totals { white-space: nowrap; color: var(--muted); font-size: 0.8rem; }
	.toolbar {
		display: flex;
		flex-wrap: wrap;
		align-items: center;
		gap: 0.6rem 1rem;
		padding: 0.75rem;
		border: 1px solid var(--border);
		border-radius: 6px;
		background: var(--surface);
		margin-bottom: 0.75rem;
	}
	button, input, select {
		font: inherit;
		font-size: 0.78rem;
	}
	.open-note {
		display: inline-block;
		margin: 0.75rem 0;
		color: var(--accent);
		font-size: 0.8rem;
	}
	button {
		color: var(--muted);
		background: transparent;
		border: 1px solid var(--border);
		border-radius: 4px;
		padding: 0.3rem 0.5rem;
		cursor: pointer;
	}
	button.on { color: var(--fg); border-color: var(--accent); background: color-mix(in srgb, var(--accent) 16%, transparent); }
	.tabs { display: flex; gap: 0.25rem; }
	input {
		min-width: 18rem;
		color: var(--fg);
		background: var(--bg);
		border: 1px solid var(--border);
		border-radius: 4px;
		padding: 0.38rem 0.55rem;
	}
	select { margin-left: 0.35rem; }
	.filters { display: flex; align-items: center; flex-wrap: wrap; gap: 0.25rem; }
	.filters > span { color: var(--muted); font-size: 0.72rem; text-transform: uppercase; }
	.chip em { opacity: 0.65; font-style: normal; }
	.workspace {
		display: grid;
		grid-template-columns: minmax(0, 1fr) 20rem;
		gap: 0.75rem;
		flex: 1;
		min-height: 0;
	}
	.note-list {
		height: 100%;
		min-height: 0;
		overflow: auto;
		padding: 0.5rem;
		border: 1px solid var(--border);
		border-radius: 6px;
		background: #0f172a;
	}
	.note-list button {
		display: grid;
		width: 100%;
		grid-template-columns: minmax(0, 1fr) auto;
		gap: 0.25rem 1rem;
		margin-bottom: 0.35rem;
		padding: 0.65rem;
		text-align: left;
	}
	.note-list button.selected { border-color: var(--accent); }
	.note-list strong {
		overflow: hidden;
		text-overflow: ellipsis;
		white-space: nowrap;
		color: var(--fg);
	}
	.note-list span {
		grid-row: 2;
		overflow: hidden;
		text-overflow: ellipsis;
		white-space: nowrap;
		color: var(--muted);
	}
	.note-list em {
		grid-column: 2;
		grid-row: 1 / span 2;
		align-self: center;
		color: var(--muted);
		font-style: normal;
		font-size: 0.7rem;
	}
	aside {
		height: 100%;
		min-height: 0;
		overflow: auto;
		padding: 1rem;
		border: 1px solid var(--border);
		border-radius: 6px;
		background: var(--surface);
	}
	aside h2 { margin: 0.25rem 0 1rem; font-size: 1rem; overflow-wrap: anywhere; }
	aside h3 { margin-top: 1.25rem; font-size: 0.8rem; color: var(--muted); }
	aside p, dl, li { font-size: 0.75rem; line-height: 1.45; }
	.kind { color: var(--accent); font-size: 0.7rem; text-transform: uppercase; }
	dl { display: grid; grid-template-columns: 3.5rem minmax(0, 1fr); gap: 0.35rem; }
	dt { color: var(--muted); }
	dd { margin: 0; overflow-wrap: anywhere; }
	ul { padding: 0; list-style: none; }
	li button { display: block; width: 100%; text-align: left; margin-bottom: 0.3rem; overflow-wrap: anywhere; }
	li span { display: block; color: var(--muted); margin-bottom: 0.15rem; }
	li strong { color: var(--fg); }
	.warning { color: #ef4444; }
	.missing-dot { display: inline-block; width: 0.7rem; height: 0.7rem; border: 2px solid #ef4444; border-radius: 50%; }
	@media (max-width: 850px) {
		main { height: auto; min-height: calc(100vh - 2.35rem); overflow: visible; }
		header { display: block; }
		.workspace { grid-template-columns: 1fr; }
		.workspace > :global(.frame), .note-list { min-height: 65vh; }
		aside { height: auto; max-height: none; }
		input { min-width: 12rem; flex: 1; }
	}
</style>
