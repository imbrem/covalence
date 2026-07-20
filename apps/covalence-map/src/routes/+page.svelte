<script lang="ts">
	import { KnowledgeGraphView } from 'covalence-ui';

	type Kind = 'task' | 'todo' | 'term' | 'note' | 'file' | 'api' | 'implementation';
	type Mode = 'tasks' | 'neighborhood' | 'history' | 'notes' | 'terms' | 'source' | 'apis';
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
	type NoteMetadata = {
		noteId: string;
		stableId: string;
		review: string;
		format: string;
	};
	type HistorySnapshot = {
		commit: string;
		overview: MapNode | null;
		reports: MapNode[];
		updated: number;
	};

	let { data } = $props();
	let allNodes = $state<MapNode[]>(data.map.nodes);
	let allEdges = $state<MapEdge[]>(data.map.edges);
	let byId = $derived(new Map(allNodes.map((node) => [node.id, node])));
	let noteStableIds = $derived(
		new Map(
			(data.map.noteMetadata as NoteMetadata[]).map((metadata) => [
				metadata.noteId,
				metadata.stableId,
			]),
		),
	);
	let tasks = $derived(allNodes.filter((node) => node.kind === 'task'));
	let statuses = $derived(
		[
			...new Set(
				allNodes
					.filter((node) =>
						mode === 'tasks'
							? node.kind === 'task'
							: mode === 'notes' || mode === 'history'
								? node.kind === 'note'
							: mode === 'terms'
									? node.kind === 'term'
									: mode === 'source'
										? node.kind === 'file'
								: true,
					)
					.map((node) => node.status)
					.filter(Boolean),
			),
		].sort() as string[],
	);
	const kinds: Kind[] = ['task', 'todo', 'term', 'api', 'implementation', 'note', 'file'];

	let mode = $state<Mode>(
		data.view === 'history'
			? 'history'
			: data.view === 'notes'
			? 'notes'
			: data.view === 'source'
				? 'source'
				: data.view === 'terms'
					? 'terms'
					: data.view === 'apis'
						? 'apis'
					: 'tasks',
	);
	let taskId = $state(allNodes.find((node) => node.kind === 'task')?.id ?? '');
	let query = $state('');
	let enabledKinds = $state<Kind[]>([...kinds]);
	let enabledStatuses = $state<string[]>([]);
	let selectedId = $state<string | null>(null);

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
		} else if (mode === 'history') {
			for (const node of allNodes) {
				if (node.kind === 'note' && node.path.startsWith('notes/history/')) ids.add(node.id);
			}
		} else if (mode === 'terms') {
			for (const node of allNodes) if (node.kind === 'term') ids.add(node.id);
			for (const edge of allEdges) {
				if (ids.has(edge.source)) ids.add(edge.target);
				if (ids.has(edge.target)) ids.add(edge.source);
			}
		} else if (mode === 'apis') {
			for (const node of allNodes) {
				if (node.kind === 'api' || node.kind === 'implementation') ids.add(node.id);
			}
			for (const edge of allEdges) {
				if (ids.has(edge.source)) ids.add(edge.target);
				if (ids.has(edge.target)) ids.add(edge.source);
			}
		} else {
			for (const node of allNodes) if (node.kind === 'file') ids.add(node.id);
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
			if (mode === 'notes' || mode === 'history') {
				return ['links-to', 'documents', 'mentions'].includes(edge.predicate);
			}
			if (mode === 'terms') return ['defined-by', 'uses-term'].includes(edge.predicate);
			if (mode === 'apis') return ['depends-on', 'implements', 'defined-in'].includes(edge.predicate);
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
	let historyIndex = $derived(
		allNodes.find((node) => node.kind === 'note' && node.path === 'notes/history/README.md') ?? null,
	);
	let historySnapshots = $derived.by(() => {
		const q = query.trim().toLowerCase();
		const snapshots = new Map<string, HistorySnapshot>();
		for (const node of allNodes) {
			if (node.kind !== 'note' || !node.path.startsWith('notes/history/') || node === historyIndex) continue;
			const [commit, file] = node.path.slice('notes/history/'.length).split('/');
			if (!commit || !file) continue;
			const snapshot = snapshots.get(commit) ?? { commit, overview: null, reports: [], updated: 0 };
			if (file === 'README.md') snapshot.overview = node;
			else snapshot.reports.push(node);
			snapshot.updated = Math.max(snapshot.updated, node.updated);
			snapshots.set(commit, snapshot);
		}
		return [...snapshots.values()]
			.filter((snapshot) => {
				if (!q) return true;
				return [snapshot.overview, ...snapshot.reports]
					.filter((node): node is MapNode => node !== null)
					.some((node) => `${node.title} ${node.path} ${node.id}`.toLowerCase().includes(q));
			})
			.map((snapshot) => ({
				...snapshot,
				reports: snapshot.reports.sort((a, b) => a.title.localeCompare(b.title)),
			}))
			.sort((a, b) => b.commit.localeCompare(a.commit));
	});
	let visibleFiles = $derived(visibleNodes.filter((node) => node.kind === 'file'));
	let missingCount = $derived(visibleNodes.filter((node) => node.status === 'missing').length);

	function setMode(next: Mode) {
		mode = next;
		enabledStatuses = [];
		selectedId =
			next === 'neighborhood'
				? taskId
				: next === 'notes' || next === 'history'
					? (allNodes.find((node) =>
							next === 'history' ? node.path === 'notes/history/README.md' : node.kind === 'note',
						)?.id ?? null)
					: next === 'terms'
						? (allNodes.find((node) => node.kind === 'term')?.id ?? null)
						: next === 'apis'
							? (allNodes.find((node) => node.kind === 'api')?.id ?? null)
						: next === 'source'
							? (allNodes.find((node) => node.kind === 'file')?.id ?? null)
					: (tasks[0]?.id ?? null);
	}

	function selectTask(next: string) {
		taskId = next;
		selectedId = next;
	}

	function noteHref(note: MapNode): string {
		return `/notes/${note.path.slice('notes/'.length)}`;
	}

	function formatDate(timestamp: number): string {
		return timestamp > 0
			? new Intl.DateTimeFormat(undefined, { dateStyle: 'medium', timeStyle: 'short' }).format(timestamp * 1000)
			: 'date unavailable';
	}
</script>

<svelte:head><title>Covalence map</title></svelte:head>

<main>
	{#if mode !== 'history'}
		<details class="toolbar" open={mode === 'notes' || mode === 'source'}>
		<summary>
			<span>{mode === 'tasks' ? 'task DAG' : mode}</span>
			<em>{visibleNodes.length} nodes · {visibleEdges.length} edges</em>
		</summary>
		<div class="controls">
		<div class="tabs" aria-label="Map view">
			<button type="button" class:on={mode === 'tasks'} onclick={() => setMode('tasks')}>task DAG</button>
			<button type="button" class:on={mode === 'neighborhood'} onclick={() => setMode('neighborhood')}>
				task neighborhood
			</button>
			<button type="button" class:on={mode === 'terms'} onclick={() => setMode('terms')}>terms</button>
			<button type="button" class:on={mode === 'apis'} onclick={() => setMode('apis')}>core APIs</button>
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
		<div class="totals">
			<strong class:warning={missingCount > 0}>{missingCount}</strong> missing targets
		</div>
		</div>
		</details>
	{/if}

	<div class="workspace">
		{#if mode === 'history'}
			<section class="history-page" aria-label="History timeline">
				<header class="history-header">
					<div>
						<p class="eyebrow">Repository record</p>
						<h1>History</h1>
						<p>Immutable, commit-addressed snapshots of what exists, what is missing, and what comes next.</p>
					</div>
					<div class="history-actions">
						<input bind:value={query} aria-label="Search history" placeholder="search snapshots and reports…" spellcheck="false" />
						{#if historyIndex}<a href={noteHref(historyIndex)}>history conventions →</a>{/if}
					</div>
				</header>

				<div class="timeline">
					{#if historySnapshots.length === 0}
						<p class="empty">No historical snapshots match this search.</p>
					{/if}
					{#each historySnapshots as snapshot}
						<article class="snapshot">
							<div class="timeline-marker" aria-hidden="true"></div>
							<div class="snapshot-card">
								<div class="snapshot-heading">
									<div>
										<span class="commit">{snapshot.commit}</span>
										<h2>{snapshot.overview?.title ?? `Snapshot ${snapshot.commit}`}</h2>
									</div>
									<time>{formatDate(snapshot.updated)}</time>
								</div>
								{#if snapshot.overview}
									<a class="overview-link" href={noteHref(snapshot.overview)}>read snapshot overview →</a>
								{/if}
								<div class="report-grid">
									{#each snapshot.reports as report}
										<a href={noteHref(report)}>
											<b>{noteStableIds.get(report.id)}</b>
											<strong>{report.title}</strong>
											<em>{report.words} words</em>
										</a>
									{/each}
								</div>
							</div>
						</article>
					{/each}
				</div>
			</section>
		{:else if mode === 'notes' || mode === 'source'}
			<section class="note-list" aria-label={mode === 'notes' ? 'Notes' : 'Source files'}>
				{#each mode === 'notes' ? visibleNotes : visibleFiles as note}
					<a
						title={note.title}
						href={mode === 'notes'
							? `/notes/${note.path.slice('notes/'.length)}`
							: `/source?path=${encodeURIComponent(note.path)}`}
					>
						<strong>
							{#if mode === 'notes'}<b>{noteStableIds.get(note.id)}</b>{/if}
							{note.title}
						</strong>
						<span>{note.path}</span>
						<em>{note.status ?? 'no status'} · {note.words} {mode === 'source' ? 'lines' : 'words'}</em>
					</a>
				{/each}
			</section>
		{:else}
			<KnowledgeGraphView
			nodes={visibleNodes.map((node) => ({
				id: node.id,
				label: node.kind === 'note'
					? (noteStableIds.get(node.id) ?? node.title)
					: node.kind === 'api'
						? `${node.id.slice(4)} · ${node.title}`
						: node.title,
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

		{#if selected}
		<aside>
				<button class="close" type="button" aria-label="Close inspector" onclick={() => (selectedId = null)}>×</button>
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
				{#if selected.kind === 'file' && selected.status !== 'missing'}
					<a class="open-note" href={`/source?path=${encodeURIComponent(selected.path)}`}>
						open source file →
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
		</aside>
		{/if}
	</div>
</main>

<style>
	main {
		width: 100%;
		height: 100vh;
		margin: 0;
		padding: 0;
		overflow: hidden;
		font-family: var(--font-mono);
		color: var(--fg);
	}
	.totals { white-space: nowrap; color: var(--muted); font-size: 0.8rem; }
	.toolbar {
		position: fixed;
		z-index: 12;
		top: 3.25rem;
		left: 1rem;
		width: min(42rem, calc(100vw - 2rem));
		border: 1px solid var(--border);
		border-radius: 8px;
		background: color-mix(in srgb, var(--surface) 90%, transparent);
		box-shadow: 0 12px 38px rgb(0 0 0 / 35%);
		backdrop-filter: blur(14px);
	}
	summary {
		display: flex;
		justify-content: space-between;
		gap: 1rem;
		padding: 0.65rem 0.8rem;
		cursor: pointer;
		list-style: none;
		font-size: 0.75rem;
	}
	summary::-webkit-details-marker { display: none; }
	summary span { color: var(--fg); }
	summary em { color: var(--muted); font-style: normal; }
	.controls {
		display: flex;
		flex-wrap: wrap;
		align-items: center;
		gap: 0.6rem 1rem;
		padding: 0 0.8rem 0.8rem;
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
		position: absolute;
		inset: 0;
	}
	.history-page {
		height: 100%;
		overflow: auto;
		padding: 6rem max(1.25rem, calc((100vw - 76rem) / 2)) 5rem;
		background:
			radial-gradient(circle at 85% 5%, color-mix(in srgb, var(--accent) 12%, transparent), transparent 28rem),
			var(--bg);
	}
	.history-header {
		display: flex;
		align-items: end;
		justify-content: space-between;
		gap: 2rem;
		margin-bottom: 3rem;
		padding-bottom: 1.5rem;
		border-bottom: 1px solid var(--border);
	}
	.history-header h1 { margin: 0.15rem 0 0.5rem; font-size: clamp(2rem, 5vw, 4.5rem); letter-spacing: -0.06em; }
	.history-header p { max-width: 48rem; margin: 0; color: var(--muted); line-height: 1.6; }
	.eyebrow { color: var(--accent) !important; font-size: 0.72rem; letter-spacing: 0.14em; text-transform: uppercase; }
	.history-actions { display: grid; flex: 0 1 27rem; gap: 0.65rem; }
	.history-actions input { width: 100%; min-width: 0; }
	.history-actions a { color: var(--accent); font-size: 0.75rem; text-align: right; text-decoration: none; }
	.timeline { position: relative; padding-left: 2.4rem; }
	.timeline::before {
		content: '';
		position: absolute;
		top: 0.8rem;
		bottom: 0;
		left: 0.45rem;
		width: 1px;
		background: linear-gradient(var(--accent), var(--border) 75%, transparent);
	}
	.snapshot { position: relative; margin-bottom: 2rem; }
	.timeline-marker {
		position: absolute;
		top: 0.65rem;
		left: -2.38rem;
		width: 0.9rem;
		height: 0.9rem;
		border: 3px solid var(--bg);
		border-radius: 50%;
		background: var(--accent);
		box-shadow: 0 0 0 1px var(--accent);
	}
	.snapshot-card {
		padding: 1.3rem;
		border: 1px solid var(--border);
		border-radius: 10px;
		background: color-mix(in srgb, var(--surface) 94%, transparent);
		box-shadow: 0 12px 32px rgb(0 0 0 / 18%);
	}
	.snapshot-heading { display: flex; justify-content: space-between; gap: 1rem; }
	.snapshot-heading h2 { margin: 0.35rem 0 0.8rem; font-size: 1.15rem; }
	.snapshot-heading time { color: var(--muted); font-size: 0.7rem; white-space: nowrap; }
	.commit { color: var(--accent); font-size: 0.75rem; }
	.overview-link { display: inline-block; margin-bottom: 1rem; color: var(--accent); font-size: 0.8rem; text-decoration: none; }
	.report-grid { display: grid; grid-template-columns: repeat(auto-fit, minmax(14rem, 1fr)); gap: 0.5rem; }
	.report-grid a {
		display: grid;
		grid-template-columns: auto minmax(0, 1fr);
		gap: 0.2rem 0.55rem;
		padding: 0.75rem;
		border: 1px solid var(--border);
		border-radius: 6px;
		color: inherit;
		background: var(--bg);
		text-decoration: none;
	}
	.report-grid a:hover { border-color: var(--accent); }
	.report-grid b { grid-row: 1 / span 2; color: var(--accent); font-size: 0.72rem; }
	.report-grid strong { overflow: hidden; text-overflow: ellipsis; white-space: nowrap; font-size: 0.8rem; }
	.report-grid em { color: var(--muted); font-size: 0.68rem; font-style: normal; }
	.note-list {
		height: 100%;
		min-height: 0;
		overflow: auto;
		padding: 7.5rem 1rem 2rem;
		background: var(--bg);
	}
	.note-list > a {
		display: grid;
		width: 100%;
		max-width: 72rem;
		grid-template-columns: minmax(0, 1fr) auto;
		gap: 0.25rem 1rem;
		margin: 0 auto 0.35rem;
		padding: 0.75rem;
		border: 1px solid var(--border);
		border-radius: 5px;
		color: inherit;
		background: var(--surface);
		text-align: left;
		text-decoration: none;
	}
	.note-list > a:hover { border-color: var(--accent); }
	.empty { max-width: 72rem; margin: 1rem auto; color: var(--muted); }
	.note-list strong {
		overflow: hidden;
		text-overflow: ellipsis;
		white-space: nowrap;
		color: var(--fg);
	}
	.note-list b {
		margin-right: 0.6rem;
		color: var(--accent);
		font-weight: 600;
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
		position: fixed;
		z-index: 11;
		top: 3.25rem;
		right: 1rem;
		bottom: 1rem;
		width: min(23rem, calc(100vw - 2rem));
		overflow: auto;
		padding: 1rem;
		border: 1px solid var(--border);
		border-radius: 8px;
		background: color-mix(in srgb, var(--surface) 92%, transparent);
		box-shadow: 0 12px 38px rgb(0 0 0 / 35%);
		backdrop-filter: blur(14px);
	}
	.close {
		float: right;
		border: 0;
		font-size: 1.15rem;
		line-height: 1;
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
		.toolbar { top: 3rem; }
		aside { top: auto; max-height: 55vh; }
		input { min-width: 12rem; flex: 1; }
		.history-header { align-items: stretch; flex-direction: column; }
		.history-actions { flex-basis: auto; }
		.history-actions a { text-align: left; }
		.snapshot-heading { flex-direction: column; }
	}
</style>
