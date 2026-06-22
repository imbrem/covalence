<script lang="ts">
	// TEMPORARY / THROWAWAY DEMO PAGE.
	// Driven by `?file=<hash>&user=<opt>`. With no `file` it's a landing input:
	// pick/download a `.mm`, POST it into a cached server session (clean REST),
	// then navigate to `?file=<hash>`. With a `file` it's the DB view: fetch the
	// cached graph by REST, kick off the kernel import by REST, and follow live
	// per-theorem status over a thin status WebSocket. Per-theorem detail
	// (proof + HOL info) is fetched lazily by REST on row select.
	import { browser } from '$app/environment';
	import { goto } from '$app/navigation';
	import { page } from '$app/stores';
	import { client } from '$lib/api';
	import type {
		MmStatusMessage,
		ImportedTheorem,
		ImportTheoremDetail,
		MmDbInfo,
		MmDbListEntry,
	} from 'covalence-client';

	// Named presets for the source dropdown. `custom` leaves the URL editable.
	const PRESETS: Record<string, { label: string; url: string; note: string }> = {
		hol: {
			label: 'hol.mm',
			url: 'https://raw.githubusercontent.com/metamath/set.mm/refs/heads/develop/hol.mm',
			note: '~151 thms · seconds',
		},
		set: {
			label: 'set.mm',
			url: 'https://raw.githubusercontent.com/metamath/set.mm/refs/heads/develop/set.mm',
			note: '~48 MB · ~47k thms · minutes',
		},
	};

	// --- routing: the page is driven by the URL ---------------------------
	const fileHash = $derived($page.url.searchParams.get('file'));
	const user = $derived($page.url.searchParams.get('user') ?? undefined);

	// --- landing state -----------------------------------------------------
	let preset = $state<'hol' | 'set' | 'custom'>('hol');
	let url = $state(PRESETS.hol.url);
	let hashInput = $state(''); // attach-by-hash input (no download)
	let workers = $state(0); // 0 = auto
	let landingMsg = $state('');
	let importing = $state(false); // landing: downloading/posting
	let serverDbs = $state<MmDbListEntry[]>([]); // "loaded on server" list

	// --- DB-view header info (origin/total) --------------------------------
	let dbInfo = $state<MmDbInfo | null>(null);
	let headerCopyMsg = $state('');

	// Choosing a preset fills the URL (still fully editable). `custom` clears it.
	function onPreset() {
		if (preset === 'custom') return;
		url = PRESETS[preset].url;
	}

	async function refreshServerDbs() {
		try {
			serverDbs = await client.mmDbList();
		} catch {
			serverDbs = [];
		}
	}

	function shortHash(h: string): string {
		return h.length > 16 ? `${h.slice(0, 8)}…${h.slice(-6)}` : h;
	}

	// --- DB-view phases ----------------------------------------------------
	// `loading` = fetching the cached graph; `notLoaded` = the session is gone
	// (e.g. after a server restart) — fall back to the landing input;
	// `importing` = the parallel prove phase flips each pending → proving →
	// proved/error.
	let phase = $state<'loading' | 'notLoaded' | 'graph' | 'importing' | 'done' | 'error'>(
		'loading',
	);
	let statusMsg = $state('');
	let total = $state(0);
	let done = $state(0);
	let currentLabel = $state('');
	let elapsedMs = $state(0);
	let nOk = $state(0);
	let theorems = $state<ImportedTheorem[]>([]);
	// label → index into `theorems`, for O(1) status updates (47k theorems × ~2
	// updates each — must not be O(n) per message). Not reactive; a plain Map.
	let labelIndex = new Map<string, number>();
	let selected = $state<ImportedTheorem | null>(null);
	// Lazily-fetched full per-theorem detail (proof + essentials + HOL), cached
	// client-side so re-selecting a row doesn't re-fetch.
	let detail = $state<ImportTheoremDetail | null>(null);
	const detailCache = new Map<string, ImportTheoremDetail>();
	let failuresOnly = $state(false);
	let search = $state('');
	let sortBy = $state<'order' | 'slow' | 'fast' | 'deps' | 'label'>('order');
	let showHisto = $state(false);
	let copyMsg = $state('');
	let ws: WebSocket | null = null;
	// The hash the current DB view was loaded for (guards re-loads on URL churn).
	let loadedHash: string | null = null;

	// Live status tallies (the foundation of the general "task view").
	const nPending = $derived(theorems.filter((t) => t.status === 'pending').length);
	const nProving = $derived(theorems.filter((t) => t.status === 'proving').length);
	const nProved = $derived(theorems.filter((t) => t.status === 'proved').length);
	const failures = $derived(theorems.filter((t) => t.status === 'error'));
	const nErr = $derived(failures.length);
	const timed = $derived(theorems.filter((t) => t.importMs != null));
	const totalMs = $derived(timed.reduce((a, t) => a + (t.importMs ?? 0), 0));
	const avgMs = $derived(timed.length ? totalMs / timed.length : 0);
	const slowest = $derived(
		timed.reduce<ImportedTheorem | null>(
			(m, t) => ((t.importMs ?? 0) > (m?.importMs ?? -1) ? t : m),
			null,
		),
	);
	// Label → theorem, for transitive dependency walks.
	const byLabel = $derived.by(() => {
		const m = new Map<string, ImportedTheorem>();
		for (const t of theorems) m.set(t.label, t);
		return m;
	});

	// The **transitive axiom base** of a theorem: the union of axiom/def labels
	// reached by recursively following theorem (`thm`) dependencies — i.e. the
	// axioms+definitions this theorem ultimately rests on, not just the ones its
	// own proof cites directly. Computed from the accumulated per-theorem `deps`.
	function transitiveAxiomBase(root: string): {
		axioms: string[];
		defs: string[];
		thms: number;
		missing: number;
	} {
		const axioms = new Set<string>();
		const defs = new Set<string>();
		const visited = new Set<string>();
		const missing = new Set<string>();
		const stack = [root];
		while (stack.length) {
			const lbl = stack.pop()!;
			if (visited.has(lbl)) continue;
			visited.add(lbl);
			const t = byLabel.get(lbl);
			if (!t) continue;
			for (const d of t.deps ?? []) {
				if (d.kind === 'axiom') axioms.add(d.label);
				else if (d.kind === 'def') defs.add(d.label);
				else if (!byLabel.has(d.label)) missing.add(d.label);
				else if (!visited.has(d.label)) stack.push(d.label);
			}
		}
		return {
			axioms: [...axioms].sort(),
			defs: [...defs].sort(),
			thms: visited.size - 1, // distinct theorems reached (excluding the root)
			missing: missing.size,
		};
	}
	const axiomBase = $derived(selected ? transitiveAxiomBase(selected.label) : null);

	// Filter: failures-only AND a case-insensitive substring match on label OR mm.
	const filtered = $derived.by(() => {
		const q = search.trim().toLowerCase();
		let list = failuresOnly ? failures : theorems;
		if (q) {
			list = list.filter(
				(t) => t.label.toLowerCase().includes(q) || t.mm.toLowerCase().includes(q),
			);
		}
		return list;
	});

	// Sort the (filtered) list. `order` = import/completion order; `slow`/`fast`
	// by import time (to inspect the stragglers — sort by speed); `deps` by direct
	// dependency count (often correlated with slowness); `label` alphabetical.
	const sorted = $derived.by(() => {
		const list = filtered.slice();
		switch (sortBy) {
			case 'slow':
				return list.sort((a, b) => (b.importMs ?? -1) - (a.importMs ?? -1));
			case 'fast':
				return list.sort((a, b) => (a.importMs ?? Infinity) - (b.importMs ?? Infinity));
			case 'deps':
				return list.sort((a, b) => (b.deps?.length ?? 0) - (a.deps?.length ?? 0));
			case 'label':
				return list.sort((a, b) => a.label.localeCompare(b.label));
			default:
				return list;
		}
	});

	// --- list virtualization ----------------------------------------------
	// The list can hold ~60k rows; rendering them all (and re-rendering during
	// the live status updates) is what made the page lag. Render only the rows
	// in a slightly-overscanned viewport. Rows are fixed-height (ROW_H, matched
	// exactly in CSS); an outer spacer is sized to the full height and the
	// rendered slice is offset with translateY.
	const ROW_H = 26; // px — must match `.rows .item` height in CSS
	const OVERSCAN = 8;
	let scrollTop = $state(0);
	let viewportH = $state(0);
	let rowsEl = $state<HTMLDivElement | null>(null);

	$effect(() => {
		if (!rowsEl) return;
		viewportH = rowsEl.clientHeight;
		const ro = new ResizeObserver(() => {
			if (rowsEl) viewportH = rowsEl.clientHeight;
		});
		ro.observe(rowsEl);
		return () => ro.disconnect();
	});

	const vStart = $derived(Math.max(0, Math.floor(scrollTop / ROW_H) - OVERSCAN));
	const vCount = $derived(Math.ceil((viewportH || 0) / ROW_H) + 2 * OVERSCAN);
	const vRows = $derived(sorted.slice(vStart, vStart + vCount));
	const totalH = $derived(sorted.length * ROW_H);
	const offsetY = $derived(vStart * ROW_H);

	function onRowsScroll(e: Event) {
		scrollTop = (e.currentTarget as HTMLDivElement).scrollTop;
	}

	// --- timing statistics -------------------------------------------------
	// Linear-interpolation quantile (the "type 7" / numpy default): for p in
	// [0,1] over a sorted ascending array, index = p*(n-1), interpolate between
	// the two surrounding samples.
	function quantile(sorted: number[], p: number): number {
		const n = sorted.length;
		if (n === 0) return 0;
		if (n === 1) return sorted[0];
		const idx = p * (n - 1);
		const lo = Math.floor(idx);
		const hi = Math.ceil(idx);
		if (lo === hi) return sorted[lo];
		const frac = idx - lo;
		return sorted[lo] * (1 - frac) + sorted[hi] * frac;
	}
	const sortedMs = $derived(
		timed
			.map((t) => t.importMs ?? 0)
			.slice()
			.sort((a, b) => a - b),
	);
	const stats = $derived(
		sortedMs.length
			? {
					min: sortedMs[0],
					q1: quantile(sortedMs, 0.25),
					median: quantile(sortedMs, 0.5),
					q3: quantile(sortedMs, 0.75),
					max: sortedMs[sortedMs.length - 1],
				}
			: null,
	);

	// --- histogram (LOG-scale buckets over importMs) -----------------------
	// Import times are heavy-tailed (most theorems fast, a few slow stragglers),
	// so linear buckets crush everything into bucket 0 with a far-right tail.
	// Bucket on log10(ms) instead; clamp to a small floor so 0 ms is well-defined.
	const HISTO_BUCKETS = 30;
	const histo = $derived.by(() => {
		const xs = sortedMs;
		if (xs.length === 0) return null;
		const min = xs[0];
		const max = xs[xs.length - 1];
		const EPS = 0.01; // ms floor for the log
		const lo = Math.log10(Math.max(min, EPS));
		const hi = Math.log10(Math.max(max, EPS));
		const span = hi - lo || 1;
		const counts = new Array<number>(HISTO_BUCKETS).fill(0);
		for (const x of xs) {
			const lx = Math.log10(Math.max(x, EPS));
			let b = Math.floor(((lx - lo) / span) * HISTO_BUCKETS);
			if (b >= HISTO_BUCKETS) b = HISTO_BUCKETS - 1;
			if (b < 0) b = 0;
			counts[b]++;
		}
		const peak = Math.max(...counts, 1);
		// Right-edge (ms) of bucket i, for axis ticks.
		const edge = (i: number) => 10 ** (lo + (span * (i + 1)) / HISTO_BUCKETS);
		return { min, max, counts, peak, edge };
	});
	// SVG geometry for the histogram.
	const HW = 640;
	const HH = 160;
	const HPAD = 24;

	async function copyFailures() {
		const data = failures.map((t) => ({ label: t.label, mm: t.mm, error: t.error }));
		try {
			await navigator.clipboard.writeText(JSON.stringify(data, null, 2));
			copyMsg = `copied ${data.length} failures`;
		} catch {
			copyMsg = 'clipboard blocked — see console';
			console.log(JSON.stringify(data, null, 2));
		}
		setTimeout(() => (copyMsg = ''), 2500);
	}
	const isRunning = $derived(phase === 'loading' || phase === 'graph' || phase === 'importing');

	/** Navigate to a session view, carrying the chosen worker count. */
	async function attach(file: string) {
		const params = new URLSearchParams({ file });
		if (workers > 0) params.set('workers', String(workers));
		await goto(`?${params.toString()}`);
	}

	// --- landing: either attach by hash (no download) or import by URL -------
	async function importDb() {
		importing = true;
		landingMsg = '';
		const hash = hashInput.trim();

		// Hash given → probe the server; attach if it exists (no download).
		if (hash) {
			landingMsg = `probing ${shortHash(hash)} on the server …`;
			try {
				const info = await client.mmDbInfo(hash, user);
				if (info) {
					await attach(info.file);
					return;
				}
				landingMsg =
					'not loaded on the server — provide a URL (clear the hash) to import it.';
			} catch (e) {
				landingMsg = `probe failed: ${e instanceof Error ? e.message : String(e)}`;
			}
			importing = false;
			return;
		}

		// No hash → download the `.mm` client-side, then POST it into a session.
		if (!url.trim()) {
			landingMsg = 'provide a .mm URL or a server hash.';
			importing = false;
			return;
		}
		landingMsg = `downloading ${url} …`;
		let source: string;
		try {
			const res = await fetch(url);
			if (!res.ok) throw new Error(`${res.status} ${res.statusText}`);
			source = await res.text();
		} catch (e) {
			landingMsg = `download failed: ${e instanceof Error ? e.message : String(e)}`;
			importing = false;
			return;
		}
		landingMsg = `downloaded ${(source.length / 1_000_000).toFixed(1)} MB — parsing on server …`;
		try {
			const { file } = await client.createMmDb(source, { user, from: url });
			await attach(file);
		} catch (e) {
			landingMsg = `import failed: ${e instanceof Error ? e.message : String(e)}`;
			importing = false;
		}
	}

	// --- DB view: load the cached graph, start proving, follow live status --
	function teardown() {
		if (ws) {
			ws.close();
			ws = null;
		}
	}

	function resetView() {
		teardown();
		total = 0;
		done = 0;
		currentLabel = '';
		elapsedMs = 0;
		nOk = 0;
		theorems = [];
		labelIndex = new Map();
		selected = null;
		detail = null;
		detailCache.clear();
		dbInfo = null;
	}

	/** Copy the full session hash to the clipboard (header copy button). */
	async function copyHash() {
		if (!fileHash) return;
		try {
			await navigator.clipboard.writeText(fileHash);
			headerCopyMsg = 'copied';
		} catch {
			headerCopyMsg = 'clipboard blocked';
		}
		setTimeout(() => (headerCopyMsg = ''), 2000);
	}

	async function loadDb(hash: string) {
		resetView();
		loadedHash = hash;
		phase = 'loading';
		statusMsg = 'loading graph …';

		// Fetch lightweight info first so origin/total show before the graph.
		try {
			dbInfo = await client.mmDbInfo(hash, user);
		} catch {
			dbInfo = null;
		}

		let graph;
		try {
			graph = await client.mmGraph(hash, user);
		} catch {
			phase = 'notLoaded';
			statusMsg = 'database not loaded on the server — import it';
			return;
		}

		total = graph.total;
		const rows: ImportedTheorem[] = [];
		labelIndex = new Map();
		for (const item of graph.theorems) {
			labelIndex.set(item.label, rows.length);
			rows.push({
				label: item.label,
				status: 'pending',
				mm: item.mm,
				deps: item.deps,
				ok: false,
			});
		}
		theorems = rows;
		phase = 'graph';
		statusMsg = `loaded ${total} theorems — starting import …`;

		// Connect the status WS first so we don't miss early frames, then start.
		connectStatus(hash);
		try {
			const wq = new URLSearchParams(window.location.search).get('workers');
			await client.startMmProve(hash, user, wq != null ? Number(wq) : undefined);
			phase = 'importing';
			statusMsg = `proving ${total} theorems …`;
		} catch (e) {
			phase = 'error';
			statusMsg = `prove failed: ${e instanceof Error ? e.message : String(e)}`;
		}
	}

	function connectStatus(hash: string) {
		ws = client.connectMmStatus(hash, user);
		ws.onmessage = (ev) => {
			let msg: MmStatusMessage;
			try {
				msg = JSON.parse(ev.data as string) as MmStatusMessage;
			} catch {
				return;
			}
			handle(msg);
		};
		ws.onerror = () => {
			// Non-fatal: the import keeps running server-side; the page just
			// won't get live updates. Leave phase as-is.
		};
	}

	// The live status model:
	//   - `snapshot` (on connect) seeds statuses for already-proved theorems so a
	//     late joiner / reconnect is current;
	//   - `proving`/`proved` flip individual rows in place via the `labelIndex`
	//     map (O(1) lookup), mutating the element so Svelte 5's deep `$state`
	//     reactivity re-renders only that row — no array rebuild;
	//   - `done` finalizes the run.
	function handle(msg: MmStatusMessage) {
		switch (msg.type) {
			case 'snapshot': {
				let n = 0;
				for (const r of msg.results) {
					const i = labelIndex.get(r.label);
					if (i != null) {
						theorems[i].status = r.ok ? 'proved' : 'error';
						theorems[i].ok = r.ok;
						n++;
					}
				}
				done = Math.max(done, n);
				break;
			}
			case 'proving': {
				const i = labelIndex.get(msg.label);
				if (i != null) {
					theorems[i].status = 'proving';
					currentLabel = msg.label;
				}
				break;
			}
			case 'proved': {
				done = msg.done;
				const i = labelIndex.get(msg.label);
				if (i != null) {
					const t = theorems[i];
					t.status = msg.ok ? 'proved' : 'error';
					t.ok = msg.ok;
					t.hyps = msg.hyps;
					t.genuine = msg.genuine;
					t.holPreview = msg.holPreview;
					t.error = msg.error;
					t.importMs = msg.importMs;
				}
				// If this row is the selected one, refresh its detail in place.
				if (selected && selected.label === msg.label) {
					detailCache.delete(msg.label);
					void selectTheorem(theorems[i]);
				}
				break;
			}
			case 'done':
				phase = 'done';
				nOk = msg.ok;
				elapsedMs = msg.elapsedMs;
				statusMsg = `done — ${msg.ok}/${msg.total} imported in ${(msg.elapsedMs / 1000).toFixed(1)}s`;
				teardown();
				break;
			case 'error':
				phase = 'error';
				statusMsg = `error: ${msg.message}`;
				teardown();
				break;
		}
	}

	// --- detail: lazily fetch full per-theorem data (proof + ess + HOL) -----
	async function selectTheorem(t: ImportedTheorem) {
		selected = t;
		const cached = detailCache.get(t.label);
		if (cached) {
			detail = cached;
			return;
		}
		detail = null;
		if (!fileHash) return;
		try {
			const d = await client.mmTheorem(fileHash, t.label, user);
			detailCache.set(t.label, d);
			// Only apply if the selection hasn't changed while we awaited.
			if (selected && selected.label === t.label) detail = d;
		} catch {
			// leave detail null; the row's accumulated fields still render
		}
	}

	// Refresh the "loaded on server" list whenever we're on the landing view.
	$effect(() => {
		if (!browser) return;
		if (!fileHash) void refreshServerDbs();
	});

	// React to the `?file` param: (re)load when it changes; tear down on leave.
	$effect(() => {
		if (!browser) return;
		const h = fileHash;
		if (!h) {
			resetView();
			loadedHash = null;
			importing = false;
			return;
		}
		if (h !== loadedHash) {
			void loadDb(h);
		}
		return () => teardown();
	});
</script>

<main>
	<header>
		<h1>Metamath → HOL import <span class="tag">temporary demo</span></h1>
		<p class="lede">
			Downloads a Metamath <code>.mm</code> database, then imports it into the native HOL kernel in
			two phases: first the <strong>whole declaration graph</strong> streams in (every theorem
			shown immediately as <span class="leg pending">pending</span>), then a parallel prove phase
			flips each to <span class="leg proving">proving</span> →
			<span class="leg proved">proved</span> / <span class="leg error">error</span> as a worker
			constructs its <code>⊢ Derivable_L ⌜S⌝</code>. Click any theorem to inspect its Metamath
			statement and HOL representation. This is a throwaway UX experiment — and the seed of a
			general <em>task view</em> of a covalence proof DB (a theorem is a task with a status; later:
			a <code>translating</code> state and per-logic columns over the same graph).
		</p>
	</header>

	{#if !fileHash || phase === 'notLoaded'}
		<section class="controls">
			{#if phase === 'notLoaded'}
				<p class="warn">
					This database isn’t loaded on the server (it may have restarted). Re-import it below.
				</p>
			{/if}

			<div class="row">
				<label class="field-lbl" title="fill the URL from a known preset">
					source
					<select class="preset-select" bind:value={preset} onchange={onPreset} disabled={importing}>
						<option value="hol">hol.mm</option>
						<option value="set">set.mm</option>
						<option value="custom">custom…</option>
					</select>
				</label>
				<input
					type="text"
					bind:value={url}
					oninput={() => (preset = 'custom')}
					placeholder=".mm URL (downloaded client-side, then parsed on the server)"
					spellcheck="false"
					disabled={importing}
				/>
			</div>

			<div class="row">
				<label class="field-lbl grow" title="attach to an already-loaded session by content hash (no download)">
					hash
					<input
						type="text"
						class="hash-input"
						bind:value={hashInput}
						placeholder="attach by content hash (no download) — leave empty to use the URL"
						spellcheck="false"
						disabled={importing}
					/>
				</label>
				<label class="workers" title="prove worker threads (0 = auto)">
					workers
					<input type="number" min="0" max="64" bind:value={workers} disabled={importing} />
				</label>
				<button class="primary" onclick={importDb} disabled={importing}>
					{importing ? 'Working…' : hashInput.trim() ? 'Attach' : 'Download & Import'}
				</button>
			</div>

			{#if landingMsg}<p class="msg landing-msg">{landingMsg}</p>{/if}
			{#if !hashInput.trim() && url === PRESETS.set.url}
				<p class="warn">
					set.mm is ~48 MB and ~47k theorems — the upload + parse is heavy and the import runs for
					minutes. hol.mm is the snappy default. (If it’s already loaded, reattach below — no
					re-download.)
				</p>
			{/if}

			<div class="server-dbs">
				<div class="sd-head">
					<span class="flabel">Loaded on server</span>
					<button class="copy" onclick={refreshServerDbs} disabled={importing}>refresh</button>
				</div>
				{#if serverDbs.length === 0}
					<p class="note">No databases loaded on the server yet.</p>
				{:else}
					<div class="sd-list">
						{#each serverDbs as db (db.file + (db.user ?? ''))}
							<button class="sd-item" onclick={() => attach(db.file)} disabled={importing}>
								<span class="sd-origin">{db.origin ?? '(no origin)'}</span>
								<span class="sd-meta">{db.total} thms · {db.proved} proved</span>
								<span class="sd-hash" title={db.file}>{shortHash(db.file)}</span>
							</button>
						{/each}
					</div>
				{/if}
			</div>
		</section>
	{/if}

	{#if fileHash && phase !== 'notLoaded'}
	<section class="dbhead">
		<button class="back" onclick={() => goto('?')} title="back to source selection">← sources</button>
		<div class="dbmeta">
			<span class="origin" title="provenance (where this .mm came from)">
				{dbInfo?.origin ?? '(no origin)'}
			</span>
			<span class="dim">· {dbInfo?.total ?? total} theorems</span>
		</div>
		<div class="hashbox">
			<code class="fullhash" title={fileHash}>{fileHash}</code>
			<button class="copy" onclick={copyHash}>copy</button>
			{#if headerCopyMsg}<span class="dim">{headerCopyMsg}</span>{/if}
		</div>
	</section>

	<section class="status">
		<div class="bar">
			<progress value={done} max={Math.max(total, 1)}></progress>
			<span class="counts">{done} / {total || '?'}</span>
		</div>
		<div class="statline">
			<span class="phase phase-{phase}">{phase}</span>
			<span class="msg">{statusMsg}</span>
			{#if currentLabel && isRunning}<span class="cur">{currentLabel}</span>{/if}
		</div>
		{#if theorems.length > 0}
			<div class="summary">
				{#if nPending > 0}<span class="pending">{nPending} pending</span>{/if}
				{#if nProving > 0}<span class="proving">{nProving} active</span>{/if}
				<span class="ok">{nProved} ✓</span>
				{#if nErr > 0}<span class="err">{nErr} ✗</span>{/if}
				{#if phase === 'done'}<span>{(elapsedMs / 1000).toFixed(1)}s wall</span>{/if}
				{#if avgMs > 0}<span class="dim">avg {avgMs.toFixed(1)} ms/thm</span>{/if}
				{#if slowest}<span class="dim">slowest {slowest.label} {(slowest.importMs ?? 0).toFixed(0)} ms</span>{/if}
				<span class="spacer"></span>
				<label class="filter">
					<input type="checkbox" bind:checked={failuresOnly} />
					failures only
				</label>
				{#if timed.length > 0}
					<button class="copy" class:on={showHisto} onclick={() => (showHisto = !showHisto)}>
						{showHisto ? 'hide plot' : 'plot'}
					</button>
				{/if}
				{#if nErr > 0}
					<button class="copy" onclick={copyFailures}>Copy failures (JSON)</button>
				{/if}
				{#if copyMsg}<span class="dim">{copyMsg}</span>{/if}
			</div>
			{#if stats}
				<div class="quantiles">
					<span class="qlabel">import ms</span>
					<span class="q">min <b>{stats.min.toFixed(1)}</b></span>
					<span class="q">q1 <b>{stats.q1.toFixed(1)}</b></span>
					<span class="q">median <b>{stats.median.toFixed(1)}</b></span>
					<span class="q">q3 <b>{stats.q3.toFixed(1)}</b></span>
					<span class="q">max <b>{stats.max.toFixed(1)}</b></span>
				</div>
			{/if}
			{#if showHisto && histo}
				<div class="histo">
					<svg viewBox="0 0 {HW} {HH}" preserveAspectRatio="none" role="img"
						aria-label="histogram of import times">
						{#each histo.counts as c, i (i)}
							{@const bw = (HW - 2 * HPAD) / HISTO_BUCKETS}
							{@const h = (c / histo.peak) * (HH - 2 * HPAD)}
							<rect
								x={HPAD + i * bw}
								y={HH - HPAD - h}
								width={Math.max(bw - 1, 1)}
								height={h}
								fill="var(--accent)"
							/>
						{/each}
						<line x1={HPAD} y1={HH - HPAD} x2={HW - HPAD} y2={HH - HPAD} stroke="var(--border)" />
					</svg>
					<div class="haxis">
						<span>{histo.min.toFixed(2)} ms</span>
						<span class="dim">log scale · {HISTO_BUCKETS} buckets · peak {histo.peak}</span>
						<span>{histo.max.toFixed(1)} ms</span>
					</div>
				</div>
			{/if}
		{/if}
	</section>

	<section class="panes">
		<div class="list">
			<div class="searchbar">
				<input
					type="text"
					class="search"
					bind:value={search}
					placeholder="filter by label or statement…"
					spellcheck="false"
				/>
				<select class="sort" bind:value={sortBy} title="sort order">
					<option value="order">order</option>
					<option value="slow">slowest</option>
					<option value="fast">fastest</option>
					<option value="deps">most deps</option>
					<option value="label">label</option>
				</select>
				{#if search || failuresOnly}
					<span class="shown">{filtered.length} / {theorems.length}</span>
				{/if}
			</div>
			<div class="rows" bind:this={rowsEl} onscroll={onRowsScroll}>
				<div class="vspacer" style="height:{totalH}px">
					<div class="vwin" style="transform:translateY({offsetY}px)">
						{#each vRows as t (t.label)}
							<button
								class="item"
								class:fail={t.status === 'error'}
								class:sel={selected?.label === t.label}
								onclick={() => selectTheorem(t)}
							>
								<span class="dot status-{t.status}"></span>
								<span class="lbl">{t.label}</span>
								<span class="mini">{t.mm}</span>
								{#if t.importMs != null}<span class="time">{t.importMs.toFixed(0)} ms</span>{/if}
							</button>
						{/each}
					</div>
				</div>
				{#if theorems.length === 0}
					<div class="empty">{phase === 'loading' ? 'Loading graph…' : 'No theorems.'}</div>
				{:else if filtered.length === 0}
					<div class="empty">No theorems match the current filter.</div>
				{/if}
			</div>
		</div>

		<div class="detail">
			{#if selected}
				<h2>{selected.label}</h2>
				<div class="field">
					<div class="flabel">Metamath statement</div>
					<pre class="mm">{selected.mm}</pre>
					{#if detail && detail.ess.length > 0}
						<div class="flabel sub">essential hypotheses</div>
						{#each detail.ess as e (e)}
							<pre class="mm hyp">{e}</pre>
						{/each}
					{/if}
				</div>
				<div class="field">
					<div class="flabel">HOL term</div>
					{#if selected.status === 'proved'}
						<div class="kv">
							<span>hypotheses</span><span>{selected.hyps}</span>
						</div>
						<div class="kv">
							<span>genuine (oracle-free)</span>
							<span class:yes={selected.genuine} class:no={!selected.genuine}>
								{selected.genuine ? 'yes' : 'no'}
							</span>
						</div>
						{#if selected.importMs != null}
							<div class="kv">
								<span>import time</span><span>{selected.importMs.toFixed(1)} ms</span>
							</div>
						{/if}
						{#if selected.deps != null}
							<div class="kv">
								<span>direct deps</span><span>{selected.deps.length}</span>
							</div>
						{/if}
						<p class="note">
							The actual kernel conclusion (<code>∀d. Closed ⟹ d ⌜S⌝</code> — derivability
							over the encoded syntax), truncated.
						</p>
						<pre class="hol">{selected.holPreview}…</pre>
					{:else if selected.status === 'error'}
						<div class="kv">
							<span>status</span><span class="no">import failed</span>
						</div>
						<pre class="hol err">{selected.error}</pre>
					{:else}
						<div class="kv">
							<span>status</span>
							<span class={selected.status === 'proving' ? 'proving' : 'dim'}>
								{selected.status === 'proving' ? 'proving…' : 'pending'}
							</span>
						</div>
						<p class="note">
							Not yet proved — the prove phase {selected.status === 'proving'
								? 'is deriving this theorem'
								: "hasn't reached this theorem yet"}.
						</p>
					{/if}
				</div>
				<div class="field">
					<div class="flabel">Dependencies</div>
					{#if selected.deps && selected.deps.length > 0}
						{@const axioms = selected.deps.filter((d) => d.kind === 'axiom')}
						{@const defs = selected.deps.filter((d) => d.kind === 'def')}
						{@const thms = selected.deps.filter((d) => d.kind === 'thm')}
						{#if axioms.length > 0}
							<div class="depgroup">
								<span class="dkind axiom">Axioms ({axioms.length})</span>
								<span class="chips">
									{#each axioms as d (d.label)}<span class="chip axiom">{d.label}</span>{/each}
								</span>
							</div>
						{/if}
						{#if defs.length > 0}
							<div class="depgroup">
								<span class="dkind def">Definitions ({defs.length})</span>
								<span class="chips">
									{#each defs as d (d.label)}<span class="chip def">{d.label}</span>{/each}
								</span>
							</div>
						{/if}
						{#if thms.length > 0}
							<div class="depgroup">
								<span class="dkind thm">Theorems ({thms.length})</span>
								<span class="chips">
									{#each thms as d (d.label)}<span class="chip thm">{d.label}</span>{/each}
								</span>
							</div>
						{/if}
					{:else}
						<p class="note">none (axiom instance / hypotheses only)</p>
					{/if}
				</div>
				{#if axiomBase}
					<div class="field">
						<div class="flabel">
							Transitive axiom base
							<span class="dim">· {axiomBase.thms} theorems reached</span>
						</div>
						<div class="depgroup">
							<span class="dkind axiom">Axioms ({axiomBase.axioms.length})</span>
							<span class="chips">
								{#each axiomBase.axioms as a (a)}<span class="chip axiom">{a}</span>{/each}
							</span>
						</div>
						<div class="depgroup">
							<span class="dkind def">Definitions ({axiomBase.defs.length})</span>
							<span class="chips">
								{#each axiomBase.defs as a (a)}<span class="chip def">{a}</span>{/each}
							</span>
						</div>
						{#if axiomBase.missing > 0}
							<p class="note">
								{axiomBase.missing} dependency theorem(s) not yet imported — closure is partial
								(re-check once the import finishes).
							</p>
						{/if}
					</div>
				{/if}
				<div class="field">
					<div class="flabel">Metamath proof</div>
					{#if detail == null}
						<p class="note">loading proof…</p>
					{:else if detail.proof}
						<pre class="mm proof">{detail.proof}</pre>
					{:else}
						<p class="note">no proof code (axiom).</p>
					{/if}
				</div>
			{:else}
				<div class="empty">Select a theorem to see its Metamath + HOL details.</div>
			{/if}
		</div>
	</section>
	{/if}
</main>

<style>
	/* Dark theme — uses the site palette from app.css
	   (--bg/--fg/--surface/--border/--accent/--muted). */
	main {
		--ok: #4ade80;
		--bad: #f87171;
		--warnc: #fbbf24;
		--code-bg: #0e0e10;
		max-width: 1100px;
		margin: 0 auto;
		padding: 1.5rem;
		font-family: var(--font-mono);
		color: var(--fg);
	}
	h1 {
		font-size: 1.4rem;
		margin: 0 0 0.4rem;
		color: var(--fg);
	}
	.tag {
		font-size: 0.65rem;
		text-transform: uppercase;
		letter-spacing: 0.08em;
		background: rgba(251, 191, 36, 0.16);
		color: var(--warnc);
		padding: 0.15rem 0.45rem;
		border-radius: 4px;
		vertical-align: middle;
	}
	.lede {
		color: var(--muted);
		font-size: 0.9rem;
		line-height: 1.5;
		max-width: 70ch;
	}
	.leg {
		font-weight: 600;
	}
	.leg.pending {
		color: var(--muted);
	}
	.leg.proving {
		color: var(--warnc);
	}
	.leg.proved {
		color: var(--ok);
	}
	.leg.error {
		color: var(--bad);
	}
	code {
		font-family: var(--font-mono);
		background: var(--surface);
		border: 1px solid var(--border);
		padding: 0.05rem 0.25rem;
		border-radius: 3px;
		font-size: 0.85em;
		color: var(--fg);
	}

	.controls {
		margin: 1.25rem 0;
	}
	.row {
		display: flex;
		gap: 0.5rem;
		align-items: center;
		margin-bottom: 0.6rem;
	}
	.field-lbl {
		display: flex;
		align-items: center;
		gap: 0.35rem;
		font-size: 0.72rem;
		color: var(--muted);
		white-space: nowrap;
	}
	.field-lbl.grow {
		flex: 1;
	}
	.field-lbl.grow .hash-input {
		flex: 1;
	}
	.preset-select {
		padding: 0.45rem 0.5rem;
		border: 1px solid var(--border);
		border-radius: 6px;
		background: var(--surface);
		color: var(--fg);
		font-family: var(--font-mono);
		font-size: 0.8rem;
		cursor: pointer;
	}
	.hash-input {
		font-size: 0.78rem !important;
	}

	/* "Loaded on server" reattach list. */
	.server-dbs {
		margin-top: 1rem;
		border-top: 1px solid var(--border);
		padding-top: 0.8rem;
	}
	.sd-head {
		display: flex;
		align-items: center;
		justify-content: space-between;
		margin-bottom: 0.4rem;
	}
	.sd-list {
		display: flex;
		flex-direction: column;
		gap: 0.3rem;
	}
	.sd-item {
		display: flex;
		align-items: center;
		gap: 0.8rem;
		text-align: left;
		padding: 0.45rem 0.6rem;
		border: 1px solid var(--border);
		border-radius: 6px;
		background: var(--surface);
		color: var(--fg);
		cursor: pointer;
		font-family: var(--font-mono);
		font-size: 0.8rem;
	}
	.sd-item:hover {
		border-color: var(--accent);
		background: rgba(124, 111, 247, 0.1);
	}
	.sd-origin {
		flex: 1;
		overflow: hidden;
		text-overflow: ellipsis;
		white-space: nowrap;
	}
	.sd-meta {
		color: var(--muted);
		font-size: 0.74rem;
		white-space: nowrap;
	}
	.sd-hash {
		color: var(--muted);
		font-size: 0.72rem;
		white-space: nowrap;
	}

	/* DB-view header: back button · origin/total · prominent copyable hash. */
	.dbhead {
		display: flex;
		align-items: center;
		gap: 0.8rem;
		flex-wrap: wrap;
		margin: 1rem 0 0.25rem;
	}
	.dbhead .back {
		padding: 0.3rem 0.6rem;
		border: 1px solid var(--border);
		border-radius: 6px;
		background: var(--surface);
		color: var(--fg);
		cursor: pointer;
		font-size: 0.78rem;
		white-space: nowrap;
	}
	.dbhead .back:hover {
		border-color: var(--accent);
	}
	.dbmeta {
		display: flex;
		align-items: baseline;
		gap: 0.4rem;
		font-size: 0.85rem;
		min-width: 0;
	}
	.dbmeta .origin {
		color: var(--fg);
		overflow: hidden;
		text-overflow: ellipsis;
		white-space: nowrap;
		max-width: 40ch;
	}
	.dbmeta .dim {
		color: var(--muted);
		white-space: nowrap;
	}
	.hashbox {
		display: flex;
		align-items: center;
		gap: 0.5rem;
		margin-left: auto;
		min-width: 0;
	}
	.fullhash {
		font-family: var(--font-mono);
		font-size: 0.72rem;
		background: var(--code-bg);
		border: 1px solid var(--border);
		border-radius: 5px;
		padding: 0.25rem 0.5rem;
		color: var(--accent);
		overflow: hidden;
		text-overflow: ellipsis;
		white-space: nowrap;
		max-width: 52ch;
	}
	.hashbox .copy {
		padding: 0.25rem 0.55rem;
		border: 1px solid var(--border);
		border-radius: 5px;
		background: var(--surface);
		color: var(--fg);
		cursor: pointer;
		font-size: 0.74rem;
	}
	.hashbox .copy:hover {
		border-color: var(--accent);
	}
	.hashbox .dim {
		color: var(--muted);
		font-size: 0.74rem;
	}
	.workers {
		display: flex;
		align-items: center;
		gap: 0.35rem;
		font-size: 0.78rem;
		color: var(--muted);
		white-space: nowrap;
	}
	.workers input[type='number'] {
		width: 3.5rem;
		padding: 0.4rem 0.4rem;
		border: 1px solid var(--border);
		border-radius: 6px;
		background: var(--code-bg);
		color: var(--fg);
		font-family: var(--font-mono);
		font-size: 0.8rem;
	}
	.landing-msg {
		margin: 0.5rem 0 0;
		font-size: 0.82rem;
	}
	button.primary:disabled {
		opacity: 0.6;
		cursor: default;
	}
	input[type='text'] {
		flex: 1;
		padding: 0.5rem 0.6rem;
		border: 1px solid var(--border);
		border-radius: 6px;
		background: var(--code-bg);
		color: var(--fg);
		font-family: var(--font-mono);
		font-size: 0.85rem;
	}
	button.primary {
		padding: 0.5rem 1rem;
		border: none;
		border-radius: 6px;
		background: var(--accent);
		color: #fff;
		font-weight: 600;
		cursor: pointer;
		white-space: nowrap;
	}
	.warn {
		margin: 0.5rem 0 0;
		font-size: 0.8rem;
		color: var(--warnc);
		background: rgba(251, 191, 36, 0.1);
		border: 1px solid rgba(251, 191, 36, 0.25);
		padding: 0.4rem 0.6rem;
		border-radius: 5px;
	}

	.status {
		margin: 1rem 0;
	}
	.bar {
		display: flex;
		align-items: center;
		gap: 0.6rem;
	}
	progress {
		flex: 1;
		height: 12px;
		accent-color: var(--accent);
	}
	.counts {
		font-variant-numeric: tabular-nums;
		font-size: 0.85rem;
		color: var(--muted);
		min-width: 6em;
		text-align: right;
	}
	.statline {
		display: flex;
		gap: 0.6rem;
		align-items: center;
		margin-top: 0.4rem;
		font-size: 0.82rem;
	}
	.phase {
		text-transform: uppercase;
		font-size: 0.62rem;
		letter-spacing: 0.06em;
		padding: 0.12rem 0.4rem;
		border-radius: 4px;
		background: var(--surface);
		border: 1px solid var(--border);
		color: var(--muted);
	}
	.phase-importing,
	.phase-loading,
	.phase-graph {
		background: rgba(124, 111, 247, 0.16);
		border-color: transparent;
		color: var(--accent);
	}
	.phase-done {
		background: rgba(74, 222, 128, 0.16);
		border-color: transparent;
		color: var(--ok);
	}
	.phase-error {
		background: rgba(248, 113, 113, 0.16);
		border-color: transparent;
		color: var(--bad);
	}
	.msg {
		color: var(--muted);
	}
	.cur {
		font-family: var(--font-mono);
		color: var(--accent);
		margin-left: auto;
	}
	.summary {
		display: flex;
		gap: 0.8rem;
		align-items: center;
		flex-wrap: wrap;
		margin-top: 0.4rem;
		font-size: 0.8rem;
	}
	.summary .ok {
		color: var(--ok);
	}
	.summary .pending {
		color: var(--muted);
	}
	.summary .proving {
		color: var(--warnc);
		font-weight: 600;
	}
	.summary .err {
		color: var(--bad);
		font-weight: 600;
	}
	.summary .dim {
		color: var(--muted);
	}
	.summary .spacer {
		flex: 1;
	}
	.summary .filter {
		display: flex;
		align-items: center;
		gap: 0.3rem;
		color: var(--muted);
		cursor: pointer;
	}
	.summary .copy {
		padding: 0.25rem 0.55rem;
		border: 1px solid var(--border);
		border-radius: 5px;
		background: var(--surface);
		color: var(--fg);
		cursor: pointer;
		font-size: 0.76rem;
	}
	.summary .copy:hover {
		border-color: var(--accent);
	}

	.panes {
		display: grid;
		grid-template-columns: minmax(280px, 1fr) minmax(320px, 1.2fr);
		gap: 1rem;
		margin-top: 0.5rem;
	}
	.list {
		display: flex;
		flex-direction: column;
		border: 1px solid var(--border);
		border-radius: 8px;
		max-height: 60vh;
		background: var(--surface);
	}
	.searchbar {
		display: flex;
		align-items: center;
		gap: 0.5rem;
		padding: 0.4rem 0.5rem;
		border-bottom: 1px solid var(--border);
		flex: none;
	}
	input.search {
		flex: 1;
		padding: 0.35rem 0.5rem;
		border: 1px solid var(--border);
		border-radius: 5px;
		background: var(--code-bg);
		color: var(--fg);
		font-family: var(--font-mono);
		font-size: 0.78rem;
	}
	.searchbar .sort {
		padding: 0.35rem 0.4rem;
		border: 1px solid var(--border);
		border-radius: 5px;
		background: var(--surface);
		color: var(--fg);
		font-family: var(--font-mono);
		font-size: 0.74rem;
		cursor: pointer;
	}
	.searchbar .shown {
		font-size: 0.72rem;
		color: var(--muted);
		font-variant-numeric: tabular-nums;
		white-space: nowrap;
	}
	.rows {
		flex: 1;
		overflow-y: auto;
		scrollbar-width: thin;
		scrollbar-color: var(--border) transparent;
	}
	.rows::-webkit-scrollbar {
		width: 8px;
	}
	.rows::-webkit-scrollbar-track {
		background: transparent;
	}
	.rows::-webkit-scrollbar-thumb {
		background: var(--border);
		border-radius: 4px;
	}
	.vspacer {
		position: relative;
		width: 100%;
	}
	.vwin {
		position: absolute;
		top: 0;
		left: 0;
		right: 0;
	}
	.quantiles {
		display: flex;
		gap: 0.8rem;
		align-items: center;
		flex-wrap: wrap;
		margin-top: 0.4rem;
		font-size: 0.78rem;
		color: var(--muted);
	}
	.quantiles .qlabel {
		text-transform: uppercase;
		font-size: 0.62rem;
		letter-spacing: 0.06em;
	}
	.quantiles .q b {
		color: var(--fg);
		font-variant-numeric: tabular-nums;
		font-weight: 600;
	}
	.histo {
		margin-top: 0.6rem;
		border: 1px solid var(--border);
		border-radius: 6px;
		padding: 0.5rem;
		background: var(--code-bg);
	}
	.histo svg {
		display: block;
		width: 100%;
		height: 160px;
	}
	.haxis {
		display: flex;
		justify-content: space-between;
		margin-top: 0.3rem;
		font-size: 0.7rem;
		color: var(--fg);
		font-variant-numeric: tabular-nums;
	}
	.haxis .dim {
		color: var(--muted);
	}
	.copy.on {
		border-color: var(--accent);
		color: var(--accent);
	}
	.item {
		display: flex;
		align-items: center;
		gap: 0.5rem;
		width: 100%;
		height: 26px; /* must match ROW_H */
		box-sizing: border-box;
		text-align: left;
		padding: 0 0.6rem;
		border: none;
		border-bottom: 1px solid var(--border);
		background: transparent;
		color: var(--fg);
		cursor: pointer;
		font-size: 0.8rem;
	}
	.item:hover {
		background: rgba(124, 111, 247, 0.1);
	}
	.item.sel {
		background: rgba(124, 111, 247, 0.2);
	}
	.item .dot {
		width: 7px;
		height: 7px;
		border-radius: 50%;
		background: var(--muted);
		flex: none;
	}
	/* 4-state task status: grey pending · orange proving · green proved · red error. */
	.item .dot.status-pending {
		background: var(--muted);
		opacity: 0.5;
	}
	.item .dot.status-proving {
		background: var(--warnc);
		box-shadow: 0 0 0 2px rgba(251, 191, 36, 0.25);
		animation: pulse 1s ease-in-out infinite;
	}
	.item .dot.status-proved {
		background: var(--ok);
	}
	.item .dot.status-error {
		background: var(--bad);
	}
	@keyframes pulse {
		0%,
		100% {
			opacity: 1;
		}
		50% {
			opacity: 0.4;
		}
	}
	.item .lbl {
		font-family: var(--font-mono);
		font-weight: 600;
		flex: none;
		color: var(--fg);
	}
	.item .mini {
		flex: 1;
		color: var(--muted);
		font-family: var(--font-mono);
		white-space: nowrap;
		overflow: hidden;
		text-overflow: ellipsis;
	}
	.item .time {
		flex: none;
		color: var(--muted);
		font-variant-numeric: tabular-nums;
		font-size: 0.72rem;
		opacity: 0.75;
	}
	.item.fail .lbl {
		color: var(--bad);
	}

	.detail {
		border: 1px solid var(--border);
		border-radius: 8px;
		padding: 1rem;
		max-height: 60vh;
		overflow-y: auto;
		background: var(--surface);
	}
	.detail h2 {
		margin: 0 0 0.8rem;
		font-family: var(--font-mono);
		font-size: 1.05rem;
		color: var(--fg);
	}
	.field {
		margin-bottom: 1rem;
	}
	.flabel {
		font-size: 0.68rem;
		text-transform: uppercase;
		letter-spacing: 0.06em;
		color: var(--muted);
		margin-bottom: 0.3rem;
	}
	.flabel.sub {
		margin-top: 0.7rem;
	}
	pre.mm,
	pre.hol {
		background: var(--code-bg);
		border: 1px solid var(--border);
		border-radius: 5px;
		padding: 0.5rem 0.6rem;
		font-family: var(--font-mono);
		font-size: 0.78rem;
		white-space: pre-wrap;
		word-break: break-word;
		margin: 0 0 0.3rem;
		color: var(--fg);
	}
	pre.hyp {
		background: var(--surface);
	}
	pre.hol.err {
		color: var(--bad);
		background: rgba(248, 113, 113, 0.08);
		border-color: rgba(248, 113, 113, 0.3);
	}
	.kv {
		display: flex;
		justify-content: space-between;
		font-size: 0.82rem;
		padding: 0.2rem 0;
		border-bottom: 1px dashed var(--border);
	}
	.kv .yes {
		color: var(--ok);
		font-weight: 600;
	}
	.kv .no {
		color: var(--bad);
		font-weight: 600;
	}
	.kv .proving {
		color: var(--warnc);
		font-weight: 600;
	}
	.kv .dim {
		color: var(--muted);
	}
	.note {
		font-size: 0.74rem;
		color: var(--muted);
		margin: 0.2rem 0 0.4rem;
		line-height: 1.4;
	}
	.empty {
		padding: 1.5rem;
		color: var(--muted);
		font-size: 0.85rem;
		text-align: center;
	}
	.depgroup {
		margin-bottom: 0.5rem;
	}
	.dkind {
		display: block;
		font-size: 0.68rem;
		text-transform: uppercase;
		letter-spacing: 0.06em;
		margin-bottom: 0.25rem;
		color: var(--muted);
	}
	.dkind.axiom {
		color: var(--warnc);
	}
	.dkind.def {
		color: var(--accent);
	}
	.dkind.thm {
		color: var(--ok);
	}
	.chips {
		display: flex;
		flex-wrap: wrap;
		gap: 0.3rem;
	}
	.chip {
		font-family: var(--font-mono);
		font-size: 0.72rem;
		padding: 0.1rem 0.4rem;
		border-radius: 4px;
		border: 1px solid var(--border);
		background: var(--code-bg);
		color: var(--fg);
	}
	.chip.axiom {
		border-color: rgba(251, 191, 36, 0.4);
	}
	.chip.def {
		border-color: rgba(124, 111, 247, 0.4);
	}
	.chip.thm {
		border-color: rgba(74, 222, 128, 0.4);
	}
	pre.proof {
		max-height: 14rem;
		overflow-y: auto;
	}
</style>
