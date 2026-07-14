<script lang="ts">
	// TEMPORARY TCB-audit page (maintainer request): renders the CI-gated
	// snapshot docs/deps/tcb-audit.json, embedded at build time. Regenerate
	// with `bun run deps` (or `bun run tcb` to print in the terminal);
	// `bun run deps:check` fails CI if this data is stale.
	import audit from '../../../../../docs/deps/tcb-audit.json';
	// The golden admitted-rule manifests: the exact rule names each language
	// mints theorems through. CI-gated via `bun run deps:check`.
	import coreManifest from '../../../../../docs/deps/core-manifest.txt?raw';
	import evalManifest from '../../../../../docs/deps/eval-manifest.txt?raw';
	import builtinsManifest from '../../../../../docs/deps/builtins-manifest.txt?raw';

	const configs = Object.entries(audit.configs) as [string, any][];
	const g: any = audit.globals;

	const reality = (audit.configs as any)['base+HOL'];
	const target = (audit.configs as any)['base+HOL (target)'];
	const evalCfg = (audit.configs as any)['base+HOL+eval'];

	function lines(s: string): string[] {
		return s
			.split('\n')
			.map((l) => l.trim())
			.filter((l) => l.length > 0);
	}
	const coreRules = lines(coreManifest);
	const evalRules = lines(evalManifest);
	const builtinRules = lines(builtinsManifest);

	// Group the flat builtins list by its `<ns>.<op>` prefix for readability.
	const builtinsByNs = builtinRules.reduce<Record<string, string[]>>((acc, r) => {
		const ns = r.includes('.') ? r.slice(0, r.indexOf('.')) : '(other)';
		(acc[ns] ??= []).push(r);
		return acc;
	}, {});
</script>

<svelte:head><title>TCB audit — covalence</title></svelte:head>

<main>
	<h1>TCB audit surface</h1>
	<p class="sub">
		Tests excluded; lower = more auditable. Snapshot from
		<code>docs/deps/tcb-audit.json</code> (embedded at build time, CI-gated via
		<code>bun run deps:check</code>; print with <code>bun run tcb</code>).
	</p>

	<table>
		<thead>
			<tr>
				<th>config</th><th>files</th><th>src-lines</th><th>unsafe</th>
				<th>mint sites</th><th>pub API</th><th>defs:: coupling</th>
			</tr>
		</thead>
		<tbody>
			{#each configs as [name, c]}
				<tr class:target={name.includes('target')}>
					<td class="name">{name}</td>
					<td>{c.files}</td>
					<td>{c.nonTestLoc}</td>
					<td class:bad={c.unsafe > 0}>{c.unsafe}</td>
					<td>{c.mintSites}</td>
					<td>{c.publicSurfaceTotal}</td>
					<td>{c.defsCoupling}</td>
				</tr>
			{/each}
		</tbody>
	</table>

	{#if reality && target}
		<p class="headline">
			In-core defs debt (dies with the literal leaves):
			<strong>{reality.nonTestLoc - target.nonTestLoc}</strong> src-lines,
			<strong>{reality.defsCoupling - target.defsCoupling}</strong> defs:: refs.
			{#if evalCfg}Eval-tier delta over minimal HOL:
				<strong>{evalCfg.nonTestLoc - reality.nonTestLoc}</strong> lines.{/if}
		</p>
	{/if}

	<section>
		<h2>Trust inventory</h2>
		<ul>
			<li><strong>Admitted rules:</strong>
				CoreLang {g.admittedRules?.coreManifest}
				· CoreEval {g.admittedRules?.evalManifest ?? '—'}
				· Builtins {g.admittedRules?.builtinsManifest}</li>
			<li><strong>Term leaves:</strong> {g.termKindVariants} TermKind
				· {g.typeKindVariants} TypeKind variants</li>
			{#each Object.entries(g.externalDeps ?? {}) as [k, v]}
				{#if v}<li><strong>External deps ({k}):</strong> {(v as any).count}
					<details><summary>list</summary><code>{(v as any).crates.join(', ')}</code></details></li>{/if}
			{/each}
		</ul>
	</section>

	<section>
		<h2>Admitted rules per language (the golden manifests)</h2>
		<p class="sub">
			Every theorem in a language is minted by one of its admitted rules.
			These are the CI-gated manifests: <code>docs/deps/*-manifest.txt</code>.
		</p>
		<div class="manifests">
			<details open>
				<summary><strong>CoreLang</strong> — {coreRules.length} rules
					(<code>core-manifest.txt</code>)</summary>
				<ul class="rule-list">
					{#each coreRules as r}<li>{r}</li>{/each}
				</ul>
			</details>
			<details>
				<summary><strong>CoreEval</strong> — {evalRules.length} rules
					(<code>eval-manifest.txt</code>)</summary>
				<ul class="rule-list">
					{#each evalRules as r}<li>{r}</li>{/each}
				</ul>
			</details>
			<details>
				<summary><strong>Builtins</strong> — {builtinRules.length} ops
					(<code>builtins-manifest.txt</code>)</summary>
				{#each Object.entries(builtinsByNs) as [ns, ops]}
					<div class="ns">
						<span class="ns-name">{ns}</span>
						<span class="ns-ops">{ops.map((o) => o.slice(ns.length + 1)).join(' · ')}</span>
					</div>
				{/each}
			</details>
		</div>
	</section>

	<section>
		<h2>Mint sites (every theorem funnels through these)</h2>
		<details>
			<summary>{configs[0]?.[1].mintSites} sites, all in the base kernel</summary>
			<pre>{configs[0]?.[1].mintSiteLocations?.join('\n')}</pre>
		</details>
	</section>
</main>

<style>
	main { max-width: 64rem; margin: 2rem auto; padding: 0 1rem;
		font-family: var(--font-mono); color: var(--fg); }
	h1 { font-size: 1.4rem; } h2 { font-size: 1.05rem; margin-top: 1.5rem; }
	.sub { color: var(--muted); font-size: 0.9rem; }
	table { border-collapse: collapse; width: 100%; font-variant-numeric: tabular-nums; }
	th, td { text-align: right; padding: 0.35rem 0.6rem; border-bottom: 1px solid var(--border); }
	th:first-child, td.name { text-align: left; font-weight: 600; }
	tr.target { color: var(--accent); font-style: italic; }
	td.bad { color: #ff6b6b; font-weight: 700; }
	.headline { background: var(--surface); border: 1px solid var(--border);
		padding: 0.6rem 0.8rem; border-radius: 6px; }
	pre, code { font-size: 0.8rem; } pre { overflow-x: auto; }
	details { margin-top: 0.3rem; }
	.manifests details { margin-bottom: 0.4rem; }
	.manifests summary { cursor: pointer; padding: 0.15rem 0; }
	.rule-list {
		display: grid;
		grid-template-columns: repeat(auto-fill, minmax(9rem, 1fr));
		gap: 0.1rem 0.75rem;
		list-style: none;
		margin: 0.4rem 0 0.4rem 1rem;
		padding: 0;
		font-size: 0.8rem;
		font-family: ui-monospace, monospace;
	}
	.ns { margin: 0.25rem 0 0.25rem 1rem; font-size: 0.8rem; line-height: 1.5; }
	.ns-name {
		display: inline-block;
		min-width: 5rem;
		font-weight: 700;
		font-family: ui-monospace, monospace;
	}
	.ns-ops { color: var(--muted); font-family: ui-monospace, monospace; }
</style>
