<script lang="ts">
	// TEMPORARY TCB-audit page (maintainer request): renders the CI-gated
	// snapshot docs/deps/tcb-audit.json, embedded at build time. Regenerate
	// with `bun run deps` (or `bun run tcb` to print in the terminal);
	// `bun run deps:check` fails CI if this data is stale.
	import audit from '../../../../../docs/deps/tcb-audit.json';

	const configs = Object.entries(audit.configs) as [string, any][];
	const g: any = audit.globals;

	const reality = (audit.configs as any)['base+HOL'];
	const target = (audit.configs as any)['base+HOL (target)'];
	const evalCfg = (audit.configs as any)['base+HOL+eval'];
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
		<h2>Mint sites (every theorem funnels through these)</h2>
		<details>
			<summary>{configs[0]?.[1].mintSites} sites, all in the base kernel</summary>
			<pre>{configs[0]?.[1].mintSiteLocations?.join('\n')}</pre>
		</details>
	</section>
</main>

<style>
	main { max-width: 64rem; margin: 2rem auto; padding: 0 1rem;
		font-family: ui-sans-serif, system-ui, sans-serif; }
	h1 { font-size: 1.4rem; } h2 { font-size: 1.05rem; margin-top: 1.5rem; }
	.sub { color: #666; font-size: 0.9rem; }
	table { border-collapse: collapse; width: 100%; font-variant-numeric: tabular-nums; }
	th, td { text-align: right; padding: 0.35rem 0.6rem; border-bottom: 1px solid #ddd; }
	th:first-child, td.name { text-align: left; font-weight: 600; }
	tr.target { color: #667; font-style: italic; }
	td.bad { color: #b00; font-weight: 700; }
	.headline { background: #f6f6ef; padding: 0.6rem 0.8rem; border-radius: 6px; }
	pre, code { font-size: 0.8rem; } pre { overflow-x: auto; }
	details { margin-top: 0.3rem; }
</style>
