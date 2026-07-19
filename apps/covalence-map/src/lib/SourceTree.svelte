<script lang="ts">
	type File = { path: string; language: string; lines: number };
	type Node = { name: string; path: string; files: File[]; children: Node[] };

	let { files, current = null }: { files: File[]; current?: string | null } = $props();

	function treeOf(items: File[]): Node {
		const root: Node = { name: 'covalence', path: '', files: [], children: [] };
		for (const file of items) {
			const parts = file.path.split('/');
			let node = root;
			for (const part of parts.slice(0, -1)) {
				let child = node.children.find((candidate) => candidate.name === part);
				if (!child) {
					child = {
						name: part,
						path: node.path ? `${node.path}/${part}` : part,
						files: [],
						children: [],
					};
					node.children.push(child);
				}
				node = child;
			}
			node.files.push(file);
		}
		const sort = (node: Node) => {
			node.children.sort((a, b) => a.name.localeCompare(b.name));
			node.files.sort((a, b) => a.path.localeCompare(b.path));
			node.children.forEach(sort);
		};
		sort(root);
		return root;
	}

	let root = $derived(treeOf(files));
</script>

<nav class="tree" aria-label="Repository tree">
	<Branch node={root} {current} root />
</nav>

{#snippet Branch({ node, current, root = false }: { node: Node; current: string | null; root?: boolean })}
	<details open={root || (current?.startsWith(`${node.path}/`) ?? false)}>
		<summary>{node.name}</summary>
		<div class="children">
			{#each node.children as child}
				{@render Branch({ node: child, current })}
			{/each}
			{#each node.files as file}
				<a
					class:current={file.path === current}
					href={`/source?path=${encodeURIComponent(file.path)}`}
					title={file.path}
				>{file.path.split('/').at(-1)}</a>
			{/each}
		</div>
	</details>
{/snippet}
<style>
	.tree { font: 0.76rem/1.65 var(--font-mono); }
	details { margin-left: 0.7rem; }
	.tree > :global(details) { margin-left: 0; }
	summary { color: var(--muted); cursor: pointer; user-select: none; }
	.children { border-left: 1px solid var(--border); margin-left: 0.25rem; padding-left: 0.2rem; }
	a {
		display: block;
		overflow: hidden;
		padding: 0 0.35rem 0 1rem;
		color: var(--fg);
		text-decoration: none;
		text-overflow: ellipsis;
		white-space: nowrap;
	}
	a:hover, a.current { color: var(--accent); background: color-mix(in srgb, var(--accent) 10%, transparent); }
</style>
