<script lang="ts">
	import type { TreeEntry } from 'covalence-client';

	interface Props {
		hash: string;
		entries: TreeEntry[];
	}

	let { hash, entries }: Props = $props();

	// Sort: dirs first, then files, alphabetical within each group
	let sorted = $derived(
		[...entries].sort((a, b) => {
			const aDir = a.mode === 'dir' ? 0 : 1;
			const bDir = b.mode === 'dir' ? 0 : 1;
			if (aDir !== bDir) return aDir - bDir;
			return a.name.localeCompare(b.name);
		})
	);

	function modeLabel(mode: string): string {
		switch (mode) {
			case 'dir': return 'dir';
			case 'executable': return 'exe';
			case 'symlink': return 'sym';
			case 'submodule': return 'sub';
			default: return '';
		}
	}

	function truncHash(h: string): string {
		return h.slice(0, 12);
	}
</script>

<div class="tree-viewer">
	<table>
		<tbody>
			{#each sorted as entry}
				<tr>
					<td class="icon">{entry.mode === 'dir' ? '📁' : '📄'}</td>
					<td class="name">
						<a href="/view/{entry.hash}">{entry.name}</a>
					</td>
					<td class="mode">
						{#if modeLabel(entry.mode)}
							<span class="mode-badge">{modeLabel(entry.mode)}</span>
						{/if}
					</td>
					<td class="hash">
						<a href="/view/{entry.hash}" class="hash-link">{truncHash(entry.hash)}</a>
					</td>
				</tr>
			{/each}
		</tbody>
	</table>
</div>

<style>
	.tree-viewer {
		width: 100%;
	}

	table {
		width: 100%;
		border-collapse: collapse;
	}

	tr:hover {
		background: var(--surface, #1a1a1e);
	}

	td {
		padding: 0.35rem 0.5rem;
		white-space: nowrap;
		vertical-align: middle;
	}

	.icon {
		width: 1.5rem;
		text-align: center;
	}

	.name {
		font-weight: 500;
	}

	.name a {
		color: var(--fg, #e0e0e0);
		text-decoration: none;
	}

	.name a:hover {
		color: var(--accent, #7c6ff7);
		text-decoration: underline;
	}

	.mode {
		width: 3rem;
	}

	.mode-badge {
		font-size: 0.7rem;
		color: var(--muted, #888);
		border: 1px solid var(--border, #2a2a2e);
		border-radius: 3px;
		padding: 0 4px;
	}

	.hash {
		text-align: right;
	}

	.hash-link {
		font-size: 0.85rem;
		color: var(--muted, #888);
		text-decoration: none;
		font-family: var(--font-mono, monospace);
	}

	.hash-link:hover {
		color: var(--accent, #7c6ff7);
	}
</style>
