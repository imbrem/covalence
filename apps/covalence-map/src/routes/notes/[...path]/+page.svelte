<script lang="ts">
	let { data } = $props();
	type Segment = { text: string; href?: string };

	function normalize(path: string): string {
		const parts: string[] = [];
		for (const part of path.split('/')) {
			if (part === '..') parts.pop();
			else if (part !== '.' && part !== '') parts.push(part);
		}
		return parts.join('/');
	}

	function sourceHref(target: string, line?: string): string {
		const clean = target.replace(/^\/home\/tekne\/projects\/covalence\//, '');
		const path = clean.startsWith('notes/') || clean.startsWith('crates/') ||
				clean.startsWith('apps/') || clean.startsWith('packages/') ||
				clean.startsWith('scripts/') || clean.startsWith('docs/') ||
				clean.startsWith('extensions/')
			? clean
			: normalize(`${data.path.slice(0, data.path.lastIndexOf('/'))}/${clean}`);
		return `/source?path=${encodeURIComponent(path)}${line ? `#L${line}` : ''}`;
	}

	function segments(line: string): Segment[] {
		const result: Segment[] = [];
		const pattern = /\[([^\]]+)\]\(([^)#]+)(?:#L?(\d+))?\)|`((?:crates|scripts|docs|notes|apps|packages|extensions)\/[^`\s:]+)(?::(\d+))?`/g;
		let offset = 0;
		for (const match of line.matchAll(pattern)) {
			if (match.index > offset) result.push({ text: line.slice(offset, match.index) });
			if (match[2] && !/^[a-z]+:/i.test(match[2])) {
				result.push({ text: match[1], href: sourceHref(match[2], match[3]) });
			} else if (match[4]) {
				result.push({ text: match[4] + (match[5] ? `:${match[5]}` : ''), href: sourceHref(match[4], match[5]) });
			} else {
				result.push({ text: match[0] });
			}
			offset = match.index + match[0].length;
		}
		result.push({ text: line.slice(offset) });
		return result;
	}
</script>

<svelte:head><title>{data.title} · Covalence map</title></svelte:head>

<main>
	<a href="/">← map</a>
	<p class="path">{data.path}</p>
	<article>
		<pre>{#each data.content.split('\n') as line}{#each segments(line) as segment}{#if segment.href}<a
							href={segment.href}>{segment.text}</a>{:else}{segment.text}{/if}{/each}
{/each}</pre>
	</article>
</main>

<style>
	main {
		max-width: 68rem;
		margin: 2rem auto;
		padding: 0 1.25rem 5rem;
	}
	a { color: var(--accent); }
	.path { color: var(--muted); font-size: 0.8rem; margin: 1.5rem 0 0.5rem; }
	article {
		padding: 1.5rem;
		border: 1px solid var(--border);
		border-radius: 6px;
		background: var(--surface);
	}
	pre {
		margin: 0;
		white-space: pre-wrap;
		overflow-wrap: anywhere;
		font: 0.9rem/1.6 var(--font-mono);
	}
</style>
