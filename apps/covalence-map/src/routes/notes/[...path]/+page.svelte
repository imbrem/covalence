<script lang="ts">
	import MarkdownIt from 'markdown-it';
	let { data } = $props();

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
		if (path.startsWith('notes/') && path.endsWith('.md') && !line) {
			return `/notes/${path.slice('notes/'.length)}`;
		}
		return `/source?path=${encodeURIComponent(path)}${line ? `#L${line}` : ''}`;
	}

	const markdown = new MarkdownIt({ html: false, linkify: true, typographer: true });
	const defaultLinkOpen =
		markdown.renderer.rules.link_open ??
		((tokens, index, options, _environment, self) =>
			self.renderToken(tokens, index, options));
	markdown.renderer.rules.link_open = (tokens, index, options, environment, self) => {
		const hrefIndex = tokens[index].attrIndex('href');
		if (hrefIndex >= 0) {
			const href = tokens[index].attrs![hrefIndex][1];
			if (!/^[a-z]+:/i.test(href) && !href.startsWith('#')) {
				const [target, fragment] = href.split('#');
				tokens[index].attrs![hrefIndex][1] = sourceHref(
					target,
					fragment?.match(/^L?(\d+)$/)?.[1],
				);
			}
		}
		return defaultLinkOpen(tokens, index, options, environment, self);
	};
	const defaultCode =
		markdown.renderer.rules.code_inline ??
		((tokens, index) => `<code>${markdown.utils.escapeHtml(tokens[index].content)}</code>`);
	markdown.renderer.rules.code_inline = (tokens, index, options, environment, self) => {
		const match = tokens[index].content.match(
			/^((?:crates|scripts|docs|notes|apps|packages|extensions)\/[^\s:]+)(?::(\d+))?$/,
		);
		if (!match) return defaultCode(tokens, index, options, environment, self);
		const label = markdown.utils.escapeHtml(tokens[index].content);
		return `<a href="${sourceHref(match[1], match[2])}"><code>${label}</code></a>`;
	};
	let rendered = $derived(markdown.render(data.content));
	let isHistory = $derived(data.path.startsWith('notes/history/'));
</script>

<svelte:head><title>{data.title} · Covalence map</title></svelte:head>

<main>
	<a href={isHistory ? '/?view=history' : '/?view=notes'}>← {isHistory ? 'history' : 'notes'}</a>
	<p class="path">{data.id ? `${data.id} · ` : ''}{data.path}</p>
	<article>
		{@html rendered}
	</article>
</main>

<style>
	main {
		max-width: 68rem;
		margin: 4.5rem auto 2rem;
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
	article :global(h1), article :global(h2), article :global(h3) {
		margin: 1.7em 0 0.65em;
		line-height: 1.25;
	}
	article :global(h1:first-child) { margin-top: 0; }
	article :global(p), article :global(li) { line-height: 1.7; }
	article :global(a) { color: var(--accent); }
	article :global(pre) {
		overflow: auto;
		padding: 0.9rem;
		border: 1px solid var(--border);
		border-radius: 5px;
		background: var(--bg);
	}
	article :global(code) {
		font-family: var(--font-mono);
	}
	article :global(blockquote) {
		margin-left: 0;
		padding-left: 1rem;
		border-left: 3px solid var(--border);
		color: var(--muted);
	}
</style>
