import { error } from '@sveltejs/kit';

export async function load({ fetch, params }) {
	const base = import.meta.env.VITE_COVALENCE_MAP_DATA_BASE?.replace(/\/$/, '') ?? '';
	const response = await fetch(`${base}/covalence-sources.json`);
	if (!response.ok) error(response.status, 'Could not load covalence-sources.json');
	const transport = (await response.json()) as {
		files: Array<{ path: string; href: string }>;
	};
	const path = `notes/${params.path}`;
	const metadata = transport.files.find((file) => file.path === path);
	if (!metadata) error(404, `Unknown note: ${params.path}`);
	const noteResponse = await fetch(`${base}${metadata.href}`);
	if (!noteResponse.ok) error(noteResponse.status, `Could not load note: ${params.path}`);
	const source = ((await noteResponse.json()) as { content: string }).content;
	const frontmatter = source.match(/^\+\+\+\r?\n([\s\S]*?)\r?\n\+\+\+\r?\n/);
	const content = frontmatter ? source.slice(frontmatter[0].length) : source;
	return {
		content,
		path,
		id: frontmatter?.[1].match(/^id\s*=\s*"([^"]+)"/m)?.[1] ?? null,
		title: content.match(/^#\s+(.+)$/m)?.[1] ?? params.path,
	};
}
