import { error } from '@sveltejs/kit';

type SourceFile = {
	path: string;
	language: string;
	lines: number;
	content: string;
	href: string;
};

export async function load({ fetch, url }) {
	const path = url.searchParams.get('path');
	if (!path) error(400, 'Missing source path');
	const base = import.meta.env.VITE_COVALENCE_MAP_DATA_BASE?.replace(/\/$/, '') ?? '';
	const response = await fetch(`${base}/covalence-sources.json`);
	if (!response.ok) error(response.status, 'Could not load covalence-sources.json');
	const transport = (await response.json()) as {
		provider: string;
		files: Array<Omit<SourceFile, 'content'>>;
	};
	const metadata = transport.files.find((candidate) => candidate.path === path);
	if (!metadata) error(404, `Unknown plaintext source: ${path}`);
	const sourceResponse = await fetch(`${base}${metadata.href}`);
	if (!sourceResponse.ok) error(sourceResponse.status, `Could not load plaintext source: ${path}`);
	const file = (await sourceResponse.json()) as SourceFile;
	return { file, provider: transport.provider };
}
