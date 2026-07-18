import { error } from '@sveltejs/kit';

const notes = import.meta.glob('../../../../../../notes/**/*.md', {
	query: '?raw',
	import: 'default',
	eager: true,
}) as Record<string, string>;

function sourcePath(routePath: string): string {
	return `../../../../../../notes/${routePath}`;
}

export function entries() {
	return Object.keys(notes).map((key) => ({
		path: key.slice(key.indexOf('/notes/') + '/notes/'.length),
	}));
}

export function load({ params }) {
	const content = notes[sourcePath(params.path)];
	if (content === undefined) error(404, `Unknown note: ${params.path}`);
	return {
		content,
		path: `notes/${params.path}`,
		title: content.match(/^#\s+(.+)$/m)?.[1] ?? params.path,
	};
}
