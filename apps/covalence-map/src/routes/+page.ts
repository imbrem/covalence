import { error } from '@sveltejs/kit';

export async function load({ fetch }) {
	const base = import.meta.env.VITE_COVALENCE_MAP_DATA_BASE?.replace(/\/$/, '') ?? '';
	const response = await fetch(`${base}/covalence-map.json`);
	if (!response.ok) error(response.status, `Could not load covalence-map.json`);
	return { map: await response.json() };
}
