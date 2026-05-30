import type { Component } from 'svelte';

export interface ViewerDescriptor {
	/** Object kinds this viewer handles. */
	kinds: string[];
	/** Display name. */
	label: string;
	/** Available sub-modes (e.g. ["text", "hex"] for blobs). */
	modes?: string[];
	/** Auto-select mode given raw data. Returns mode name. */
	autoMode?: (data: Uint8Array) => string;
	/** The Svelte component to render. */
	component: Component<any>;
}

const viewers = new Map<string, ViewerDescriptor>();

export function registerViewer(desc: ViewerDescriptor): void {
	for (const kind of desc.kinds) {
		viewers.set(kind, desc);
	}
}

export function getViewer(kind: string): ViewerDescriptor | undefined {
	return viewers.get(kind);
}
