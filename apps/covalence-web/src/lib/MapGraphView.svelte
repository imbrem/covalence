<script lang="ts">
	import { onMount } from 'svelte';
	import type { Core, ElementDefinition, LayoutOptions } from 'cytoscape';

	type MapNode = {
		id: string;
		label: string;
		kind: string;
		status?: string | null;
	};

	type MapEdge = {
		id: string;
		source: string;
		target: string;
		label: string;
	};

	interface Props {
		nodes: MapNode[];
		edges: MapEdge[];
		layout?: 'breadthfirst' | 'cose';
		selectedId?: string | null;
		onselect?: (id: string) => void;
	}

	let {
		nodes,
		edges,
		layout = 'cose',
		selectedId = null,
		onselect = () => {},
	}: Props = $props();

	let container: HTMLDivElement;
	let cy: Core | undefined;
	let ready = $state(false);

	const colours: Record<string, string> = {
		task: '#8b5cf6',
		todo: '#f59e0b',
		note: '#3b82f6',
		file: '#10b981',
	};

	function elements(): ElementDefinition[] {
		return [
			...nodes.map((node) => ({
				data: {
					id: node.id,
					label: node.label,
					kind: node.kind,
					status: node.status ?? '',
				},
			})),
			...edges.map((edge) => ({
				data: {
					id: edge.id,
					source: edge.source,
					target: edge.target,
					label: edge.label,
				},
			})),
		];
	}

	function layoutOptions(): LayoutOptions {
		return layout === 'breadthfirst'
			? {
					name: 'breadthfirst',
					directed: true,
					padding: 28,
					spacingFactor: 1.25,
					animate: false,
				}
			: {
					name: 'cose',
					padding: 28,
					animate: false,
					nodeRepulsion: () => 9000,
					idealEdgeLength: () => 90,
				};
	}

	onMount(async () => {
		const { default: cytoscape } = await import('cytoscape');
		cy = cytoscape({
			container,
			style: [
				{
					selector: 'node',
					style: {
						'background-color': (ele) => colours[ele.data('kind')] ?? '#64748b',
						label: 'data(label)',
						color: '#dbeafe',
						'font-family': 'ui-monospace, monospace',
						'font-size': 9,
						'text-valign': 'bottom',
						'text-margin-y': 5,
						'text-wrap': 'ellipsis',
						'text-max-width': 130,
						width: 18,
						height: 18,
						'border-width': 2,
						'border-color': (ele) =>
							ele.data('status') === 'missing' ? '#ef4444' : '#111827',
					},
				},
				{
					selector: 'node:selected',
					style: {
						'border-color': '#f8fafc',
						'border-width': 4,
						width: 24,
						height: 24,
					},
				},
				{
					selector: 'edge',
					style: {
						width: 1.5,
						'line-color': '#475569',
						'target-arrow-color': '#475569',
						'target-arrow-shape': 'triangle',
						'curve-style': 'bezier',
						'arrow-scale': 0.75,
						label: 'data(label)',
						'font-family': 'ui-monospace, monospace',
						'font-size': 7,
						color: '#94a3b8',
						'text-rotation': 'autorotate',
						'text-background-color': '#0f172a',
						'text-background-opacity': 0.8,
						'text-background-padding': 2,
					},
				},
			],
		});
		cy.on('tap', 'node', (event) => onselect(event.target.id()));
		ready = true;
		return () => cy?.destroy();
	});

	$effect(() => {
		if (!ready || !cy) return;
		cy.elements().remove();
		cy.add(elements());
		cy.layout(layoutOptions()).run();
		cy.fit(undefined, 30);
	});

	$effect(() => {
		if (!ready || !cy) return;
		cy.elements().unselect();
		if (selectedId) cy.getElementById(selectedId).select();
	});
</script>

<div class="graph" bind:this={container} aria-label="Interactive Covalence map"></div>

<style>
	.graph {
		width: 100%;
		height: min(68vh, 48rem);
		min-height: 32rem;
		border: 1px solid var(--border);
		border-radius: 6px;
		background: #0f172a;
	}
</style>
