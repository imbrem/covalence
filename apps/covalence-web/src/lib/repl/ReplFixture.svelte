<script lang="ts">
	// Test fixture: `<Repl>` with a help widget, so the `#help` → clickable
	// example path can be exercised the way a page wires it (a snippet taking
	// the `run` callback can't be written inline in a `.test.ts`).
	import Repl from '../Repl.svelte';

	let {
		evalCell,
		showCell = null,
		onReset = null
	}: {
		evalCell: (src: string) => Promise<{ ok: boolean; result: string; error: string }>;
		showCell?: ((src: string) => Promise<string>) | null;
		onReset?: (() => void) | null;
	} = $props();
</script>

{#snippet help(run: (src: string) => Promise<void>)}
	<p>docs go here</p>
	<button data-testid="example-button" onclick={() => run('(car (quote (a b)))')}>car</button>
	<button data-testid="example-button" onclick={() => run('(cdr (quote (a b)))')}>cdr</button>
{/snippet}

<Repl {evalCell} {showCell} {onReset} {help} />
