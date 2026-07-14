<script lang="ts">
	// LISP REPL — LIVE. `covalence-lisp` (crates/lang/lisp) compiled to WASM in
	// `covalence-web-kernel`. A PERSISTENT session: `defun`s accumulate, so you
	// can define recursive functions and build the metacircular interpreter up
	// over several cells. Every printed value is read OFF a genuine kernel
	// theorem (`⊢ program = value`); hover a cell to see it (via `#show`).
	import { onMount } from 'svelte';
	import Repl from '$lib/Repl.svelte';
	import examples from '$lib/lispExamples.json';

	let wasm = $state<any>(null);
	let ready = $state(false);
	let loadError = $state('');

	onMount(async () => {
		try {
			const mod = await import('$lib/kernel/covalence_web_kernel.js');
			const wasmUrl = (await import('$lib/kernel/covalence_web_kernel_bg.wasm?url')).default;
			await mod.default({ module_or_path: wasmUrl });
			wasm = mod;
			ready = true;
		} catch (e) {
			loadError = String(e);
		}
	});

	const evalCell = (src: string) => {
		const r = JSON.parse(wasm.lisp_eval_cell(src));
		return { ok: !!r.ok, result: r.result ?? '', error: r.error ?? '' };
	};
	// Hover → the kernel theorem behind a value, via the `#show` directive.
	const showCell = (src: string) => {
		const r = JSON.parse(wasm.lisp_eval_cell('#show ' + src));
		return r.ok ? (r.result ?? '') : '';
	};
	const onReset = () => wasm?.lisp_reset?.();
</script>

<svelte:head><title>lisp — covalence</title></svelte:head>

<main>
	<h1>lisp</h1>
	<p class="sub">
		A small, kernel-backed Lisp (<code>covalence-lisp</code>), running live in your
		browser via WASM. <strong>Every printed value is backed by a kernel theorem</strong>
		— the REPL reduces a program to <code>⊢ program = value</code> and prints the value
		off that theorem. <strong>Hover a result</strong> to see the proof.
	</p>
	<p class="sub">
		This is a real REPL: <code>defun</code>s persist across cells. Try the numbered
		examples in order — define <code>lat?</code>, then use it; or define the
		<code>★ metacircular eval</code> and run it. User definitions ride along as
		<em>hypotheses</em> on the theorem (<code>definitions ⊢ program = value</code>),
		which is sound even for recursion that might not terminate.
	</p>

	<Repl {evalCell} {showCell} {onReset} {ready} {loadError} examples={examples as any} />

	<p class="foot">
		Little Schemer ch1 primitives (<code>car cdr cons atom? null? eq?</code>) +
		<code>cond</code>/<code>lambda</code>/<code>defun</code> recursion; the metacircular
		interpreter runs its ground <code>quote/car/cdr/cons</code> fragment. Full
		<code>metacircular.lisp</code> is in progress (see the crate's <code>SKELETONS.md</code>).
	</p>
</main>

<style>
	main {
		max-width: 60rem;
		margin: 1.5rem auto;
		padding: 0 1rem 3rem;
		font-family: var(--font-mono);
		color: var(--fg);
	}
	h1 {
		font-size: 1.4rem;
	}
	.sub {
		color: var(--muted);
		font-size: 0.85rem;
		line-height: 1.55;
		margin: 0.4rem 0 0.8rem;
	}
	.foot {
		margin-top: 1.25rem;
		font-size: 0.78rem;
		color: var(--muted);
		line-height: 1.5;
	}
	code {
		background: var(--surface);
		border: 1px solid var(--border);
		border-radius: 3px;
		padding: 0 3px;
		font-size: 0.85em;
	}
</style>
