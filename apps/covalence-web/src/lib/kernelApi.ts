// The one place the `covalence-web-kernel` WASM bundle is loaded.
//
// Every page that needs the in-browser kernel (`/haskell`, `/proofs`) and the
// kernel Web Worker (`kernel.worker.ts`, driving `/article`) goes through
// `loadKernel()`. Three near-identical copies of this dance used to live in
// those three files; they drifted, and two of them were broken (see the mount
// note in `kernelState.svelte.ts`).
//
// INVARIANT: the wasm module is instantiated AT MOST ONCE per page load. The
// bundle is ~3.7 MB and instantiation is not cheap, so the in-flight promise —
// not just the settled result — is memoized: two callers racing on mount share
// one instantiation.
//
// INVARIANT: `KernelExports` names exactly the wasm-bindgen exports we call.
// It is a hand-written structural view, not the generated `.d.ts`: the
// generated glue lives under `src/lib/kernel/`, which is gitignored build
// output, so nothing checked in may import its types. Adding a call site means
// adding it here first — that is the point.

/** Structural view of the `covalence-web-kernel` wasm-bindgen exports we use. */
export interface KernelExports {
	/** Check a `.cov` article → JSON `CheckReport`. */
	check(src: string): string;
	/** Check a `.cov` article against a named model (`nat/self`, `nat/unary`). */
	check_model(src: string, model: string): string;
	/** Haskell dialect → canonical S-expression interchange text. */
	haskell_to_sexpr(src: string): string;
	/** Haskell dialect → carved (untyped) `sexpr` kernel `Term`. */
	haskell_to_hol_term(src: string): string;
	/** Annotated Haskell dialect → well-typed HOL `Term` + its HOL type. */
	haskell_to_typed_hol(src: string): string;
	/** Theorem module + S-expr proof file → per-theorem outcomes. */
	check_haskell_proofs(module_src: string, proof_src: string): string;
	/** Evaluate one Lisp cell (value read off a `⊢ program = value` theorem). */
	lisp_eval_cell(src: string): string;
	/** Forget the persistent Lisp session. */
	lisp_reset(): void;
	/** Evaluate one Forsp cell. */
	forsp_eval_cell(src: string): string;
	/** Forget the persistent Forsp runtime. */
	forsp_reset(): void;
	/** Evaluate one Forth cell. Currently always errors — no evaluator yet. */
	forth_eval_cell(src: string): string;
}

/** Shape every `*_eval_cell` / lowering entry point returns (as JSON text). */
export type KernelResult<T> = ({ ok: true } & T) | { ok: false; error: string };

let inflight: Promise<KernelExports> | null = null;

/**
 * Load + instantiate the kernel WASM bundle. Memoized: repeated calls (and
 * concurrent calls) share one instantiation.
 *
 * Rejects if the bundle is missing — that means `bun run build:web-kernel`
 * has not been run, and callers should surface the message verbatim rather
 * than pretending the kernel is merely slow.
 */
export function loadKernel(): Promise<KernelExports> {
	if (inflight) return inflight;
	inflight = (async () => {
		const mod = await import('$lib/kernel/covalence_web_kernel.js');
		const wasmUrl = (await import('$lib/kernel/covalence_web_kernel_bg.wasm?url')).default;
		await mod.default({ module_or_path: wasmUrl });
		return mod as unknown as KernelExports;
	})();
	// A failed load must not be cached as a permanently-poisoned promise: a
	// retry (e.g. after the dev server rebuilds the bundle) should try again.
	inflight.catch(() => {
		inflight = null;
	});
	return inflight;
}

/** Parse a kernel JSON reply, turning a malformed/throwing reply into `ok:false`. */
export function parseResult<T>(json: string): KernelResult<T> {
	try {
		const r = JSON.parse(json);
		if (r && r.ok) return r as { ok: true } & T;
		return { ok: false, error: r?.error ?? 'unknown error' };
	} catch (e) {
		return { ok: false, error: String(e) };
	}
}
