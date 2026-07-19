/// <reference lib="webworker" />
//
// Kernel Web Worker.
//
// The wasm-bindgen build of `covalence-web-kernel` runs *here*, off the main
// thread, so a heavy check (e.g. `nat/unary`, which proves four `list unit`
// axioms then replays an induction, ~10-20s on first run) never freezes the UI.
//
// Protocol (main thread → worker):
//   { type: 'check', id, src, model }
// Protocol (worker → main thread):
//   { type: 'ready' }                      — kernel inited, ready for checks
//   { type: 'error', message }             — kernel init failed
//   { type: 'result', id, json }           — a check completed; `json` is the
//                                            JSON string from `check_model`
//                                            (always set, even on error, so the
//                                            UI never hangs)

import { loadKernel, type KernelExports } from '$lib/kernelApi';

type CheckMsg = { type: 'check'; id: number; src: string; model: string };
type InMsg = CheckMsg;

// The worker shares the main thread's typed view of the wasm exports and its
// loader; it differs only in WHERE the module is instantiated, not in how.
let checkModel: KernelExports['check_model'] | null = null;

async function init() {
	try {
		const kernel = await loadKernel();
		checkModel = kernel.check_model;
		(self as DedicatedWorkerGlobalScope).postMessage({ type: 'ready' });
	} catch (e) {
		const message = e instanceof Error ? e.message : String(e);
		(self as DedicatedWorkerGlobalScope).postMessage({ type: 'error', message });
	}
}

self.addEventListener('message', (ev: MessageEvent<InMsg>) => {
	const msg = ev.data;
	if (msg.type !== 'check') return;
	const { id, src, model } = msg;
	let json: string;
	try {
		if (!checkModel) throw new Error('kernel not initialized');
		json = checkModel(src, model);
	} catch (e) {
		const message = e instanceof Error ? e.message : String(e);
		json = JSON.stringify({
			ok: false,
			theorems: [],
			diagnostics: [{ severity: 'error', message, span: null }],
		});
	}
	(self as DedicatedWorkerGlobalScope).postMessage({ type: 'result', id, json });
});

void init();
