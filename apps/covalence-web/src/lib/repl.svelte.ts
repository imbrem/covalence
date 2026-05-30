import { client } from '$lib/api';
import type { HealthResponse } from 'covalence-client';

// --- REPL line type ---
export interface ReplLine {
	kind: 'input' | 'output' | 'error';
	text: string;
}

// --- Shared reactive state ---
// This module holds REPL state that survives navigation between routes.

let lines: ReplLine[] = $state([]);
let input = $state('');
let history: string[] = $state([]);
let historyIndex = $state(-1);
let ws: WebSocket | null = $state(null);
let wsReconnectDelay = 1000;
let wsConnected = $state(false);

let healthy = $state(false);
let lastHealth: HealthResponse | null = $state(null);
let connectedSince: number | null = $state(null);
let connectedDuration = $state(0);

let timer: ReturnType<typeof setTimeout> | null = null;
let tickTimer: ReturnType<typeof setInterval> | null = null;
let initialized = false;

function scrollToBottom() {
	// Caller can override; this is a no-op placeholder.
	// The page component sets the real scroll target via setOutputEl.
}

let outputEl: HTMLElement | null = null;

export function setOutputEl(el: HTMLElement | null) {
	outputEl = el;
}

function doScroll() {
	requestAnimationFrame(() => {
		if (outputEl) outputEl.scrollTop = outputEl.scrollHeight;
	});
}

function initWs() {
	const socket = client.connectRepl();
	socket.onopen = () => {
		ws = socket;
		wsConnected = true;
		wsReconnectDelay = 1000;
	};
	socket.onmessage = (e) => {
		if (typeof e.data === 'string' && e.data.length > 0) {
			const kind = e.data.startsWith('error:') || e.data.startsWith('parse error:')
				? 'error' as const
				: 'output' as const;
			lines.push({ kind, text: e.data });
			doScroll();
		}
	};
	socket.onclose = () => {
		wsConnected = false;
		ws = null;
		wsReconnectDelay = Math.min(wsReconnectDelay * 2, 30000);
		setTimeout(initWs, wsReconnectDelay);
	};
	socket.onerror = () => {
		wsConnected = false;
	};
}

export function send() {
	const cmd = input.trim();
	if (!cmd || !ws) return;
	lines.push({ kind: 'input', text: cmd });
	history.push(cmd);
	historyIndex = -1;
	ws.send(cmd);
	input = '';
	doScroll();
}

function startTick() {
	stopTick();
	tickTimer = setInterval(() => {
		if (connectedSince != null) {
			connectedDuration = Math.floor((Date.now() - connectedSince) / 1000);
		}
	}, 1000);
}

function stopTick() {
	if (tickTimer != null) {
		clearInterval(tickTimer);
		tickTimer = null;
	}
}

async function poll() {
	try {
		lastHealth = await client.health();
		if (!healthy) {
			healthy = true;
			connectedSince = Date.now();
			startTick();
		}
	} catch {
		if (healthy) {
			healthy = false;
			connectedSince = null;
			connectedDuration = 0;
			stopTick();
		}
	}
	timer = setTimeout(poll, 1000);
}

/** Initialize WebSocket + health polling. Call once from root layout or first mount. */
export function init() {
	if (initialized) return;
	initialized = true;
	initWs();
	poll();
}

/** Cleanup (call on app destroy). */
export function destroy() {
	if (timer != null) clearTimeout(timer);
	stopTick();
	if (ws) ws.close();
	initialized = false;
}

export function formatDuration(secs: number): string {
	const h = Math.floor(secs / 3600);
	const m = Math.floor((secs % 3600) / 60);
	const s = secs % 60;
	if (h > 0) return `${h}h ${m}m ${s}s`;
	if (m > 0) return `${m}m ${s}s`;
	return `${s}s`;
}

// --- Exported reactive accessors ---
// Svelte 5 module-level $state is reactive when accessed from .svelte files.

export function getLines(): ReplLine[] { return lines; }
export function getInput(): string { return input; }
export function setInput(v: string) { input = v; }
export function getHistory(): string[] { return history; }
export function getHistoryIndex(): number { return historyIndex; }
export function setHistoryIndex(v: number) { historyIndex = v; }
export function isWsConnected(): boolean { return wsConnected; }
export function isHealthy(): boolean { return healthy; }
export function getLastHealth(): HealthResponse | null { return lastHealth; }
export function getConnectedDuration(): number { return connectedDuration; }
export function doPoll() { poll(); }
