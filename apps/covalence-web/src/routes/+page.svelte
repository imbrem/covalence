<script lang="ts">
	import { fetchApi } from '$lib/api';
	import { connectRepl } from '$lib/ws';

	interface Health {
		status: string;
		version: string;
		cog_version: string;
		target: string;
		uptime_secs: number;
	}

	// --- Syntax highlighting ---
	const KEYWORDS = new Set([
		'module', 'component', 'import', 'export', 'func', 'param', 'result',
		'type', 'instance', 'core', 'canon', 'lift', 'lower',
		'memory', 'table', 'global', 'elem', 'data', 'start', 'local',
		'block', 'loop', 'if', 'else', 'end', 'br', 'br_if', 'br_table',
		'return', 'call', 'call_indirect',
		'load', 'load-url', 'load-file', 'store', 'help',
		'parse-module', 'parse-component', 'check-prop',
		'i32', 'i64', 'f32', 'f64', 'v128', 'funcref', 'externref',
	]);

	function escHtml(s: string): string {
		return s.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');
	}

	function highlight(text: string): string {
		let out = '';
		let i = 0;
		while (i < text.length) {
			const ch = text[i];
			if (ch === ';') {
				let end = text.indexOf('\n', i);
				if (end === -1) end = text.length;
				out += `<span class="hl-comment">${escHtml(text.slice(i, end))}</span>`;
				i = end;
			} else if (ch === '|') {
				let end = text.indexOf('|', i + 1);
				if (end === -1) end = text.length; else end++;
				out += `<span class="hl-atom">${escHtml(text.slice(i, end))}</span>`;
				i = end;
			} else if (ch === '"') {
				let end = i + 1;
				while (end < text.length && text[end] !== '"') {
					if (text[end] === '\\') end++;
					end++;
				}
				if (end < text.length) end++;
				out += `<span class="hl-string">${escHtml(text.slice(i, end))}</span>`;
				i = end;
			} else if (ch === '(' || ch === ')') {
				out += `<span class="hl-paren">${ch}</span>`;
				i++;
			} else if (/\s/.test(ch)) {
				out += ch;
				i++;
			} else {
				let end = i;
				while (end < text.length && !/[\s()";|]/.test(text[end])) end++;
				const atom = text.slice(i, end);
				let cls: string;
				if (KEYWORDS.has(atom)) cls = 'hl-keyword';
				else if (/^-?[0-9]/.test(atom) || /^0x[0-9a-fA-F]+$/.test(atom)) cls = 'hl-number';
				else if (atom.startsWith('$')) cls = 'hl-var';
				else if (/^[a-f0-9]{64}$/.test(atom)) cls = 'hl-hash';
				else cls = 'hl-atom';
				out += `<span class="${cls}">${escHtml(atom)}</span>`;
				i = end;
			}
		}
		return out;
	}

	// --- Paren balancing ---
	function parensBalanced(text: string): boolean {
		let depth = 0;
		let inStr = false;
		let escaped = false;
		for (const ch of text) {
			if (escaped) { escaped = false; continue; }
			if (inStr) {
				if (ch === '\\') escaped = true;
				else if (ch === '"') inStr = false;
				continue;
			}
			if (ch === '"') inStr = true;
			else if (ch === '(') depth++;
			else if (ch === ')') depth--;
		}
		return depth <= 0;
	}

	// --- LISP indentation ---
	const SPECIAL_FORMS = new Set([
		'module', 'component', 'func', 'block', 'loop', 'if', 'type',
		'import', 'export', 'instance', 'core', 'memory', 'table', 'global',
		'elem', 'data', 'canon', 'alias', 'local',
	]);

	function calcIndent(text: string, cursor: number): number {
		const before = text.slice(0, cursor);
		const stack: { col: number; argCol: number }[] = [];
		let col = 0;
		let i = 0;
		let inStr = false;
		let escaped = false;

		while (i < before.length) {
			const ch = before[i];
			if (escaped) { escaped = false; col++; i++; continue; }
			if (inStr) {
				if (ch === '\\') escaped = true;
				else if (ch === '"') inStr = false;
				if (ch === '\n') col = 0; else col++;
				i++; continue;
			}
			if (ch === '\n') { col = 0; i++; continue; }
			if (ch === '"') { inStr = true; col++; i++; continue; }
			if (ch === '(') {
				const parenCol = col;
				col++; i++;
				// Skip spaces after paren
				while (i < before.length && before[i] === ' ') { col++; i++; }
				// Read head atom
				const headStart = i;
				while (i < before.length && !/[\s()";|]/.test(before[i])) { col++; i++; }
				const head = before.slice(headStart, i);

				let argCol: number;
				if (!head || SPECIAL_FORMS.has(head)) {
					argCol = parenCol + 2;
				} else {
					// Align with first argument (column after head + space)
					argCol = (i < before.length && before[i] === ' ') ? col + 1 : col;
				}
				stack.push({ col: parenCol, argCol });
				continue;
			}
			if (ch === ')') { stack.pop(); col++; i++; continue; }
			col++; i++;
		}

		if (stack.length === 0) return 0;
		return stack[stack.length - 1].argCol;
	}

	// --- REPL state ---
	interface ReplLine {
		kind: 'input' | 'output' | 'error';
		text: string;
	}

	let lines: ReplLine[] = $state([]);
	let input = $state('');
	let history: string[] = $state([]);
	let historyIndex = $state(-1);
	let ws: WebSocket | null = $state(null);
	let wsConnected = $state(false);
	let outputEl: HTMLElement;
	let inputEl: HTMLTextAreaElement;

	let highlightedInput = $derived(highlight(input));

	function scrollToBottom() {
		requestAnimationFrame(() => {
			if (outputEl) outputEl.scrollTop = outputEl.scrollHeight;
		});
	}

	function initWs() {
		const socket = connectRepl();
		socket.onopen = () => {
			ws = socket;
			wsConnected = true;
		};
		socket.onmessage = (e) => {
			if (typeof e.data === 'string' && e.data.length > 0) {
				const kind = e.data.startsWith('error:') || e.data.startsWith('parse error:')
					? 'error' as const
					: 'output' as const;
				lines.push({ kind, text: e.data });
				scrollToBottom();
			}
		};
		socket.onclose = () => {
			wsConnected = false;
			ws = null;
			setTimeout(initWs, 2000);
		};
		socket.onerror = () => {
			wsConnected = false;
		};
	}

	function send() {
		const cmd = input.trim();
		if (!cmd || !ws) return;
		lines.push({ kind: 'input', text: cmd });
		history.push(cmd);
		historyIndex = -1;
		ws.send(cmd);
		input = '';
		scrollToBottom();
	}

	function onKeydown(e: KeyboardEvent) {
		if (e.key === 'Enter' && !e.shiftKey) {
			if (input.trim() === '' || parensBalanced(input)) {
				e.preventDefault();
				send();
			} else {
				// Insert newline with LISP indentation
				e.preventDefault();
				const pos = inputEl.selectionStart;
				const indent = calcIndent(input, pos);
				const ins = '\n' + ' '.repeat(indent);
				input = input.slice(0, pos) + ins + input.slice(pos);
				requestAnimationFrame(() => {
					const newPos = pos + ins.length;
					inputEl.selectionStart = newPos;
					inputEl.selectionEnd = newPos;
				});
			}
		} else if (e.key === 'Tab') {
			e.preventDefault();
			const pos = inputEl.selectionStart;
			input = input.slice(0, pos) + '  ' + input.slice(pos);
			requestAnimationFrame(() => {
				inputEl.selectionStart = pos + 2;
				inputEl.selectionEnd = pos + 2;
			});
		} else if (e.key === 'ArrowUp' && !input.includes('\n')) {
			e.preventDefault();
			if (history.length === 0) return;
			if (historyIndex === -1) historyIndex = history.length;
			if (historyIndex > 0) {
				historyIndex--;
				input = history[historyIndex];
			}
		} else if (e.key === 'ArrowDown' && !input.includes('\n')) {
			e.preventDefault();
			if (historyIndex === -1) return;
			if (historyIndex < history.length - 1) {
				historyIndex++;
				input = history[historyIndex];
			} else {
				historyIndex = -1;
				input = '';
			}
		}
	}

	// --- Health status ---
	const HEALTH_POLL_MS = 1000;
	let healthy = $state(false);
	let lastHealth: Health | null = $state(null);
	let connectedSince: number | null = $state(null);
	let connectedDuration = $state(0);
	let timer: ReturnType<typeof setTimeout> | null = null;
	let tickTimer: ReturnType<typeof setInterval> | null = null;

	async function poll() {
		try {
			lastHealth = await fetchApi<Health>('/api/health');
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
		timer = setTimeout(poll, HEALTH_POLL_MS);
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

	function formatDuration(secs: number): string {
		const h = Math.floor(secs / 3600);
		const m = Math.floor((secs % 3600) / 60);
		const s = secs % 60;
		if (h > 0) return `${h}h ${m}m ${s}s`;
		if (m > 0) return `${m}m ${s}s`;
		return `${s}s`;
	}

	$effect(() => {
		initWs();
		poll();
		return () => {
			if (timer != null) clearTimeout(timer);
			stopTick();
			if (ws) ws.close();
		};
	});
</script>

<div class="app">
	<div class="repl">
		<div class="repl-output" bind:this={outputEl}>
			{#each lines as line}
				{#if line.kind === 'input'}
					<div class="line input"><span class="prompt">cov&gt;</span> {@html highlight(line.text)}</div>
				{:else if line.kind === 'error'}
					<div class="line error">{line.text}</div>
				{:else}
					<div class="line output">{@html highlight(line.text)}</div>
				{/if}
			{/each}
		</div>
		<div class="repl-input">
			<span class="prompt">cov&gt;</span>
			<div class="input-wrapper">
				<pre class="input-highlight" aria-hidden="true">{@html highlightedInput}&nbsp;</pre>
				<!-- svelte-ignore a11y_autofocus -->
				<textarea
					bind:value={input}
					bind:this={inputEl}
					onkeydown={onKeydown}
					rows="1"
					placeholder={wsConnected ? '(help)' : 'connecting...'}
					disabled={!wsConnected}
					autofocus
				></textarea>
			</div>
		</div>
	</div>

	<footer class="status-bar">
		<button
			class="health-dot"
			class:healthy
			class:unhealthy={!healthy}
			onclick={() => poll()}
			title={healthy ? 'API connected' : 'API unreachable'}
		></button>
		<span class="status-text">
			{#if healthy && lastHealth}
				connected {formatDuration(connectedDuration)} &mdash; server up {formatDuration(Math.floor(lastHealth.uptime_secs))}
			{:else}
				API unreachable
			{/if}
		</span>
		{#if wsConnected}
			<span class="ws-badge">ws</span>
		{/if}
	</footer>
</div>

<style>
	.app {
		display: flex;
		flex-direction: column;
		height: 100vh;
		max-width: 900px;
		margin: 0 auto;
	}

	.repl {
		flex: 1;
		display: flex;
		flex-direction: column;
		min-height: 0;
		padding: 1rem 1.5rem 0;
	}

	.repl-output {
		flex: 1;
		overflow-y: auto;
		padding-bottom: 0.5rem;
	}

	.line {
		white-space: pre-wrap;
		word-break: break-all;
		line-height: 1.5;
	}

	.line.input {
		color: var(--fg);
	}

	.line.output {
		color: var(--muted);
	}

	.line.error {
		color: #f87171;
	}

	.prompt {
		color: var(--accent);
		user-select: none;
	}

	.repl-input {
		display: flex;
		align-items: flex-start;
		gap: 0.5rem;
		padding: 0.75rem 0;
		border-top: 1px solid var(--border);
	}

	.repl-input > .prompt {
		line-height: 1.5;
		flex-shrink: 0;
	}

	/* --- Input overlay: highlighted pre behind transparent textarea --- */
	.input-wrapper {
		position: relative;
		flex: 1;
		min-height: 1.5em;
	}

	.input-highlight {
		white-space: pre-wrap;
		word-break: break-all;
		font-family: var(--font-mono);
		font-size: 1rem;
		line-height: 1.5;
		padding: 0;
		margin: 0;
		pointer-events: none;
	}

	.input-wrapper textarea {
		position: absolute;
		top: 0;
		left: 0;
		width: 100%;
		height: 100%;
		background: transparent;
		border: none;
		outline: none;
		color: transparent;
		caret-color: var(--fg);
		font-family: var(--font-mono);
		font-size: 1rem;
		line-height: 1.5;
		padding: 0;
		margin: 0;
		resize: none;
		overflow: hidden;
		white-space: pre-wrap;
		word-break: break-all;
	}

	.input-wrapper textarea::placeholder {
		color: var(--muted);
		opacity: 0.5;
	}

	/* --- Syntax highlighting colors --- */
	.line :global(.hl-paren),
	.input-highlight :global(.hl-paren) { color: var(--muted); }

	.line :global(.hl-string),
	.input-highlight :global(.hl-string) { color: #a8e6a3; }

	.line :global(.hl-keyword),
	.input-highlight :global(.hl-keyword) { color: #7cc4f5; }

	.line :global(.hl-number),
	.input-highlight :global(.hl-number) { color: #f5c07c; }

	.line :global(.hl-var),
	.input-highlight :global(.hl-var) { color: #c9a0f5; }

	.line :global(.hl-hash),
	.input-highlight :global(.hl-hash) { color: #f5c07c; opacity: 0.8; }

	.line :global(.hl-comment),
	.input-highlight :global(.hl-comment) { color: var(--muted); font-style: italic; }

	.line :global(.hl-atom),
	.input-highlight :global(.hl-atom) { color: var(--fg); }

	/* --- Status bar --- */
	.status-bar {
		display: flex;
		align-items: center;
		gap: 0.5rem;
		padding: 0.5rem 1.5rem;
		border-top: 1px solid var(--border);
		background: var(--surface);
		flex-shrink: 0;
	}

	.health-dot {
		width: 8px;
		height: 8px;
		border-radius: 50%;
		border: none;
		cursor: pointer;
		padding: 0;
		flex-shrink: 0;
	}

	.health-dot.healthy {
		background: #4ade80;
		box-shadow: 0 0 4px #4ade8066;
	}

	.health-dot.unhealthy {
		background: #f87171;
		box-shadow: 0 0 4px #f8717166;
	}

	.status-text {
		font-size: 0.75rem;
		color: var(--muted);
	}

	.ws-badge {
		font-size: 0.65rem;
		color: var(--accent);
		border: 1px solid var(--accent);
		border-radius: 3px;
		padding: 0 4px;
		line-height: 1.4;
		margin-left: auto;
	}
</style>
