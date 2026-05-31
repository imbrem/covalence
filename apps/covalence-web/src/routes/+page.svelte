<script lang="ts">
	import { client } from '$lib/api';
	import type { ObjectInfoResponse } from 'covalence-client';
	import {
		init, destroy, send, setOutputEl, formatDuration, doPoll,
		getLines, getInput, setInput, getHistory, getHistoryIndex, setHistoryIndex,
		isWsConnected, isHealthy, getLastHealth, getConnectedDuration,
	} from '$lib/repl.svelte';

	// --- Syntax highlighting ---
	const KEYWORDS = new Set([
		// WAT component-model structural keywords
		'module', 'component', 'import', 'export', 'func', 'param', 'result',
		'type', 'instance', 'core', 'canon', 'lift', 'lower',
		'memory', 'table', 'global', 'elem', 'data', 'start', 'local', 'alias',
		// REPL commands
		'store', 'help', 'parse-module', 'parse-component', 'decide',
	]);

	function escHtml(s: string): string {
		return s.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;').replace(/"/g, '&quot;').replace(/'/g, '&#39;');
	}

	/** Heuristic: is this output structured code (S-expression or hashes) vs. prose (help, status)? */
	function isCodeOutput(text: string): boolean {
		const trimmed = text.trim();
		if (!trimmed) return false;
		const lines = trimmed.split('\n');
		// All lines are 64-char hex hashes
		if (lines.every(l => /^[a-f0-9]{64}$/.test(l.trim()))) return true;
		// Looks like an S-expression block: starts with ( and last line ends with )
		const first = lines[0].trimStart();
		const last = lines[lines.length - 1].trimEnd();
		if (first.startsWith('(') && last.endsWith(')')) {
			let depth = 0, inStr = false, escaped = false;
			for (let i = 0; i < first.length; i++) {
				const ch = first[i];
				if (escaped) { escaped = false; continue; }
				if (inStr) {
					if (ch === '\\') escaped = true;
					else if (ch === '"') inStr = false;
					continue;
				}
				if (ch === '"') inStr = true;
				else if (ch === '(') depth++;
				else if (ch === ')') {
					depth--;
					if (depth === 0 && i < first.length - 1) {
						const rest = first.slice(i + 1).trim();
						if (rest && !rest.startsWith('(') && !rest.startsWith(';')) return false;
					}
				}
			}
			return true;
		}
		return false;
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
				if (/^[a-f0-9]{64}$/.test(atom)) {
					out += `<a class="hl-hash" href="/view/${atom}" data-hash="${atom}">${escHtml(atom)}</a>`;
				} else {
					let cls: string;
					if (KEYWORDS.has(atom)) cls = 'hl-keyword';
					else if (/^-?[0-9]/.test(atom) || /^0x[0-9a-fA-F]+$/.test(atom)) cls = 'hl-number';
					else if (atom.startsWith('$')) cls = 'hl-var';
					else cls = 'hl-atom';
					out += `<span class="${cls}">${escHtml(atom)}</span>`;
				}
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
		return depth === 0;
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
				while (i < before.length && before[i] === ' ') { col++; i++; }
				const headStart = i;
				while (i < before.length && !/[\s()";|]/.test(before[i])) { col++; i++; }
				const head = before.slice(headStart, i);

				let argCol: number;
				if (!head || SPECIAL_FORMS.has(head)) {
					argCol = parenCol + 2;
				} else {
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

	// --- Use shared REPL state ---
	let lines = $derived(getLines());
	let input = $derived(getInput());
	let wsConnected = $derived(isWsConnected());
	let healthy = $derived(isHealthy());
	let lastHealth = $derived(getLastHealth());
	let connectedDuration = $derived(getConnectedDuration());

	let highlightedInput = $derived(highlight(input));

	let outputEl: HTMLElement;
	let inputEl: HTMLTextAreaElement;

	function onKeydown(e: KeyboardEvent) {
		if (e.key === 'Enter' && !e.shiftKey) {
			if (input.trim() === '' || parensBalanced(input)) {
				e.preventDefault();
				send();
			} else {
				e.preventDefault();
				const pos = inputEl.selectionStart;
				const indent = calcIndent(input, pos);
				const ins = '\n' + ' '.repeat(indent);
				const newVal = input.slice(0, pos) + ins + input.slice(pos);
				setInput(newVal);
				requestAnimationFrame(() => {
					const newPos = pos + ins.length;
					inputEl.selectionStart = newPos;
					inputEl.selectionEnd = newPos;
				});
			}
		} else if (e.key === 'Tab') {
			e.preventDefault();
			const pos = inputEl.selectionStart;
			setInput(input.slice(0, pos) + '  ' + input.slice(pos));
			requestAnimationFrame(() => {
				inputEl.selectionStart = pos + 2;
				inputEl.selectionEnd = pos + 2;
			});
		} else if (e.key === 'ArrowUp' && !input.includes('\n')) {
			e.preventDefault();
			const history = getHistory();
			let historyIndex = getHistoryIndex();
			if (history.length === 0) return;
			if (historyIndex === -1) historyIndex = history.length;
			if (historyIndex > 0) {
				historyIndex--;
				setHistoryIndex(historyIndex);
				setInput(history[historyIndex]);
			}
		} else if (e.key === 'ArrowDown' && !input.includes('\n')) {
			e.preventDefault();
			const history = getHistory();
			let historyIndex = getHistoryIndex();
			if (historyIndex === -1) return;
			if (historyIndex < history.length - 1) {
				historyIndex++;
				setHistoryIndex(historyIndex);
				setInput(history[historyIndex]);
			} else {
				setHistoryIndex(-1);
				setInput('');
			}
		}
	}

	// --- Tooltip state ---
	let tooltipText = $state('');
	let tooltipX = $state(0);
	let tooltipY = $state(0);
	let tooltipVisible = $state(false);
	const infoCache = new Map<string, ObjectInfoResponse>();

	function onOutputMouseOver(e: MouseEvent) {
		const target = e.target as HTMLElement;
		if (target.tagName === 'A' && target.classList.contains('hl-hash')) {
			const hash = target.dataset.hash;
			if (!hash) return;
			showTooltip(hash, target);
		}
	}

	function onOutputMouseOut(e: MouseEvent) {
		const target = e.target as HTMLElement;
		if (target.tagName === 'A' && target.classList.contains('hl-hash')) {
			tooltipVisible = false;
		}
	}

	async function showTooltip(hash: string, el: HTMLElement) {
		const rect = el.getBoundingClientRect();
		tooltipX = rect.left;
		tooltipY = rect.top - 4;

		let info = infoCache.get(hash);
		if (!info) {
			tooltipText = 'loading\u2026';
			tooltipVisible = true;
			const fetched = await client.objectInfo(hash);
			if (fetched) {
				infoCache.set(hash, fetched);
				info = fetched;
			} else {
				tooltipText = 'not found';
				return;
			}
		}
		tooltipText = `${info.kind} \u00b7 ${formatSize(info.size)}`;
		tooltipVisible = true;
	}

	function formatSize(bytes: number): string {
		if (bytes < 1024) return `${bytes} B`;
		if (bytes < 1024 * 1024) return `${(bytes / 1024).toFixed(1)} KB`;
		return `${(bytes / (1024 * 1024)).toFixed(1)} MB`;
	}

	function onInputChange(e: Event) {
		setInput((e.target as HTMLTextAreaElement).value);
	}

	$effect(() => {
		init();
		return () => destroy();
	});

	$effect(() => {
		if (outputEl) setOutputEl(outputEl);
	});
</script>

<div class="app">
	<div class="repl">
		<!-- svelte-ignore a11y_no_static_element_interactions -->
		<div
			class="repl-output"
			bind:this={outputEl}
			onmouseover={onOutputMouseOver}
			onmouseout={onOutputMouseOut}
		>
			{#each lines as line}
				{#if line.kind === 'input'}
					<div class="line input"><span class="prompt">cov&gt;</span> {@html highlight(line.text)}</div>
				{:else if line.kind === 'error'}
					<div class="line error">{line.text}</div>
				{:else}
					<div class="line output">{@html isCodeOutput(line.text) ? highlight(line.text) : escHtml(line.text)}</div>
				{/if}
			{/each}
		</div>
		<div class="repl-input">
			<span class="prompt">cov&gt;</span>
			<div class="input-wrapper">
				<pre class="input-highlight" aria-hidden="true">{@html highlightedInput}&nbsp;</pre>
				<!-- svelte-ignore a11y_autofocus -->
				<textarea
					value={input}
					oninput={onInputChange}
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

	{#if tooltipVisible}
		<div class="hash-tooltip" style="left:{tooltipX}px;top:{tooltipY}px">
			{tooltipText}
		</div>
	{/if}

	<footer class="status-bar">
		<button
			class="health-dot"
			class:healthy
			class:unhealthy={!healthy}
			onclick={() => doPoll()}
			title={healthy ? 'API connected' : 'API unreachable'}
			aria-label={healthy ? 'API connected' : 'API unreachable'}
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
	.input-highlight :global(.hl-hash) {
		color: #f5c07c;
		opacity: 0.8;
		text-decoration: none;
		cursor: pointer;
	}

	.line :global(.hl-hash:hover) {
		text-decoration: underline;
		opacity: 1;
	}

	.line :global(.hl-comment),
	.input-highlight :global(.hl-comment) { color: var(--muted); font-style: italic; }

	.line :global(.hl-atom),
	.input-highlight :global(.hl-atom) { color: var(--fg); }

	/* --- Tooltip --- */
	.hash-tooltip {
		position: fixed;
		transform: translateY(-100%);
		background: var(--surface);
		border: 1px solid var(--border);
		border-radius: 4px;
		padding: 0.25rem 0.5rem;
		font-size: 0.75rem;
		color: var(--fg);
		pointer-events: none;
		z-index: 100;
		white-space: nowrap;
	}

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
