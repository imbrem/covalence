<script lang="ts">
	// The terminal chrome every REPL surface shares: a full-viewport column with
	// a scrolling transcript, a syntax-highlighted prompt line, and a status bar.
	//
	// The shell owns *editing* (Enter/Tab/history/indentation) and nothing else:
	// what a transcript entry looks like is the caller's business, delegated to
	// the `transcript` snippet, so a line-oriented WebSocket log (`/`) and a
	// cell-oriented request/response transcript (`/lisp`) both fit unchanged.
	//
	// Invariant: the textarea is NEVER disabled. A disabled textarea drops focus
	// mid-session (the user types into nothing); a busy REPL instead keeps focus
	// and ignores submits, which is what `busy` does.
	import type { Snippet } from 'svelte';
	import { calcIndent, escHtml, parensBalanced } from './sexpr';

	let {
		prompt,
		value,
		onValueChange,
		onSubmit,
		highlight = escHtml,
		specialForms = new Set<string>(),
		history = [],
		placeholder = '',
		busy = false,
		autofocus = true,
		transcript,
		status = null,
		outputEl = $bindable(null),
		onOutputMouseOver = null,
		onOutputMouseOut = null,
		onOutputScroll = null
	}: {
		prompt: string;
		value: string;
		onValueChange: (v: string) => void;
		onSubmit: () => void;
		highlight?: (text: string) => string;
		specialForms?: ReadonlySet<string>;
		history?: string[];
		placeholder?: string;
		busy?: boolean;
		autofocus?: boolean;
		transcript: Snippet;
		status?: Snippet | null;
		outputEl?: HTMLElement | null;
		onOutputMouseOver?: ((e: MouseEvent) => void) | null;
		onOutputMouseOut?: ((e: MouseEvent) => void) | null;
		onOutputScroll?: (() => void) | null;
	} = $props();

	let inputEl: HTMLTextAreaElement | null = null;
	// Purely ephemeral cursor into `history`; -1 means "editing a fresh line".
	let historyIndex = $state(-1);

	let highlighted = $derived(highlight(value));

	/** Replace the input and restore the caret, which a value swap would reset. */
	function setAndPlaceCaret(next: string, caret: number) {
		onValueChange(next);
		// The frame can land after an unmount (navigating away mid-edit).
		requestAnimationFrame(() => {
			if (!inputEl) return;
			inputEl.selectionStart = caret;
			inputEl.selectionEnd = caret;
		});
	}

	function onKeydown(e: KeyboardEvent) {
		if (e.key === 'Enter' && !e.shiftKey) {
			e.preventDefault();
			// A form is submittable only once its parens close; until then Enter
			// opens a new line indented to the enclosing form.
			if (value.trim() === '' || parensBalanced(value)) {
				if (busy) return;
				historyIndex = -1;
				onSubmit();
			} else if (inputEl) {
				const pos = inputEl.selectionStart;
				const ins = '\n' + ' '.repeat(calcIndent(value, pos, specialForms));
				setAndPlaceCaret(value.slice(0, pos) + ins + value.slice(pos), pos + ins.length);
			}
		} else if (e.key === 'Tab' && inputEl) {
			e.preventDefault();
			const pos = inputEl.selectionStart;
			setAndPlaceCaret(value.slice(0, pos) + '  ' + value.slice(pos), pos + 2);
		} else if (e.key === 'ArrowUp' && !value.includes('\n')) {
			// History only rides the arrows on a single-line input — inside a
			// multi-line form the arrows have to move the caret.
			e.preventDefault();
			if (history.length === 0) return;
			if (historyIndex === -1) historyIndex = history.length;
			if (historyIndex > 0) {
				historyIndex--;
				onValueChange(history[historyIndex]);
			}
		} else if (e.key === 'ArrowDown' && !value.includes('\n')) {
			e.preventDefault();
			if (historyIndex === -1) return;
			if (historyIndex < history.length - 1) {
				historyIndex++;
				onValueChange(history[historyIndex]);
			} else {
				historyIndex = -1;
				onValueChange('');
			}
		}
	}
</script>

<div class="app">
	<div class="repl">
		<!-- svelte-ignore a11y_no_static_element_interactions -->
		<!-- svelte-ignore a11y_mouse_events_have_key_events -->
		<div
			class="repl-output"
			data-testid="repl-output"
			bind:this={outputEl}
			onmouseover={onOutputMouseOver}
			onmouseout={onOutputMouseOut}
			onscroll={onOutputScroll}
		>
			{@render transcript()}
		</div>
		<div class="repl-input" class:busy>
			<span class="prompt">{prompt}</span>
			<div class="input-wrapper">
				<pre class="input-highlight" aria-hidden="true">{@html highlighted}&nbsp;</pre>
				<!-- svelte-ignore a11y_autofocus -->
				<textarea
					data-testid="repl-input"
					value={value}
					oninput={(e) => onValueChange((e.currentTarget as HTMLTextAreaElement).value)}
					bind:this={inputEl}
					onkeydown={onKeydown}
					rows="1"
					spellcheck="false"
					{placeholder}
					{autofocus}
				></textarea>
			</div>
		</div>
	</div>

	{#if status}
		<footer class="status-bar" data-testid="status-bar">{@render status()}</footer>
	{/if}
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
		/* Firefox */
		scrollbar-width: thin;
		scrollbar-color: var(--muted) transparent;
		scrollbar-gutter: stable;
	}
	/* WebKit / Chromium: thin, subtle, themed scrollbar that only shows
	   a thumb (no track chrome) and matches the REPL's monospace feel. */
	.repl-output::-webkit-scrollbar {
		width: 8px;
		height: 8px;
	}
	.repl-output::-webkit-scrollbar-track {
		background: transparent;
	}
	.repl-output::-webkit-scrollbar-thumb {
		background: color-mix(in srgb, var(--muted) 45%, transparent);
		border-radius: 4px;
		border: 2px solid transparent;
		background-clip: padding-box;
		min-height: 32px;
	}
	.repl-output:hover::-webkit-scrollbar-thumb {
		background: color-mix(in srgb, var(--muted) 70%, transparent);
		background-clip: padding-box;
	}
	.repl-output::-webkit-scrollbar-corner {
		background: transparent;
	}

	/* Transcript content is authored by the caller's snippet, so it carries the
	   CALLER's style scope — these have to be `:global`, kept contained by the
	   scoped `.repl-output` ancestor. */
	.repl-output :global(.line) {
		white-space: pre-wrap;
		word-break: break-all;
		line-height: 1.5;
	}
	.repl-output :global(.line.input) {
		color: var(--fg);
	}
	.repl-output :global(.line.output) {
		color: var(--muted);
	}
	.repl-output :global(.line.error) {
		color: #f87171;
	}
	.repl-output :global(.prompt) {
		color: var(--accent);
		user-select: none;
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

	/* Busy is a hint, not a lockout: the caret stays, the prompt dims. */
	.repl-input.busy > .prompt {
		opacity: 0.45;
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

	/* --- Syntax highlighting colors (shared by transcript + input overlay) --- */
	.repl-output :global(.hl-paren),
	.input-highlight :global(.hl-paren) {
		color: var(--muted);
	}
	.repl-output :global(.hl-string),
	.input-highlight :global(.hl-string) {
		color: #a8e6a3;
	}
	.repl-output :global(.hl-keyword),
	.input-highlight :global(.hl-keyword) {
		color: #7cc4f5;
	}
	.repl-output :global(.hl-number),
	.input-highlight :global(.hl-number) {
		color: #f5c07c;
	}
	.repl-output :global(.hl-var),
	.input-highlight :global(.hl-var) {
		color: #c9a0f5;
	}
	.repl-output :global(.hl-hash),
	.input-highlight :global(.hl-hash) {
		color: #f5c07c;
		opacity: 0.8;
		text-decoration: none;
		cursor: pointer;
	}
	.repl-output :global(.hl-hash:hover) {
		text-decoration: underline;
		opacity: 1;
	}
	.repl-output :global(.hl-comment),
	.input-highlight :global(.hl-comment) {
		color: var(--muted);
		font-style: italic;
	}
	.repl-output :global(.hl-atom),
	.input-highlight :global(.hl-atom) {
		color: var(--fg);
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
</style>
