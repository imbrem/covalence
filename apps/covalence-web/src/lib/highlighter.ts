import type { HighlightFn, HighlightResult, LanguageOption } from 'covalence-ui';

/** Language registry: [moduleImport, displayName]. */
const LANGUAGES: [string, () => Promise<{ default: unknown }>, string][] = [
	['javascript', () => import('highlight.js/lib/languages/javascript'), 'JavaScript'],
	['typescript', () => import('highlight.js/lib/languages/typescript'), 'TypeScript'],
	['python', () => import('highlight.js/lib/languages/python'), 'Python'],
	['rust', () => import('highlight.js/lib/languages/rust'), 'Rust'],
	['c', () => import('highlight.js/lib/languages/c'), 'C'],
	['cpp', () => import('highlight.js/lib/languages/cpp'), 'C++'],
	['json', () => import('highlight.js/lib/languages/json'), 'JSON'],
	['xml', () => import('highlight.js/lib/languages/xml'), 'XML / HTML'],
	['css', () => import('highlight.js/lib/languages/css'), 'CSS'],
	['bash', () => import('highlight.js/lib/languages/bash'), 'Bash'],
	['sql', () => import('highlight.js/lib/languages/sql'), 'SQL'],
	['wasm', () => import('highlight.js/lib/languages/wasm'), 'WebAssembly'],
	['markdown', () => import('highlight.js/lib/languages/markdown'), 'Markdown'],
	['yaml', () => import('highlight.js/lib/languages/yaml'), 'YAML'],
	['toml', () => import('highlight.js/lib/languages/ini'), 'TOML / INI'],
	['lisp', () => import('highlight.js/lib/languages/lisp'), 'Lisp'],
	['scheme', () => import('highlight.js/lib/languages/scheme'), 'Scheme'],
];

let cached: HighlightFn | null = null;

/** Lazily initialize highlight.js and return a synchronous highlight function. */
export async function createHighlighter(): Promise<HighlightFn> {
	if (cached) return cached;

	const { default: hljs } = await import('highlight.js/lib/core');

	// Register all languages in parallel
	const mods = await Promise.all(LANGUAGES.map(([, loader]) => loader()));
	for (let i = 0; i < LANGUAGES.length; i++) {
		const [id] = LANGUAGES[i];
		hljs.registerLanguage(id, mods[i].default as any);
	}

	const fn: HighlightFn = (code: string, language: string | null): HighlightResult => {
		if (language === 'plain') {
			return { html: escapeHtml(code), detectedLanguage: null };
		}

		try {
			if (language) {
				const result = hljs.highlight(code, { language, ignoreIllegals: true });
				return { html: result.value, detectedLanguage: language };
			}
			// Auto-detect
			const result = hljs.highlightAuto(code);
			return {
				html: result.value,
				detectedLanguage: result.language ?? null,
			};
		} catch {
			return { html: escapeHtml(code), detectedLanguage: null };
		}
	};

	cached = fn;
	return fn;
}

/** Options for the language picker dropdown. */
export function getLanguageOptions(): LanguageOption[] {
	return LANGUAGES.map(([id, , name]) => ({ id, name }));
}

/** Simple heuristic: check shebang line and common patterns. */
export function suggestLanguage(data: Uint8Array): string | null {
	// Decode first 512 bytes for heuristics
	const head = new TextDecoder('utf-8', { fatal: false }).decode(data.subarray(0, 512));

	// Shebang
	const shebang = head.match(/^#!\s*\/\S*\b(\w+)/);
	if (shebang) {
		const interp = shebang[1];
		const map: Record<string, string> = {
			python: 'python', python3: 'python',
			node: 'javascript', bash: 'bash', sh: 'bash', zsh: 'bash',
		};
		if (map[interp]) return map[interp];
	}

	// Content patterns
	if (/^\s*\{[\s\n]/.test(head) && /"[^"]*"\s*:/.test(head)) return 'json';
	if (/^\s*<\?xml/.test(head)) return 'xml';
	if (/^\s*<!DOCTYPE|^\s*<html/i.test(head)) return 'xml';
	if (/^\s*\(module\b/.test(head)) return 'wasm';
	if (/^\s*\((?:declare-|define-|assert|set-logic|check-sat)/.test(head)) return 'lisp';
	if (/^---\n/.test(head)) return 'yaml';
	if (/^\s*fn\s+\w+|^\s*use\s+\w+::|^\s*(?:pub\s+)?(?:struct|enum|impl|mod|trait)\s/.test(head)) return 'rust';
	if (/^\s*(?:def|class|import|from)\s/.test(head)) return 'python';
	if (/^\s*(?:function|const|let|var|import|export)\s/.test(head)) return 'javascript';
	if (/^\s*(?:interface|type|namespace)\s/.test(head)) return 'typescript';
	if (/^\s*(?:#include|int\s+main)/.test(head)) return 'c';
	if (/^\s*SELECT|^\s*CREATE|^\s*INSERT/i.test(head)) return 'sql';

	return null;
}

function escapeHtml(s: string): string {
	return s
		.replace(/&/g, '&amp;')
		.replace(/</g, '&lt;')
		.replace(/>/g, '&gt;')
		.replace(/"/g, '&quot;');
}
