import hljs from 'highlight.js/lib/core';
import bash from 'highlight.js/lib/languages/bash';
import css from 'highlight.js/lib/languages/css';
import ini from 'highlight.js/lib/languages/ini';
import javascript from 'highlight.js/lib/languages/javascript';
import json from 'highlight.js/lib/languages/json';
import markdown from 'highlight.js/lib/languages/markdown';
import rust from 'highlight.js/lib/languages/rust';
import typescript from 'highlight.js/lib/languages/typescript';
import xml from 'highlight.js/lib/languages/xml';
import yaml from 'highlight.js/lib/languages/yaml';

for (const [name, language] of Object.entries({
	bash,
	css,
	javascript,
	json,
	markdown,
	rust,
	toml: ini,
	typescript,
	xml,
	yaml,
})) {
	hljs.registerLanguage(name, language);
}

const aliases: Record<string, string> = {
	javascript: 'javascript',
	json: 'json',
	markdown: 'markdown',
	rust: 'rust',
	shell: 'bash',
	svelte: 'xml',
	toml: 'toml',
	typescript: 'typescript',
	yaml: 'yaml',
};

function escapeHtml(source: string): string {
	return source.replaceAll('&', '&amp;').replaceAll('<', '&lt;').replaceAll('>', '&gt;');
}

export function highlightSource(source: string, language: string): string {
	const grammar = aliases[language];
	if (!grammar) return escapeHtml(source);
	try {
		return hljs.highlight(source, { language: grammar, ignoreIllegals: true }).value;
	} catch {
		return escapeHtml(source);
	}
}
