// Curated Metamath ASCII-token → Unicode map, mirroring the "structured" /
// typeset view on the Metamath Proof Explorer (which drives it from each
// database's `$t` `althtmldef` section). This is a pragmatic hand-picked subset
// covering the common set.mm / iset.mm / hol.mm tokens — not the full typeset
// table — so the demo can show readable formulas. Extend freely; unmapped
// tokens pass through unchanged.
//
// ASCII metamath reuses tokens across typecodes (e.g. `<.` is both "less-than"
// and "ordered pair open"); a flat map can't disambiguate by context, so we
// pick the most common reading. Good enough for a browse-and-skim demo.
export const MM_UNICODE: Record<string, string> = {
	// turnstile / metalogic
	'|-': '⊢',
	'|=': '⊨',
	// propositional
	'-.': '¬',
	'/\\': '∧',
	'\\/': '∨',
	'->': '→',
	'<->': '↔',
	'-/\\': '⊼',
	// quantifiers
	'A.': '∀',
	'E.': '∃',
	'E!': '∃!',
	'E*': '∃*',
	'T.': '⊤',
	'F.': '⊥',
	// greek metavariables (wff / setvar names)
	ph: '𝜑',
	ps: '𝜓',
	ch: '𝜒',
	th: '𝜃',
	ta: '𝜏',
	et: '𝜂',
	ze: '𝜁',
	si: '𝜎',
	rh: '𝜌',
	mu: '𝜇',
	la: '𝜆',
	ka: '𝜅',
	// equality / membership
	'=/=': '≠',
	'e.': '∈',
	'e/': '∉',
	// subset / set algebra
	C_: '⊆',
	'C.': '⊊',
	'i^i': '∩',
	'u.': '∪',
	'|^|': '⋂',
	'U.': '⋃',
	'(/)': '∅',
	'~P': '𝒫',
	'X.': '×',
	'\\setminus': '∖',
	// pairs / maps / functions
	'<.': '⟨',
	'>.': '⟩',
	'|->': '↦',
	'o.': '∘',
	"`'": '◡',
	'"': '“',
	// numbers / arithmetic
	RR: 'ℝ',
	CC: 'ℂ',
	NN: 'ℕ',
	ZZ: 'ℤ',
	QQ: 'ℚ',
	NN0: 'ℕ₀',
	'RR+': 'ℝ⁺',
	_V: '𝐕',
	'<_': '≤',
	'+oo': '+∞',
	'-oo': '−∞',
	'x.': '·',
	'~~>': '⇝',
};

/** Render a space-separated Metamath statement, optionally typeset to Unicode.
 * Tokens not in {@link MM_UNICODE} (labels, variables, digits, parens) pass
 * through unchanged. */
export function renderMm(s: string, unicode: boolean): string {
	if (!unicode) return s;
	return s
		.split(' ')
		.map((tok) => MM_UNICODE[tok] ?? tok)
		.join(' ');
}
