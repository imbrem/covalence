/** Result of highlighting a code string. */
export interface HighlightResult {
	/** HTML string with syntax highlighting spans. */
	html: string;
	/** Detected language id, or null if unknown / plain text. */
	detectedLanguage: string | null;
}

/** Synchronous highlight callback — async init happens before this is created. */
export type HighlightFn = (code: string, language: string | null) => HighlightResult;

/** Entry for a language picker dropdown. */
export interface LanguageOption {
	id: string;
	name: string;
}
