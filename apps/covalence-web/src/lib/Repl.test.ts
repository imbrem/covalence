import { render, screen, fireEvent, waitFor } from '@testing-library/svelte';
import { expect, test, vi } from 'vitest';
import Repl from './Repl.svelte';
import ReplFixture from './repl/ReplFixture.svelte';
import { LISP_SPECIAL_FORMS } from './repl/sexpr';

/** Type `src` into the prompt and submit it. */
async function submit(src: string) {
	const input = screen.getByTestId('repl-input');
	await fireEvent.input(input, { target: { value: src } });
	await fireEvent.keyDown(input, { key: 'Enter' });
	return input;
}

// Regression test for the "stuck on proving…" bug: `entries.push(entry)` stores
// a Svelte-5 proxy, so mutating a captured RAW reference updates the data but
// never fires the reactive signal — the cell stayed on "proving…" forever. The
// fix mutates through the array proxy; this asserts the result actually renders.
test('a submitted cell shows its result and clears "proving…"', async () => {
	const evalCell = vi.fn(async (src: string) => ({
		ok: true,
		result: src === '(atom? (quote a))' ? 't' : 'x',
		error: ''
	}));
	render(Repl, { props: { evalCell } });

	await submit('(atom? (quote a))');

	// The result renders …
	await waitFor(() => expect(screen.getByText('t')).toBeInTheDocument());
	// … and the transient "proving…" is gone (the regression left it stuck).
	expect(screen.queryByText(/proving/)).toBeNull();
	expect(evalCell).toHaveBeenCalledWith('(atom? (quote a))');
});

test('an error result renders (not stuck on proving…)', async () => {
	const evalCell = async () => ({ ok: false, result: '', error: 'boom' });
	render(Repl, { props: { evalCell } });

	await submit('(oops)');

	await waitFor(() => expect(screen.getByText('boom')).toBeInTheDocument());
	expect(screen.queryByText(/proving/)).toBeNull();
});

test('a `#lang` mention in an error renders as a highlighted hint chip', async () => {
	const evalCell = async () => ({
		ok: false,
		result: '',
		error: 'unknown #lang `foo` (try: lisp | scheme | sector); see #lang scheme'
	});
	const { container } = render(Repl, { props: { evalCell } });

	await submit('#lang foo');

	await waitFor(() => expect(container.querySelector('.out.err')).not.toBeNull());
	const hints = [...container.querySelectorAll('.lang-hint')].map((h) => h.textContent);
	// The bare mention and the `#lang scheme` suggestion both pop as chips …
	expect(hints).toEqual(['#lang', '#lang scheme']);
	// … while the message text survives verbatim (marked up, never rewritten).
	expect(container.querySelector('.out.err')!.textContent).toContain(
		'unknown #lang `foo` (try: lisp | scheme | sector); see #lang scheme'
	);
});

// The hover-proof honesty fix: the server's `#show` returns the FULL sequent
// (`hyps ⊢ concl`), and the client renders it VERBATIM — no client-side `⊢`
// prefix, which would misstate a hypothesis-carrying theorem as `⊢ concl`.
test('the hover popover renders the server sequent verbatim (no injected turnstile)', async () => {
	const sequent = 'app = λx. λy. … ⊢ app (a b) (c) = (a b c)';
	const evalCell = async () => ({ ok: true, result: '(a b c)', error: '' });
	const showCell = vi.fn(async () => sequent);
	const { container } = render(Repl, { props: { evalCell, showCell } });

	await submit('(app (quote (a b)) (quote (c)))');
	await waitFor(() => expect(screen.getByText('(a b c)')).toBeInTheDocument());

	await fireEvent.mouseEnter(screen.getByTestId('repl-cell'));
	await waitFor(() => expect(container.querySelector('.hol')!.textContent).toBe(sequent));
	expect(showCell).toHaveBeenCalledWith('(app (quote (a b)) (quote (c)))');

	// Regression: the popover must live OUTSIDE the scrolling transcript (a
	// fixed floating layer). The old in-cell absolute popover was clipped by
	// the transcript's overflow (hidden above the first cells) and popped a
	// scrollbar.
	expect(container.querySelector('[data-testid="repl-output"] .hol')).toBeNull();

	// It vanishes when the cursor leaves the cell.
	await fireEvent.mouseLeave(screen.getByTestId('repl-cell'));
	await waitFor(() => expect(container.querySelector('.hol')).toBeNull());
});

// A cell whose `#show` fails (e.g. a defun/defthm ack — not a reducible
// expression) must NOT keep a popover: a turnstile/"fetching proof…" with no
// theorem behind it would be a false claim.
test('a failed #show removes the popover instead of claiming a proof', async () => {
	const evalCell = async () => ({ ok: true, result: 'app', error: '' });
	const showCell = async () => {
		throw new Error('defun is not an expression');
	};
	const { container } = render(Repl, { props: { evalCell, showCell } });

	await submit('(defun app (x y) y)');
	await waitFor(() => expect(screen.getByText('app')).toBeInTheDocument());

	await fireEvent.mouseEnter(screen.getByTestId('repl-cell'));
	await waitFor(() => expect(container.querySelector('.hol')).toBeNull());
	expect(screen.getByTestId('repl-cell').classList.contains('has-hol')).toBe(false);
	expect(screen.queryByText(/fetching proof/)).toBeNull();
});

// `#help` is rendered client-side as a widget — no server round-trip — and its
// example buttons run REAL cells through the transcript (no privileged path).
test('#help renders the widget inline without hitting the server', async () => {
	const evalCell = vi.fn(async () => ({ ok: true, result: 'a', error: '' }));
	render(ReplFixture, { props: { evalCell } });

	await submit('#help');

	await waitFor(() => expect(screen.getByTestId('help-widget')).toBeInTheDocument());
	expect(evalCell).not.toHaveBeenCalled();
	expect(screen.getAllByTestId('example-button')).toHaveLength(2);
});

test('an example button inside #help runs its cell through the transcript', async () => {
	const evalCell = vi.fn(async () => ({ ok: true, result: 'a', error: '' }));
	render(ReplFixture, { props: { evalCell } });

	await submit('#help');
	await waitFor(() => expect(screen.getByTestId('help-widget')).toBeInTheDocument());

	await fireEvent.click(screen.getAllByTestId('example-button')[0]);

	await waitFor(() => expect(screen.getByText('a')).toBeInTheDocument());
	expect(evalCell).toHaveBeenCalledWith('(car (quote (a b)))');
	// The `#help` cell plus the example cell — the example is a real cell.
	expect(screen.getAllByTestId('repl-cell')).toHaveLength(2);
});

test('#reset clears the transcript and resets the session', async () => {
	const evalCell = vi.fn(async () => ({ ok: true, result: 'v', error: '' }));
	const onReset = vi.fn();
	render(Repl, { props: { evalCell, onReset } });

	await submit('(a)');
	await waitFor(() => expect(screen.getByText('v')).toBeInTheDocument());

	await submit('#reset');

	await waitFor(() => expect(screen.queryAllByTestId('repl-cell')).toHaveLength(0));
	expect(onReset).toHaveBeenCalledOnce();
	// `#reset` never reaches the server — it is a client directive.
	expect(evalCell).toHaveBeenCalledTimes(1);
});

test('the reset control in the status bar clears the transcript', async () => {
	const evalCell = async () => ({ ok: true, result: 'v', error: '' });
	const onReset = vi.fn();
	render(Repl, { props: { evalCell, onReset } });

	await submit('(a)');
	await waitFor(() => expect(screen.getByText('v')).toBeInTheDocument());

	const bar = screen.getByTestId('status-bar');
	await fireEvent.click(bar.querySelector('button')!);

	await waitFor(() => expect(screen.queryAllByTestId('repl-cell')).toHaveLength(0));
	expect(onReset).toHaveBeenCalledOnce();
});

// History arrived with the shared shell: submitted cells go into the ring, and
// ArrowUp recalls them (single-line input only — inside a multi-line form the
// arrows have to move the caret).
test('ArrowUp recalls submitted cells', async () => {
	const evalCell = async () => ({ ok: true, result: 'v', error: '' });
	render(Repl, { props: { evalCell } });

	await submit('(first)');
	await waitFor(() => expect(screen.getByText('v')).toBeInTheDocument());
	await submit('(second)');

	const input = screen.getByTestId('repl-input') as HTMLTextAreaElement;
	await fireEvent.keyDown(input, { key: 'ArrowUp' });
	expect(input.value).toBe('(second)');
	await fireEvent.keyDown(input, { key: 'ArrowUp' });
	expect(input.value).toBe('(first)');
	await fireEvent.keyDown(input, { key: 'ArrowDown' });
	expect(input.value).toBe('(second)');
});

// Enter submits only a balanced form; an unbalanced one gets an indented
// newline instead, which is what makes the one-line prompt usable.
test('Enter on an unbalanced form inserts an indented newline instead of submitting', async () => {
	const evalCell = vi.fn(async () => ({ ok: true, result: 'v', error: '' }));
	render(Repl, { props: { evalCell, specialForms: LISP_SPECIAL_FORMS } });

	const input = screen.getByTestId('repl-input') as HTMLTextAreaElement;
	await fireEvent.input(input, { target: { value: '(defun f (x)' } });
	input.selectionStart = input.selectionEnd = '(defun f (x)'.length;
	await fireEvent.keyDown(input, { key: 'Enter' });

	expect(evalCell).not.toHaveBeenCalled();
	expect(input.value).toBe('(defun f (x)\n  ');
	expect(screen.queryAllByTestId('repl-cell')).toHaveLength(0);
});

// On /lisp the prompt tracks the live dialect, so a cell must render the
// prompt it was SUBMITTED under. Rendering the current prompt against every
// cell retroactively relabels history: a form run in `lisp` would read as
// `acl2>` after a later `#lang acl2`, claiming a dialect it never ran in.
test('a cell keeps the prompt it was submitted under when the prompt changes', async () => {
	const evalCell = vi.fn(async () => ({ ok: true, result: '4', error: '' }));
	const { rerender } = render(Repl, { props: { evalCell, prompt: 'lisp>' } });

	await submit('(+ 2 2)');
	await waitFor(() => expect(screen.getByText('4')).toBeInTheDocument());

	// The dialect switches — the live prompt becomes acl2>, but the cell that
	// already ran must still show lisp>.
	await rerender({ evalCell, prompt: 'acl2>' });

	const cell = screen.getAllByTestId('repl-cell')[0];
	expect(cell.textContent).toContain('lisp>');
	expect(cell.textContent).not.toContain('acl2>');
});
