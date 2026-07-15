import { render, screen, fireEvent, waitFor } from '@testing-library/svelte';
import { expect, test, vi } from 'vitest';
import Repl from './Repl.svelte';

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

	const input = screen.getByRole('textbox');
	await fireEvent.input(input, { target: { value: '(atom? (quote a))' } });
	await fireEvent.keyDown(input, { key: 'Enter' });

	// The result renders …
	await waitFor(() => expect(screen.getByText('t')).toBeInTheDocument());
	// … and the transient "proving…" is gone (the regression left it stuck).
	expect(screen.queryByText(/proving/)).toBeNull();
	expect(evalCell).toHaveBeenCalledWith('(atom? (quote a))');
});

test('an error result renders (not stuck on proving…)', async () => {
	const evalCell = async () => ({ ok: false, result: '', error: 'boom' });
	render(Repl, { props: { evalCell } });

	const input = screen.getByRole('textbox');
	await fireEvent.input(input, { target: { value: '(oops)' } });
	await fireEvent.keyDown(input, { key: 'Enter' });

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

	const input = screen.getByRole('textbox');
	await fireEvent.input(input, { target: { value: '#lang foo' } });
	await fireEvent.keyDown(input, { key: 'Enter' });

	await waitFor(() => expect(container.querySelector('.out.err')).not.toBeNull());
	const hints = [...container.querySelectorAll('.lang-hint')].map((h) => h.textContent);
	// The bare mention and the `#lang scheme` suggestion both pop as chips …
	expect(hints).toEqual(['#lang', '#lang scheme']);
	// … while the message text survives verbatim (marked up, never rewritten).
	expect(container.querySelector('.out.err')!.textContent).toContain(
		'unknown #lang `foo` (try: lisp | scheme | sector); see #lang scheme'
	);
});

test('an example marked active gets the .active class', () => {
	const evalCell = async () => ({ ok: true, result: '', error: '' });
	render(Repl, {
		props: {
			evalCell,
			examples: [
				{ title: '#lang lisp', src: '#lang lisp', active: true },
				{ title: '#lang scheme', src: '#lang scheme' }
			]
		}
	});

	expect(screen.getByRole('button', { name: '#lang lisp' }).classList.contains('active')).toBe(
		true
	);
	expect(screen.getByRole('button', { name: '#lang scheme' }).classList.contains('active')).toBe(
		false
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

	const input = screen.getByRole('textbox');
	await fireEvent.input(input, { target: { value: '(app (quote (a b)) (quote (c)))' } });
	await fireEvent.keyDown(input, { key: 'Enter' });
	await waitFor(() => expect(screen.getByText('(a b c)')).toBeInTheDocument());

	await fireEvent.mouseEnter(container.querySelector('.cell')!);
	await waitFor(() => expect(container.querySelector('.hol')!.textContent).toBe(sequent));
	expect(showCell).toHaveBeenCalledWith('(app (quote (a b)) (quote (c)))');
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

	const input = screen.getByRole('textbox');
	await fireEvent.input(input, { target: { value: '(defun app (x y) y)' } });
	await fireEvent.keyDown(input, { key: 'Enter' });
	await waitFor(() => expect(screen.getByText('app')).toBeInTheDocument());

	await fireEvent.mouseEnter(container.querySelector('.cell')!);
	await waitFor(() => expect(container.querySelector('.hol')).toBeNull());
	expect(container.querySelector('.cell')!.classList.contains('has-hol')).toBe(false);
	expect(screen.queryByText(/fetching proof/)).toBeNull();
});

test('an example button runs and shows its result', async () => {
	const evalCell = async () => ({ ok: true, result: 'a', error: '' });
	render(Repl, {
		props: { evalCell, examples: [{ title: 'car', src: '(car (quote (a b)))' }] }
	});

	await fireEvent.click(screen.getByRole('button', { name: 'car' }));
	await waitFor(() => expect(screen.getByText('a')).toBeInTheDocument());
});
