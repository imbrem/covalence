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

test('an example button runs and shows its result', async () => {
	const evalCell = async () => ({ ok: true, result: 'a', error: '' });
	render(Repl, {
		props: { evalCell, examples: [{ title: 'car', src: '(car (quote (a b)))' }] }
	});

	await fireEvent.click(screen.getByRole('button', { name: 'car' }));
	await waitFor(() => expect(screen.getByText('a')).toBeInTheDocument());
});
