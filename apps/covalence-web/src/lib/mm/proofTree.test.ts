import { expect, test } from 'vitest';
import {
	applyChildren,
	assemble,
	newGoal,
	openGoals,
	replaceGoal,
	substToken,
	treeStatus
} from './proofTree';

/** Close `g` by applying `label` with the given children. */
function applied(
	g: ReturnType<typeof newGoal>,
	label: string,
	children: ReturnType<typeof newGoal>[]
) {
	return {
		...g,
		step: { via: 'apply' as const, label, kind: 'axiom' as const, subst: [], unsolved: [], children }
	};
}

test('applyChildren puts floats before essentials, in frame order', () => {
	// tpl's frame is (tt: term t, tr: term r); /apply returns floats in that
	// order, which is the order their subproofs must appear in.
	const kids = applyChildren(
		[
			{ var: 't', typecode: 'term', expr: 't' },
			{ var: 'r', typecode: 'term', expr: '0' }
		],
		[{ label: 'min', expr: '|- P' }]
	);
	expect(kids.map((k) => k.expr)).toEqual(['term t', 'term 0', '|- P']);
	expect(kids.map((k) => k.origin.kind)).toEqual(['float', 'float', 'essential']);
});

test('a float the goal does not determine yields a null-expr unsolved goal', () => {
	// mp's P occurs only in its hypotheses: normal, not an error.
	const kids = applyChildren(
		[
			{ var: 'P', typecode: 'wff', expr: null },
			{ var: 'Q', typecode: 'wff', expr: 't = t' }
		],
		[]
	);
	expect(kids[0]).toMatchObject({ expr: null, unsolved: true });
	expect(kids[1]).toMatchObject({ expr: 'wff t = t', unsolved: false });
});

test('assemble is post-order: arguments in frame order, then the label', () => {
	// The `th1` prefix: tt · tze · tpl proves `term ( t + 0 )`.
	const root = newGoal('term ( t + 0 )');
	const t = newGoal('term t');
	const zero = newGoal('term 0');
	const tree = applied(root, 'tpl', [
		{ ...t, step: { via: 'cite', labels: ['tt'] } },
		applied(zero, 'tze', [])
	]);
	expect(assemble(tree)).toEqual({ ok: true, steps: ['tt', 'tze', 'tpl'] });
});

test('assemble refuses a tree with an open leaf and names it', () => {
	const root = newGoal('|- t = t');
	const open = newGoal('|- P');
	const tree = applied(root, 'mp', [open]);
	const res = assemble(tree);
	expect(res.ok).toBe(false);
	if (!res.ok) expect(res.open.id).toBe(open.id);
});

test('openGoals and treeStatus report shape only', () => {
	const root = newGoal('|- t = t');
	const a = newGoal('|- P');
	const tree = applied(root, 'mp', [a]);
	expect(openGoals(tree).map((g) => g.expr)).toEqual(['|- P']);
	expect(treeStatus(tree)).toEqual({ nodes: 2, open: 1, closed: false });
	// "closed" is a statement about leaves, never about provedness.
	const done = replaceGoal(tree, a.id, { ...a, step: { via: 'cite', labels: ['min'] } });
	expect(treeStatus(done)).toEqual({ nodes: 2, open: 0, closed: true });
});

test('replaceGoal is structural and leaves the original tree intact', () => {
	const root = newGoal('|- t = t');
	const a = newGoal('|- P');
	const tree = applied(root, 'mp', [a]);
	const next = replaceGoal(tree, a.id, { ...a, step: { via: 'cite', labels: ['min'] } });
	expect(openGoals(next)).toHaveLength(0);
	expect(openGoals(tree)).toHaveLength(1); // undo stack still holds a usable tree
});

test('substToken replaces whole tokens only', () => {
	expect(substToken('|- ( P -> t = t )', 'P', 't = t')).toBe('|- ( t = t -> t = t )');
	// `ph` must not be clobbered when substituting `p`.
	expect(substToken('|- ( ph -> p )', 'p', 'X')).toBe('|- ( ph -> X )');
});
