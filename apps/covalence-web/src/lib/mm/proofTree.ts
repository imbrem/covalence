// The backward proof tree behind the /metamath proof builder, and the
// forward (RPN) label sequence it assembles for POST /verify.
//
// HONESTY INVARIANT, load-bearing for the whole builder: nothing in this file
// decides that anything is *proved*. `assemble` turns a fully-closed tree into
// a label sequence and `treeStatus` reports whether any leaf is still open —
// both are bookkeeping about the *shape* of the tree. Only a `/verify`
// response with `ok:true` may be rendered as proved, and only with the
// conclusion that response returned. A tree with no open leaves is "closed,
// not yet checked".
import type { MmApplyFloat, MmAssertionKind, MmSubstEntry } from 'covalence-client';

/** How a goal came to exist, for display next to it. */
export type GoalOrigin =
  | { kind: 'root' }
  /** An essential ($e) hypothesis of the assertion applied to the parent. */
  | { kind: 'essential'; hypLabel: string }
  /** A floating ($f) hypothesis — a syntax obligation for one variable. */
  | { kind: 'float'; var: string; typecode: string };

/** A goal node. `expr` is a rendered statement whose first token is the
 * typecode (`|- t = t`, `wff P`, `term ( t + 0 )`), or `null` for a float
 * whose variable the goal did not determine — see {@link GoalNode.unsolved}. */
export interface GoalNode {
  id: number;
  expr: string | null;
  origin: GoalOrigin;
  /** True for a float goal whose variable is in the application's `unsolved`
   * list: the goal does not determine it, so the user must supply it. This is
   * NORMAL (e.g. `mp`'s `P` occurs only in its hypotheses), not an error. */
  unsolved: boolean;
  /** `null` while the goal is open. */
  step: GoalStep | null;
}

/** How a goal was closed. */
export type GoalStep =
  /** An assertion was applied backwards via POST /apply. `children` are the
   * assertion's hypotheses in **frame order** — floats first (the order
   * `/apply` returns them in), then essentials — which is exactly the order
   * their subproofs must appear in ahead of `label` in RPN. */
  | {
      via: 'apply';
      label: string;
      kind: MmAssertionKind;
      subst: MmSubstEntry[];
      unsolved: string[];
      children: GoalNode[];
    }
  /** A literal RPN fragment typed by the user. This is how hypothesis labels
   * are cited: `$f` floats are always citable and a theorem's own `$e` labels
   * become citable when `/verify` is passed that theorem's name. `/apply`
   * cannot express them — it only matches *assertions*. */
  | { via: 'cite'; labels: string[] };

let nextId = 1;
/** Fresh node id. Ids are per-session and only used as keyed-each identities. */
export function newGoal(
  expr: string | null,
  origin: GoalOrigin = { kind: 'root' },
  unsolved = false,
): GoalNode {
  return { id: nextId++, expr, origin, unsolved, step: null };
}

/** Build the children of an application, in frame order: every float (each a
 * syntax obligation `typecode expr`), then every essential subgoal. */
export function applyChildren(
  floats: MmApplyFloat[],
  subgoals: { label: string; expr: string }[],
): GoalNode[] {
  const kids: GoalNode[] = floats.map((f) =>
    newGoal(
      // `expr === null` ⟺ the var is unsolved; there is no goal text to show
      // until the user supplies one.
      f.expr === null ? null : `${f.typecode} ${f.expr}`,
      { kind: 'float', var: f.var, typecode: f.typecode },
      f.expr === null,
    ),
  );
  for (const s of subgoals) {
    kids.push(newGoal(s.expr, { kind: 'essential', hypLabel: s.label }));
  }
  return kids;
}

/** Depth-first walk, parents before children. */
export function* walk(root: GoalNode): Generator<GoalNode> {
  yield root;
  if (root.step?.via === 'apply') {
    for (const c of root.step.children) yield* walk(c);
  }
}

/** Every still-open leaf, in depth-first order — the goals the user has left
 * to do. A goal with a null `expr` (unsolved var) counts as open. */
export function openGoals(root: GoalNode): GoalNode[] {
  return [...walk(root)].filter((g) => g.step === null);
}

/** Replace `node` (matched by id) with `next` inside `root`, structurally —
 * returns a new tree, leaving `root` untouched so the caller can keep the old
 * one on an undo stack. */
export function replaceGoal(root: GoalNode, id: number, next: GoalNode): GoalNode {
  if (root.id === id) return next;
  if (root.step?.via !== 'apply') return root;
  return {
    ...root,
    step: { ...root.step, children: root.step.children.map((c) => replaceGoal(c, id, next)) },
  };
}

/** Substitute the single variable token `v` by the token string `expr`
 * throughout `stmt`.
 *
 * Metamath statements *are* token strings and substitution *is* token
 * replacement, so this is exact rather than an approximation — but it is still
 * only used to fill in a variable the user supplied for an unsolved float, so
 * that the sibling subgoals mentioning it read correctly. `/verify` remains
 * the judge of whether the resulting proof is a proof. */
export function substToken(stmt: string, v: string, expr: string): string {
  return stmt
    .split(' ')
    .map((t) => (t === v ? expr : t))
    .join(' ');
}

/** Apply {@link substToken} to every goal expression in a subtree.
 *
 * Used when the user supplies an expression for an unsolved float variable:
 * the variable occurs literally in the sibling subgoals `/apply` returned
 * (e.g. `mp`'s `P` in `|- P` and `|- ( P -> ... )`), so filling it in has to
 * propagate. Cosmetic-but-exact; `/verify` still adjudicates the result. */
export function substSubtree(n: GoalNode, v: string, expr: string): GoalNode {
  const next: GoalNode = {
    ...n,
    expr: n.expr === null ? null : substToken(n.expr, v, expr),
  };
  if (next.step?.via === 'apply') {
    next.step = {
      ...next.step,
      children: next.step.children.map((c) => substSubtree(c, v, expr)),
    };
  }
  return next;
}

/** Result of assembling a tree into a forward proof. */
export type Assembly =
  | { ok: true; steps: string[] }
  /** At least one leaf is still open; `open` is the first one encountered. */
  | { ok: false; open: GoalNode };

/** Post-order flatten to the RPN label sequence `/verify` wants: for each
 * applied assertion, its arguments' subproofs in frame order (floats, then
 * essentials), then the assertion's own label. A cited fragment contributes
 * its labels verbatim. */
export function assemble(root: GoalNode): Assembly {
  const steps: string[] = [];
  function go(n: GoalNode): GoalNode | null {
    const s = n.step;
    if (s === null) return n;
    if (s.via === 'cite') {
      steps.push(...s.labels);
      return null;
    }
    for (const c of s.children) {
      const open = go(c);
      if (open) return open;
    }
    steps.push(s.label);
    return null;
  }
  const open = go(root);
  return open ? { ok: false, open } : { ok: true, steps };
}

/** Counts for the builder's header. Deliberately says nothing about "proved". */
export function treeStatus(root: GoalNode): { nodes: number; open: number; closed: boolean } {
  const all = [...walk(root)];
  const open = all.filter((g) => g.step === null).length;
  return { nodes: all.length, open, closed: open === 0 };
}
