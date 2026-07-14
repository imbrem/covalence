use covalence_hash::O256;

use super::*;
use covalence_repl_core::{Fuel, Status};

// --- test foreign prims ---

struct TestIO {
    output: String,
}

impl TestIO {
    fn new() -> Self {
        TestIO {
            output: String::new(),
        }
    }
}

impl ForeignPrims for TestIO {
    fn call(&mut self, name: &str, ctx: &mut FCtx<'_>) -> Result<bool, FError> {
        match name {
            "print" => {
                let val = ctx.try_pop()?;
                let s = ctx.show(val);
                self.output.push_str(&s);
                self.output.push('\n');
                Ok(true)
            }
            _ => Ok(false),
        }
    }
}

// --- parsing & printing ---

#[test]
fn parse_atom() {
    let mut f = Forsp::new();
    let v = f.read_one("hello").unwrap();
    assert_eq!(f.show(v), "hello");
}

#[test]
fn parse_int() {
    let mut f = Forsp::new();
    let v = f.read_one("42").unwrap();
    assert_eq!(f.show(v), "42");
}

#[test]
fn parse_negative_int() {
    let mut f = Forsp::new();
    let v = f.read_one("-7").unwrap();
    assert_eq!(f.show(v), "-7");
}

#[test]
fn parse_list() {
    let mut f = Forsp::new();
    let v = f.read_one("(a b c)").unwrap();
    assert_eq!(f.show(v), "(a b c)");
}

#[test]
fn parse_nested_list() {
    let mut f = Forsp::new();
    let v = f.read_one("(a (b c) d)").unwrap();
    assert_eq!(f.show(v), "(a (b c) d)");
}

#[test]
fn parse_empty_list() {
    let mut f = Forsp::new();
    let v = f.read_one("()").unwrap();
    assert!(v.is_nil());
    assert_eq!(f.show(v), "()");
}

#[test]
fn parse_improper_list() {
    let mut f = Forsp::new();
    let v = f.read_one("(a . b)").unwrap();
    assert_eq!(f.heap.tag(v), Tag::Cons);
    assert_eq!(f.show(v), "(a . b)");
}

#[test]
fn sugar_splice_in_body() {
    let mut f = Forsp::new();
    let v = f.read("$x").unwrap();
    assert_eq!(f.show(v), "(quote x pop)");
}

#[test]
fn sugar_push_in_body() {
    let mut f = Forsp::new();
    let v = f.read("^x").unwrap();
    assert_eq!(f.show(v), "(quote x push)");
}

#[test]
fn sugar_quote_in_body() {
    let mut f = Forsp::new();
    let v = f.read("'x").unwrap();
    assert_eq!(f.show(v), "(quote x)");
}

#[test]
fn sugar_in_list() {
    let mut f = Forsp::new();
    let v = f.read_one("($x $y ^x)").unwrap();
    assert_eq!(f.show(v), "(quote x pop quote y pop quote x push)");
}

#[test]
fn sugar_quote_list() {
    let mut f = Forsp::new();
    let v = f.read("'(a b)").unwrap();
    assert_eq!(f.show(v), "(quote (a b))");
}

#[test]
fn comment_skipping() {
    let mut f = Forsp::new();
    let v = f.read("; comment\nhello").unwrap();
    assert_eq!(f.show(v), "(hello)");
}

// --- evaluator ---

#[test]
fn push_int() {
    let mut f = Forsp::new();
    f.run("42").unwrap();
    assert_eq!(f.pop_int(), 42);
}

#[test]
fn basic_arithmetic() {
    let mut f = Forsp::new();
    f.run("3 4 +").unwrap();
    assert_eq!(f.pop_int(), 7);
}

#[test]
fn subtraction() {
    let mut f = Forsp::new();
    f.run("10 3 -").unwrap();
    assert_eq!(f.pop_int(), 7);
}

#[test]
fn multiplication() {
    let mut f = Forsp::new();
    f.run("6 7 *").unwrap();
    assert_eq!(f.pop_int(), 42);
}

#[test]
fn variable_binding() {
    let mut f = Forsp::new();
    f.run("42 $x ^x").unwrap();
    assert_eq!(f.pop_int(), 42);
}

#[test]
fn closure_force() {
    let mut f = Forsp::new();
    f.run("(42) force").unwrap();
    assert_eq!(f.pop_int(), 42);
}

#[test]
fn closure_with_binding() {
    let mut f = Forsp::new();
    f.run("($x ^x 1 +) $inc  10 inc").unwrap();
    assert_eq!(f.pop_int(), 11);
}

#[test]
fn church_true() {
    let mut f = Forsp::new();
    f.run("($x $y ^x) $true  1 2 true").unwrap();
    assert_eq!(f.pop_int(), 2);
}

#[test]
fn church_false() {
    let mut f = Forsp::new();
    f.run("($x $y ^y) $false  1 2 false").unwrap();
    assert_eq!(f.pop_int(), 1);
}

#[test]
fn cons_car_cdr() {
    let mut f = Forsp::new();
    f.run("2 1 cons $pair  ^pair car  ^pair cdr").unwrap();
    assert_eq!(f.pop_int(), 2);
    assert_eq!(f.pop_int(), 1);
}

#[test]
fn eq_same() {
    let mut f = Forsp::new();
    f.run("'a 'a eq").unwrap();
    assert_eq!(f.pop_atom(), "t");
}

#[test]
fn eq_different() {
    let mut f = Forsp::new();
    f.run("'a 'b eq").unwrap();
    assert!(f.pop().is_nil());
}

#[test]
fn cswap_nil_swaps() {
    let mut f = Forsp::new();
    f.run("1 2 '() cswap").unwrap();
    assert_eq!(f.pop_int(), 1);
    assert_eq!(f.pop_int(), 2);
}

#[test]
fn cswap_nonnil_no_swap() {
    let mut f = Forsp::new();
    f.run("1 2 't cswap").unwrap();
    assert_eq!(f.pop_int(), 2);
    assert_eq!(f.pop_int(), 1);
}

#[test]
fn tag_int() {
    let mut f = Forsp::new();
    f.run("42 tag").unwrap();
    assert_eq!(f.pop_atom(), "num");
    assert_eq!(f.pop_int(), 42);
}

#[test]
fn lexical_scoping() {
    let mut f = Forsp::new();
    f.run("1 $x  ($x 2 $x ^x) $f  99 f  ^x").unwrap();
    let outer_x = f.pop_int();
    let inner_x = f.pop_int();
    assert_eq!(inner_x, 2);
    assert_eq!(outer_x, 1);
}

#[test]
fn if_true_branch() {
    let mut f = Forsp::new();
    f.run(
        "
        ($a $b ^a) $nip
        ($cond $else $then ^else ^then ^cond cswap nip force) $if
        (10) (20) 't if
    ",
    )
    .unwrap();
    assert_eq!(f.pop_int(), 10);
}

#[test]
fn if_false_branch() {
    let mut f = Forsp::new();
    f.run(
        "
        ($a $b ^a) $nip
        ($cond $else $then ^else ^then ^cond cswap nip force) $if
        (10) (20) '() if
    ",
    )
    .unwrap();
    assert_eq!(f.pop_int(), 20);
}

#[test]
fn recursive_factorial() {
    let mut f = Forsp::new();
    f.run(
        "
        ($a $b ^a) $nip
        ($cond $else $then ^else ^then ^cond cswap nip force) $if

        ($self $n
            (1)
            (^n  ^n 1 - ^self ^self force  *)
            ^n 1 eq
            if
        ) $fact-impl

        ($n ^n ^fact-impl ^fact-impl force) $fact

        5 fact
    ",
    )
    .unwrap();
    assert_eq!(f.pop_int(), 120);
}

#[test]
fn stack_introspection() {
    let mut f = Forsp::new();
    f.run("1 2 3 stack").unwrap();
    let s = f.pop();
    assert_eq!(f.show(s), "(3 2 1)");
}

#[test]
fn nested_closures() {
    let mut f = Forsp::new();
    f.run(
        "
        ($n ($x ^x ^n +)) $make-adder
        5 make-adder $add5
        10 add5 force
    ",
    )
    .unwrap();
    assert_eq!(f.pop_int(), 15);
}

#[test]
fn roundtrip_show_read() {
    let mut f = Forsp::new();
    let original = "(a (b 42) c)";
    let v = f.read_one(original).unwrap();
    assert_eq!(f.show(v), original);
}

#[test]
fn improper_list_roundtrip() {
    let mut f = Forsp::new();
    let v = f.read_one("(1 2 . 3)").unwrap();
    assert_eq!(f.show(v), "(1 2 . 3)");
}

// --- error cases ---

#[test]
fn error_stack_underflow() {
    let mut f = Forsp::new();
    let err = f.run("+").unwrap_err();
    assert!(matches!(err, FError::StackUnderflow));
}

#[test]
fn error_unbound_variable() {
    let mut f = Forsp::new();
    let err = f.run("nonexistent").unwrap_err();
    assert!(matches!(err, FError::Unbound(_)));
}

#[test]
fn error_type_mismatch() {
    let mut f = Forsp::new();
    let err = f.run("'a 'b +").unwrap_err();
    assert!(matches!(err, FError::Type { .. }));
}

#[test]
fn error_dangling_quote() {
    let mut f = Forsp::new();
    let err = f.run("quote").unwrap_err();
    assert!(matches!(err, FError::DanglingQuote));
}

// --- foreign prims ---

#[test]
fn foreign_print() {
    let mut f = Forsp::new_with(TestIO::new());
    f.run("42 print").unwrap();
    assert_eq!(f.foreign.output.trim(), "42");
}

#[test]
fn foreign_print_list() {
    let mut f = Forsp::new_with(TestIO::new());
    f.run("'(1 2 3) print").unwrap();
    assert_eq!(f.foreign.output.trim(), "(1 2 3)");
}

#[test]
fn foreign_multiple_prints() {
    let mut f = Forsp::new_with(TestIO::new());
    f.run("1 print 2 print 3 print").unwrap();
    assert_eq!(f.foreign.output, "1\n2\n3\n");
}

#[test]
fn foreign_unknown_returns_unbound() {
    let mut f = Forsp::new_with(TestIO::new());
    let err = f.run("nonexistent").unwrap_err();
    assert!(matches!(err, FError::Unbound(_)));
}

#[test]
fn env_overrides_foreign() {
    // Symbol definitions take precedence over foreign prims.
    let mut f = Forsp::new_with(TestIO::new());
    // Define `print` as a no-op that just drops the value.
    f.run("($x) $print  42 print").unwrap();
    // Our foreign print was NOT called.
    assert_eq!(f.foreign.output, "");
}

#[test]
fn foreign_in_closure() {
    let mut f = Forsp::new_with(TestIO::new());
    f.run("($x ^x print) $show  42 show").unwrap();
    assert_eq!(f.foreign.output.trim(), "42");
}

// --- Hash and Blob types ---

#[test]
fn hash_self_eval() {
    let mut f = Forsp::new();
    let h = O256::blob(b"hello");
    let v = f.heap.hash(h);
    f.push(v);
    // Hash values are self-evaluating — they should survive eval.
    assert_eq!(f.heap.tag(f.try_peek().unwrap()), Tag::Hash);
    assert_eq!(f.pop_hash(), h);
}

#[test]
fn hash_parse_hex() {
    let mut f = Forsp::new();
    let h = O256::blob(b"hello");
    let hex = h.to_string();
    let v = f.read_one(&hex).unwrap();
    assert_eq!(f.heap.tag(v), Tag::Hash);
    assert_eq!(f.heap.as_hash(v), h);
}

#[test]
fn hash_roundtrip() {
    let mut f = Forsp::new();
    let h = O256::blob(b"test");
    let v = f.heap.hash(h);
    let shown = f.show(v);
    assert_eq!(shown, h.to_string());
}

#[test]
fn hash_equality() {
    let mut f = Forsp::new();
    let h = O256::blob(b"hello");
    let hex = h.to_string();
    // Push two copies via parsing and test eq.
    f.run(&format!("{hex} {hex} eq")).unwrap();
    assert_eq!(f.pop_atom(), "t");
}

#[test]
fn hash_inequality() {
    let mut f = Forsp::new();
    let h1 = O256::blob(b"hello");
    let h2 = O256::blob(b"world");
    f.run(&format!("{h1} {h2} eq")).unwrap();
    assert!(f.pop().is_nil());
}

#[test]
fn hash_tag() {
    let mut f = Forsp::new();
    let h = O256::blob(b"hello");
    let hex = h.to_string();
    f.run(&format!("{hex} tag")).unwrap();
    assert_eq!(f.pop_atom(), "hash");
}

#[test]
fn blob_from_string() {
    let mut f = Forsp::new();
    let v = f.read_one("\"hello\"").unwrap();
    assert_eq!(f.heap.tag(v), Tag::Blob);
    assert_eq!(f.heap.as_blob(v), b"hello");
}

#[test]
fn blob_self_eval() {
    let mut f = Forsp::new();
    f.run("\"hello\"").unwrap();
    assert_eq!(f.heap.tag(f.try_peek().unwrap()), Tag::Blob);
    assert_eq!(f.pop_blob(), b"hello");
}

#[test]
fn blob_equality() {
    let mut f = Forsp::new();
    f.run("\"hello\" \"hello\" eq").unwrap();
    assert_eq!(f.pop_atom(), "t");
}

#[test]
fn blob_inequality() {
    let mut f = Forsp::new();
    f.run("\"hello\" \"world\" eq").unwrap();
    assert!(f.pop().is_nil());
}

#[test]
fn blob_tag() {
    let mut f = Forsp::new();
    f.run("\"hello\" tag").unwrap();
    assert_eq!(f.pop_atom(), "blob");
}

#[test]
fn blob_in_foreign_print() {
    let mut f = Forsp::new_with(TestIO::new());
    f.run("\"hello\" print").unwrap();
    assert_eq!(f.foreign.output.trim(), "\"hello\"");
}

#[test]
fn hash_in_foreign_print() {
    let mut f = Forsp::new_with(TestIO::new());
    let h = O256::blob(b"hello");
    f.run(&format!("{h} print")).unwrap();
    assert_eq!(f.foreign.output.trim(), &h.to_string());
}

// --- content-addressed Forsp values ---

#[test]
fn content_hash_nil_is_stable() {
    let mut f1 = Forsp::new();
    let mut f2 = Forsp::new();
    assert_eq!(
        f1.heap.content_hash(ValRef::NIL),
        f2.heap.content_hash(ValRef::NIL),
    );
}

#[test]
fn content_hash_disjoint_by_kind() {
    // Same logical "value" under different cell tags must not collide.
    let mut f = Forsp::new();
    let nil_h = f.heap.content_hash(ValRef::NIL);
    let zero = f.heap.int(0);
    let zero_h = f.heap.content_hash(zero);
    let empty_atom = f.heap.atom("");
    let empty_atom_h = f.heap.content_hash(empty_atom);
    let empty_blob = f.heap.blob(vec![]);
    let empty_blob_h = f.heap.content_hash(empty_blob);
    assert_ne!(nil_h, zero_h);
    assert_ne!(nil_h, empty_atom_h);
    assert_ne!(nil_h, empty_blob_h);
    assert_ne!(empty_atom_h, empty_blob_h);
}

#[test]
fn content_hash_structural_equality() {
    // Two cons lists built independently with content-equal cells hash the
    // same — that's the whole point of content addressing.
    let mut f = Forsp::new();
    let a1 = f.heap.int(1);
    let a2 = f.heap.int(2);
    let l1 = {
        let tail = f.heap.cons(a2, ValRef::NIL);
        f.heap.cons(a1, tail)
    };
    let l2 = {
        let b1 = f.heap.int(1);
        let b2 = f.heap.int(2);
        let tail = f.heap.cons(b2, ValRef::NIL);
        f.heap.cons(b1, tail)
    };
    assert_ne!(l1, l2);
    assert_eq!(f.heap.content_hash(l1), f.heap.content_hash(l2));
}

#[test]
fn content_hash_distinguishes_atom_from_blob() {
    let mut f = Forsp::new();
    let a = f.heap.atom("hello");
    let b = f.heap.blob(b"hello".to_vec());
    assert_ne!(f.heap.content_hash(a), f.heap.content_hash(b));
}

#[test]
fn value_at_round_trips_a_list() {
    let mut f = Forsp::new();
    let v = f.read_one("(a (b 42) c)").unwrap();
    let h = f.content_hash(v);
    assert_eq!(f.heap.value_at(h), Some(v));
}

#[test]
fn bang_hex_resolves_to_registered_value() {
    let mut f = Forsp::new();
    let v = f.read_one("(1 2 3)").unwrap();
    let h = f.content_hash(v);
    let src = format!("!{h}");
    let resolved = f.read_one(&src).unwrap();
    assert_eq!(resolved, v);
}

#[test]
fn bang_hex_unknown_errors() {
    let mut f = Forsp::new();
    // Some never-hashed hash → reader rejects.
    let h = O256::blob(b"definitely not in this heap");
    let err = f.read_one(&format!("!{h}")).unwrap_err();
    assert!(matches!(err, FError::Parse(_)));
}

#[test]
fn bang_non_hex_falls_through_to_atom() {
    // `!foo` (rest is not 64 hex chars) should NOT trigger lookup; it stays
    // a regular atom that the evaluator can fail on as "unbound".
    let mut f = Forsp::new();
    let v = f.read_one("!foo").unwrap();
    assert_eq!(f.heap.tag(v), Tag::Atom);
    assert_eq!(f.heap.as_atom(v), "!foo");
}

#[test]
fn closure_prints_as_bang_hex() {
    let mut f = Forsp::new();
    f.run("($x ^x 1 +) $inc  ^inc").unwrap();
    let top = f.try_peek().unwrap();
    assert_eq!(f.heap.tag(top), Tag::Closure);
    let shown = f.show(top);
    assert!(shown.starts_with('!'), "got {shown:?}");
    assert_eq!(shown.len(), 1 + 64);
}

#[test]
fn closure_print_then_read_recovers_it() {
    let mut f = Forsp::new();
    // Build a closure on the stack.
    f.run("($x ^x 1 +) $inc  ^inc").unwrap();
    let original = f.pop();
    let shown = f.show(original);
    // Read the `!HEX` form back and check it's the same closure.
    let recovered = f.read_one(&shown).unwrap();
    assert_eq!(recovered, original);
    // It is still applicable.
    let ten = f.heap.int(10);
    f.push(ten);
    f.push(recovered);
    f.run("force").unwrap();
    assert_eq!(f.pop_int(), 11);
}

#[test]
fn structurally_equal_closures_share_a_hash() {
    // Push two closures with content-equal body and env onto the stack.
    let mut f = Forsp::new();
    f.run("($x ^x) ($x ^x)").unwrap();
    let b = f.pop();
    let a = f.pop();
    assert_ne!(a, b);
    assert_eq!(f.heap.tag(a), Tag::Closure);
    assert_eq!(f.heap.tag(b), Tag::Closure);
    assert_eq!(f.heap.content_hash(a), f.heap.content_hash(b));
}

// --- small-step reduction (differential: small-step == big-step) ------------

/// Render the top-of-stack value produced by big-step [`exec`].
fn big_step_top(source: &str) -> String {
    let mut f = Forsp::new();
    f.run(source).unwrap();
    let top = f.try_peek().unwrap();
    f.show(top)
}

/// Reduce `source` small-step and render the top-of-stack value off the final
/// snapshot, keeping the runtime alive to read the heap.
fn small_step_render(source: &str) -> (String, u64, Status) {
    let mut f = Forsp::new();
    let program = f.read(source).unwrap();
    let sem = ForspSemantics::new(f);
    let input = sem.initial(program);
    use covalence_repl_core::{Reduction, RunToValue, Strategy};
    let mut red: Reduction<ForspRepr, ForspSemantics<()>> = Reduction::start(input);
    RunToValue.drive(&sem, &mut red, Fuel::UNBOUNDED).unwrap();
    let status = red.status();
    let steps = red.steps();
    let (head, _) = red.into_parts();
    let rendered = sem.with_runtime(|rt| {
        if head.stack.is_nil() {
            "()".to_string()
        } else {
            let top = rt.heap.car(head.stack);
            rt.show(top)
        }
    });
    (rendered, steps, status)
}

/// Assert small-step and big-step agree on the rendered top value, and that the
/// small-step reduction halted with a positive step count.
fn assert_differential(source: &str) {
    let big = big_step_top(source);
    let (small, steps, status) = small_step_render(source);
    assert_eq!(small, big, "small-step != big-step for `{source}`");
    assert_eq!(status, Status::Value, "did not halt: `{source}`");
    assert!(steps > 0, "no steps taken for `{source}`");
}

#[test]
fn small_step_push_int() {
    assert_differential("42");
}

#[test]
fn small_step_arithmetic() {
    assert_differential("3 4 +");
}

#[test]
fn small_step_variable_binding() {
    assert_differential("42 $x ^x");
}

#[test]
fn small_step_closure_force() {
    assert_differential("(42) force");
}

#[test]
fn small_step_closure_with_binding() {
    assert_differential("($x ^x 1 +) $inc  10 inc");
}

#[test]
fn small_step_church_false() {
    assert_differential("($x $y ^y) $false  1 2 false");
}

#[test]
fn small_step_cons_car() {
    assert_differential("2 1 cons car");
}

#[test]
fn small_step_lexical_scoping() {
    // Two values on the stack; render checks the top (outer x == 1).
    assert_differential("1 $x  ($x 2 $x ^x) $f  99 f  ^x");
}

#[test]
fn small_step_nested_closures() {
    assert_differential(
        "
        ($n ($x ^x ^n +)) $make-adder
        5 make-adder $add5
        10 add5 force
    ",
    );
}

#[test]
fn small_step_recursive_factorial() {
    // The recursion goes through the reified continuation, not the Rust stack.
    assert_differential(
        "
        ($a $b ^a) $nip
        ($cond $else $then ^else ^then ^cond cswap nip force) $if

        ($self $n
            (1)
            (^n  ^n 1 - ^self ^self force  *)
            ^n 1 eq
            if
        ) $fact-impl

        ($n ^n ^fact-impl ^fact-impl force) $fact

        5 fact
    ",
    );
}

#[test]
fn small_step_trace_is_monotone() {
    // The trace records input-first and grows by exactly `steps` transitions.
    let f = Forsp::new();
    let red = f.reduce_source("3 4 +").unwrap();
    assert_eq!(red.status, Status::Value);
    assert_eq!(red.trace.len() as u64, red.steps);
    assert!(red.trace.states.len() >= 2);
    // The first snapshot is the un-stepped input (empty stack, one frame).
    let first = &red.trace.states[0];
    assert!(first.stack.is_nil());
    assert_eq!(first.control.len(), 1);
    // The last snapshot is halted.
    assert!(red.trace.states.last().unwrap().is_halted());
}

#[test]
fn small_step_fuel_bound_diverges_not_hangs() {
    // A bounded pull on a program that needs more than 2 steps reports
    // `Diverging`, not a value — the streaming non-termination story.
    let mut f = Forsp::new();
    let program = f.read("1 2 3 4 + + +").unwrap();
    let red = f.forsp_reduce(program, Fuel::steps(2)).unwrap();
    assert!(matches!(red.status, Status::Diverging(_)));
    assert_eq!(red.steps, 2);
}
