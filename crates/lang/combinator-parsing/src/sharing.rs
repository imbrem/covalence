//! Handing an outer loop's item to each step of an inner loop without cloning it once more
//! than necessary.
//!
//! The cross-product operators — relational `Ap` and `Bind`, in both encodings — consume one
//! *outer* item (a function value, a head witness) once per *inner* result. Every inner step
//! but the last genuinely needs its own copy. The last one does not: nothing reads the outer
//! item afterwards, so it can simply be moved.
//!
//! That final clone is not a rounding error. A relational witness at `Ap`-depth `j` is `j`
//! nodes deep and is cloned deeply, so a *fully deterministic* left-nested chain of `k` `Ap`s
//! producing a single result paid O(k²) allocations — 16770 at depth 128, against ~260 for
//! the witness it actually returns. Under genuine ambiguity the same clone multiplies the
//! mandatory retention cost by the depth.
//!
//! This is an allocation optimisation with no semantic content whatsoever. Enumeration order,
//! result count, and every witness are unchanged: the last iteration receives exactly the
//! value it used to receive a clone of.

/// Hand out `slot`'s value for one inner-loop step, cloning unless this is the last step.
///
/// `slot` is filled immediately before the inner loop and emptied only by the `is_last`
/// call, so the `expect` is unreachable for any caller that passes `is_last` exactly once,
/// on the final step.
pub(crate) fn clone_unless_last<T: Clone>(slot: &mut Option<T>, is_last: bool) -> T {
    if is_last { slot.take() } else { slot.clone() }
        .expect("the inner loop takes from its slot only on its final step")
}

#[cfg(test)]
mod tests {
    use super::clone_unless_last;

    /// The values handed out are the same ones an unconditional clone would hand out; only
    /// the final one is the original rather than a copy of it.
    #[test]
    fn hands_out_the_same_sequence_an_unconditional_clone_would() {
        let mut slot = Some(String::from("witness"));
        let handed: Vec<String> = (0..4)
            .map(|index| clone_unless_last(&mut slot, index + 1 == 4))
            .collect();
        assert_eq!(handed, vec!["witness"; 4]);
        assert_eq!(slot, None, "the last step moved rather than cloned");
    }

    /// A single-element inner loop is the case the optimisation exists for: it never clones.
    #[test]
    fn a_one_step_inner_loop_never_clones() {
        let mut slot = Some(String::from("witness"));
        assert_eq!(clone_unless_last(&mut slot, true), "witness");
        assert_eq!(slot, None);
    }

    /// An inner loop that never reaches its last step — because the body returned early on a
    /// budget failure — leaves the slot filled and is simply dropped.
    #[test]
    fn an_abandoned_inner_loop_leaves_the_slot_filled() {
        let mut slot = Some(String::from("witness"));
        assert_eq!(clone_unless_last(&mut slot, false), "witness");
        assert_eq!(slot.as_deref(), Some("witness"));
    }
}
