//! Deterministic ACL2 admission/proof workload driver.
//!
//! This executable is measurement infrastructure, not theorem evidence. It
//! prints a small tab-separated protocol; `scripts/bench-acl2.mjs` owns the
//! stable JSON schema, statistics, scoring, and regression policy.

use std::time::Instant;

use covalence_lisp::acl2::Acl2Session;

const SIZES: &[usize] = &[1, 2, 4, 8, 16];

fn nested_if(size: usize) -> String {
    let mut body = "x".to_string();
    for _ in 0..size {
        body = format!("(if (consp x) (car x) {body})");
    }
    body
}

fn nested_sum(size: usize) -> String {
    let mut sum = "0".to_string();
    for _ in 0..size {
        sum = format!("(+ 1 {sum})");
    }
    sum
}

fn measure(family: &str, size: usize, repetition: usize) -> (u128, bool, usize) {
    let (source, expected, theorem) = match family {
        "admission" => {
            let name = format!("branch-{size}-{repetition}");
            (
                format!("(defun {name} (x) {})", nested_if(size)),
                name,
                false,
            )
        }
        "proof" => {
            let name = format!("sum-{size}-{repetition}");
            (
                format!("(defthm {name} (equal {} {size}))", nested_sum(size)),
                name,
                true,
            )
        }
        _ => unreachable!(),
    };

    // Exclude the shared-theory/session bootstrap floor so authored workload
    // growth remains visible.
    let mut session = match Acl2Session::new() {
        Ok(session) => session,
        Err(_) => return (0, false, source.len()),
    };
    let started = Instant::now();
    let result = session.eval_cell(&source);
    let elapsed_ns = started.elapsed().as_nanos();
    let correct = matches!(result.as_deref(), Ok(value) if value == expected)
        && (!theorem || session.theorem(&expected).is_some());
    (elapsed_ns, correct, source.len())
}

fn main() {
    let mut args = std::env::args().skip(1);
    let repetitions = args
        .next()
        .and_then(|value| value.parse::<usize>().ok())
        .unwrap_or(5);
    let warmup = args
        .next()
        .and_then(|value| value.parse::<usize>().ok())
        .unwrap_or(1);

    println!("acl2-perf-v1");
    for family in ["admission", "proof"] {
        for &size in SIZES {
            for repetition in 0..warmup {
                let _ = measure(family, size, repetition);
            }
            for repetition in 0..repetitions {
                let (elapsed_ns, correct, source_bytes) =
                    measure(family, size, warmup + repetition);
                println!(
                    "{family}\t{size}\t{source_bytes}\t{repetition}\t{elapsed_ns}\t{}",
                    usize::from(correct)
                );
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{nested_if, nested_sum};

    #[test]
    fn workload_sizes_are_exact_and_monotone() {
        assert_eq!(nested_if(1), "(if (consp x) (car x) x)");
        assert_eq!(nested_sum(3), "(+ 1 (+ 1 (+ 1 0)))");
        assert!(nested_if(8).len() > nested_if(4).len());
        assert!(nested_sum(8).len() > nested_sum(4).len());
    }
}
