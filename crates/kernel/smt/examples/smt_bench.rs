//! # Demo: cvc5-found, kernel-checked linear-arithmetic infeasibility
//!
//! Builds a scalable infeasible bound chain `5 ≤ x₀ ≤ x₁ ≤ … ≤ xₙ₋₁ ≤ 2`,
//! lets **cvc5** decide it (UNSAT), and independently produces a **kernel-checked
//! proof** `⊢ (5 ≤ x₀) ⟹ … ⟹ (xₙ₋₁ ≤ 2) ⟹ ⊥` by replaying the transitivity
//! chain through `refute_chain` — the **same replay** run two ways:
//!
//! - `EvalDischarger` over the native `int`: the closed `5 ≤ 2` is decided by the
//!   `covalence-hol-eval` computation-cert TCB;
//! - `SuccDischarger` over `succ`-tower `nat`: the closed `5 ≤ 2` is proved by
//!   **pure induction, with no eval-TCB dependency at all**.
//!
//! Prints the theorem and benchmarks both against cvc5's wall time.
//!
//! Run:  `cargo run --release --example smt_bench -p covalence-kernel-smt`
//! (Needs a `cvc5` on `$PATH` for the solver column; skips it gracefully.)

use std::io::Write;
use std::process::Command;
use std::time::{Duration, Instant};

use covalence_core::Type;
use covalence_hol_api::{
    Discharger, EvalDischarger, LinOrder, NativeHol, Strict, SuccDischarger, SuccHol,
};
use covalence_kernel_smt::{Edge, refute_chain};

/// Build the infeasible chain `5 ≤ x₀ ≤ … ≤ x_{n-1} ≤ 2` over any ordered
/// backend `L` with discharger `D`, replay it into the hypothesis-free theorem
/// `⊢ (5 ≤ x₀) ⟹ … ⟹ ⊥`, and return the kernel replay time + the printed
/// conclusion. `carrier` is `L`'s number type (`int` / `nat`).
fn prove_infeasible<L, D>(l: &L, d: &D, carrier: &L::Type, n: usize) -> (Duration, String)
where
    L: LinOrder,
    D: Discharger<L>,
    L::Term: PartialEq + std::fmt::Display,
{
    let vars: Vec<_> = (0..n)
        .map(|i| l.var(&format!("x{i}"), carrier.clone()))
        .collect();

    // 5 … 2 with the intermediate variables between them.
    let mut points = vec![d.lit(l, 5)];
    points.extend(vars.iter().cloned());
    points.push(d.lit(l, 2));

    let mut atoms = Vec::new();
    let mut edges = Vec::new();
    for w in points.windows(2) {
        let atom = l.le(w[0].clone(), w[1].clone()).unwrap();
        atoms.push(atom.clone());
        edges.push(Edge::new(
            w[0].clone(),
            w[1].clone(),
            l.assume(atom).unwrap(),
            Strict::Le,
        ));
    }

    let start = Instant::now();
    // {atoms} ⊢ ⊥, then discharge each assumption → ⊢ atom₀ ⟹ … ⟹ ⊥.
    let bot = refute_chain(l, d, &edges).expect("infeasible ⟹ refutation");
    let mut thm = bot;
    for atom in atoms.iter().rev() {
        thm = l.imp_intro(thm, atom).unwrap();
    }
    let elapsed = start.elapsed();
    assert!(l.hyps(&thm).is_empty(), "discharged to a closed theorem");
    (elapsed, l.concl(&thm).to_string())
}

/// Emit the SMT-LIB problem for the same chain.
fn smt2(n: usize) -> String {
    let mut s = String::from("(set-logic QF_LIA)\n");
    for i in 0..n {
        s.push_str(&format!("(declare-fun x{i} () Int)\n"));
    }
    let pt = |i: usize| match i {
        0 => "5".to_string(),
        i if i == n + 1 => "2".to_string(),
        i => format!("x{}", i - 1),
    };
    for i in 0..=n {
        s.push_str(&format!("(assert (<= {} {}))\n", pt(i), pt(i + 1)));
    }
    s.push_str("(check-sat)\n");
    s
}

/// Run cvc5 on the problem, returning (verdict, wall time) — or `None` if absent.
fn run_cvc5(n: usize) -> Option<(String, Duration)> {
    let path = std::env::temp_dir().join(format!("cov_smt_bench_{n}.smt2"));
    std::fs::File::create(&path)
        .ok()?
        .write_all(smt2(n).as_bytes())
        .ok()?;
    let start = Instant::now();
    let out = Command::new("cvc5").arg(&path).output().ok()?;
    let verdict = String::from_utf8_lossy(&out.stdout).trim().to_string();
    Some((verdict, start.elapsed()))
}

fn ms(d: Duration) -> String {
    format!("{:.2} ms", d.as_secs_f64() * 1e3)
}

fn main() {
    println!("=== Covalence SMT — cvc5-found, kernel-checked, representation-generic ===\n");
    println!("Problem family:  5 ≤ x₀ ≤ x₁ ≤ … ≤ x_{{n-1}} ≤ 2   (infeasible for every n)\n");

    // The actual theorem, proved the eval-free way (succ-nat), for n = 3.
    let (_, concl) = prove_infeasible(&SuccHol, &SuccDischarger, &Type::nat(), 3);
    println!("Kernel theorem (n = 3, eval-TCB-FREE succ backend), hypothesis-free + checked:");
    println!("    ⊢ {concl}\n");

    if run_cvc5(2).is_none() {
        println!("(cvc5 not on $PATH — skipping the solver column)\n");
    }

    // Warm both backends' lazily-cached order lemmas so the first timed row isn't
    // skewed by one-time `cached_thm!` initialisation.
    prove_infeasible(&NativeHol, &EvalDischarger, &Type::int(), 2);
    prove_infeasible(&SuccHol, &SuccDischarger, &Type::nat(), 2);

    println!(
        "{:>6} | {:>12} | {:>16} | {:>18}",
        "n", "cvc5 (wall)", "kernel: int/eval", "kernel: succ/no-eval"
    );
    println!("{:->6}-+-{:->12}-+-{:->16}-+-{:->18}", "", "", "", "");
    for &n in &[3usize, 8, 32, 128, 512] {
        let (t_eval, _) = prove_infeasible(&NativeHol, &EvalDischarger, &Type::int(), n);
        let (t_succ, _) = prove_infeasible(&SuccHol, &SuccDischarger, &Type::nat(), n);
        let cvc5 = run_cvc5(n).map(|(v, d)| {
            assert_eq!(v, "unsat", "cvc5 must agree the chain is infeasible");
            ms(d)
        });
        println!(
            "{:>6} | {:>12} | {:>16} | {:>18}",
            n,
            cvc5.unwrap_or_else(|| "—".into()),
            ms(t_eval),
            ms(t_succ),
        );
    }
    println!(
        "\nOne `refute_chain`, three ways to establish the same infeasibility:\n\
         cvc5 (external solver), the eval kernel (`5 ≤ 2` by computation cert),\n\
         and a from-scratch `succ`-nat core (`5 ≤ 2` by pure induction — NO eval\n\
         TCB). Swapping the `Discharger` is the only change. Every kernel row is a\n\
         genuine hypothesis-free `⊢ … ⟹ ⊥` theorem.\n\
         (cvc5 wall time includes ~10 ms process startup, which the in-process\n\
         kernel replay avoids.)"
    );
}
