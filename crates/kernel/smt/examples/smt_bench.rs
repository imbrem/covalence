//! # Demo: cvc5-found, kernel-checked linear-arithmetic infeasibility
//!
//! Builds a scalable infeasible bound chain `5 ≤ x₀ ≤ x₁ ≤ … ≤ xₙ₋₁ ≤ 2`,
//! lets **cvc5** decide it (UNSAT), and independently produces a **kernel-checked
//! proof** `⊢ (5 ≤ x₀) ⟹ … ⟹ (xₙ₋₁ ≤ 2) ⟹ ⊥` by replaying the transitivity
//! chain through `refute_chain`. The closed comparison `5 ≤ 2` at the end is
//! discharged by the parametric [`EvalDischarger`] — swap it for a `succ`
//! discharger and the same proof runs with no eval-TCB dependency.
//!
//! Prints the theorem and benchmarks kernel-replay time against cvc5 wall time.
//!
//! Run:  `cargo run --release --example smt_bench -p covalence-kernel-smt`
//! (Needs a `cvc5` on `$PATH` for the solver column; skips it gracefully.)

use std::io::Write;
use std::process::Command;
use std::time::Instant;

use covalence_hol_api::{Hol, Int, LinOrder, NativeHol};
use covalence_hol_eval::EvalThm;
use covalence_hol_eval::derived::DerivedRules;
use covalence_kernel_smt::{Edge, EvalDischarger, Strict, refute_chain};

/// Build the infeasible chain `5 ≤ x₀ ≤ … ≤ x_{n-1} ≤ 2` and replay it into the
/// hypothesis-free theorem `⊢ (5 ≤ x₀) ⟹ … ⟹ ⊥`. Returns the theorem and the
/// kernel replay time.
fn prove_infeasible(n: usize) -> (EvalThm, std::time::Duration) {
    let l = NativeHol;
    let ty = l.int_ty();
    let vars: Vec<_> = (0..n)
        .map(|i| l.var(&format!("x{i}"), ty.clone()))
        .collect();

    // Endpoints 5 … 2 with the intermediate variables between them.
    let mut points = vec![l.int_lit(5)];
    points.extend(vars.iter().cloned());
    points.push(l.int_lit(2));

    // One `≤` edge between each adjacent pair.
    let mut atoms = Vec::new();
    let mut edges = Vec::new();
    for w in points.windows(2) {
        let atom = LinOrder::le(&l, w[0].clone(), w[1].clone()).unwrap();
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
    let bot = refute_chain(&l, &EvalDischarger, &edges).expect("infeasible ⟹ refutation");
    let mut thm = bot;
    for atom in atoms.iter().rev() {
        thm = thm.imp_intro(atom).unwrap();
    }
    let elapsed = start.elapsed();
    assert!(thm.hyps().is_empty(), "discharged to a closed theorem");
    (thm, elapsed)
}

/// Emit the SMT-LIB problem for the same chain.
fn smt2(n: usize) -> String {
    let mut s = String::from("(set-logic QF_LIA)\n");
    for i in 0..n {
        s.push_str(&format!("(declare-fun x{i} () Int)\n"));
    }
    let pt = |i: usize| {
        if i == 0 {
            "5".to_string()
        } else if i == n + 1 {
            "2".to_string()
        } else {
            format!("x{}", i - 1)
        }
    };
    for i in 0..=n {
        s.push_str(&format!("(assert (<= {} {}))\n", pt(i), pt(i + 1)));
    }
    s.push_str("(check-sat)\n");
    s
}

/// Run cvc5 on the problem, returning (verdict, wall time) — or `None` if cvc5
/// is not available.
fn run_cvc5(n: usize) -> Option<(String, std::time::Duration)> {
    let dir = std::env::temp_dir();
    let path = dir.join(format!("cov_smt_bench_{n}.smt2"));
    std::fs::File::create(&path)
        .ok()?
        .write_all(smt2(n).as_bytes())
        .ok()?;
    let start = Instant::now();
    let out = Command::new("cvc5").arg(&path).output().ok()?;
    let elapsed = start.elapsed();
    let verdict = String::from_utf8_lossy(&out.stdout).trim().to_string();
    Some((verdict, elapsed))
}

fn main() {
    println!("=== Covalence SMT — cvc5-found, kernel-checked ===\n");
    println!("Problem family:  5 ≤ x₀ ≤ x₁ ≤ … ≤ x_{{n-1}} ≤ 2   (infeasible for every n)\n");

    // Show the actual theorem for a small instance.
    let l = NativeHol;
    let (thm, _) = prove_infeasible(3);
    println!("Kernel theorem (n = 3), hypothesis-free and checked:");
    println!("    ⊢ {}\n", l.concl(&thm));

    let cvc5_available = run_cvc5(2).is_some();
    if !cvc5_available {
        println!("(cvc5 not on $PATH — skipping the solver column)\n");
    }

    println!(
        "{:>6} | {:>14} | {:>16} | {:>10}",
        "n", "cvc5 (wall)", "kernel replay", "verdict"
    );
    println!("{:->6}-+-{:->14}-+-{:->16}-+-{:->10}", "", "", "", "");
    for &n in &[3usize, 8, 32, 128, 512, 2048] {
        let (_thm, k) = prove_infeasible(n);
        let cvc5 = run_cvc5(n);
        let cvc5_str = match &cvc5 {
            Some((v, d)) => {
                assert_eq!(v, "unsat", "cvc5 must agree the chain is infeasible");
                format!("{:.2} ms", d.as_secs_f64() * 1e3)
            }
            None => "—".to_string(),
        };
        println!(
            "{:>6} | {:>14} | {:>13.2} ms | {:>10}",
            n,
            cvc5_str,
            k.as_secs_f64() * 1e3,
            "⊢ UNSAT"
        );
    }
    println!(
        "\nEvery kernel-replay row is a genuine `⊢ … ⟹ ⊥` theorem — cvc5 finds the\n\
         infeasibility, the kernel independently *proves* it. The closed `5 ≤ 2`\n\
         step is discharged by the parametric `EvalDischarger`; the same replay\n\
         runs over a `succ`-nat backend with no eval-TCB dependency.\n\
         (cvc5 wall time includes ~10 ms process startup — the fixed cost of\n\
         shelling out to the solver, which the in-process kernel replay avoids.)"
    );
}
