//! `cov k` — reduce K programs against a K definition, kernel-checked. The K
//! frontend's CLI surface, peer of `cov hol`. Loads a `.k` definition (rewrite
//! rules in the first-order fragment), reduces a program, and prints its normal
//! form together with a note that the reduction is a hypothesis-free `⊢ Reduces`
//! theorem. See `notes/vibes/k/reduction-demo-scope.md`.

use std::path::PathBuf;

use clap::Subcommand;
use covalence_init::k::session::KSession;

#[derive(clap::Args)]
pub struct KArgs {
    #[command(subcommand)]
    pub command: KCommand,
}

#[derive(Subcommand)]
pub enum KCommand {
    /// Reduce a program against a `.k` definition to its normal form.
    Reduce(ReduceArgs),
    /// Run the built-in demo definitions (PEANO / colors / boolean).
    Demo,
}

#[derive(clap::Args)]
pub struct ReduceArgs {
    /// The `.k` definition file.
    pub definition: PathBuf,
    /// The program term to reduce, e.g. "plus(s(z()), s(z()))".
    pub program: String,
    /// Fuel bound (max reduction steps).
    #[arg(long, default_value_t = 100_000)]
    pub fuel: usize,
}

pub fn run(args: KArgs) {
    super::run_or_exit(match args.command {
        KCommand::Reduce(a) => reduce(a),
        KCommand::Demo => demo(),
    });
}

fn reduce(a: ReduceArgs) -> eyre::Result<()> {
    let src = std::fs::read_to_string(&a.definition)?;
    let session =
        KSession::from_source(&src).map_err(|e| eyre::eyre!("loading definition: {e}"))?;
    let r = a.program.clone();
    let out = session
        .reduce_with_fuel(&a.program, a.fuel)
        .map_err(|e| eyre::eyre!("reducing `{r}`: {e}"))?;
    println!("{}  =>  {}", a.program, out.rendered);
    if out.complete {
        println!("  (normal form; ⊢ Reduces is hypothesis-free, kernel-checked)");
    } else {
        println!("  (fuel exhausted; partial ⊢ Reduces, still kernel-checked)");
    }
    Ok(())
}

fn demo() -> eyre::Result<()> {
    const PEANO: &str = "\
module PEANO
  rule plus(z(), N) => N
  rule plus(s(M), N) => s(plus(M, N))
  rule mult(z(), N) => z()
  rule mult(s(M), N) => plus(N, mult(M, N))
endmodule";
    const COLORS: &str = "\
module COLORS
  rule colorOf(Banana()) => Yellow()
  rule contentsOfJar(Jar(F)) => F
endmodule";
    const BOOL: &str = "\
module BOOLSIMP
  rule and(tt(), X) => X
  rule and(ff(), X) => ff()
  rule or(tt(), X) => tt()
  rule or(ff(), X) => X
  rule neg(tt()) => ff()
  rule neg(ff()) => tt()
endmodule";
    const PEANO_MAX: &str = "\
module PEANO-MAX
  rule leq(z(), N) => true()
  rule leq(s(M), z()) => false()
  rule leq(s(M), s(N)) => leq(M, N)
  rule max(M, N) => N requires leq(M, N)
  rule max(M, N) => M requires leq(N, M)
endmodule";

    let cases: &[(&str, &str, &[&str])] = &[
        (
            "PEANO",
            PEANO,
            &["plus(s(s(z())), s(z()))", "mult(s(s(z())), s(s(z())))"],
        ),
        (
            "COLORS (K tutorial Lesson 1.2)",
            COLORS,
            &["colorOf(Banana())", "contentsOfJar(Jar(Kiwi()))"],
        ),
        ("BOOLSIMP", BOOL, &["and(or(tt(), ff()), neg(ff()))"]),
        (
            "PEANO-MAX (requires — Lesson 1.7)",
            PEANO_MAX,
            &["max(s(z()), s(s(z())))", "max(s(s(z())), s(z()))"],
        ),
    ];

    for (name, src, programs) in cases {
        let session = KSession::from_source(src).map_err(|e| eyre::eyre!("{name}: {e}"))?;
        println!("== {name} ==");
        for p in *programs {
            let out = session
                .reduce(p)
                .map_err(|e| eyre::eyre!("{name}: reducing {p}: {e}"))?;
            println!("  {p}  =>  {}", out.rendered);
        }
    }
    println!("\nEach `=>` is a hypothesis-free ⊢ Reduces theorem, kernel-checked.");
    Ok(())
}
