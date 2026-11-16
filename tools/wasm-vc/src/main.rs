//! `wasm-vc`: verification conditions for annotated WAT in the Wasm
//! specification library (`docs/wasm-spec-library.md`).
//!
//! * `vcs`: print the conditions of an entry (SMT-LIB and Lean statements);
//! * `smt`: check them with z3, cvc5 or bitwuzla (oracles only);
//! * `gen`: generate the `tactic+script` solution module: conditions with
//!   tactics chosen by trying candidates in Lean (hints from solver cores),
//!   and the program-logic proof of the specification;
//! * `agent`: the `all-in` loop: `gen`, then a model proposes an invariant and
//!   proofs for the residual conditions, each checked by Lean, with a log;
//! * `reflect`: annotated WAT (`i32` and `i64`) to the reflective VC generator
//!   `Silmaril.Wasm.Auto.VCGen`: Lean computes the conditions, z3 checks them as
//!   Lean prints them, candidate tactics prove them (docs/wasm-auto-verify.md).

mod agent;
mod lean;
mod reflect;
mod sexp;
mod smt;
mod sym;
mod term;
mod vc;
mod wat;

use anyhow::{Context, Result, bail};
use clap::{Parser, Subcommand};
use std::path::{Path, PathBuf};
use std::process::Command;

#[derive(Parser)]
#[command(name = "wasm-vc", about = "Verification conditions for annotated WAT")]
struct Cli {
    /// Root of the Lean (Lake) project holding the Silmaril libraries; default: the nearest
    /// ancestor directory with a `lakefile.toml`
    #[arg(long, global = true)]
    root: Option<PathBuf>,
    #[command(subcommand)]
    command: Cmd,
}

static ROOT: std::sync::OnceLock<Option<PathBuf>> = std::sync::OnceLock::new();

/// The Lake project root: `--root` if given, else the nearest ancestor of `start` with a
/// `lakefile.toml`.
pub fn lake_root(start: &Path) -> Result<PathBuf> {
    if let Some(Some(r)) = ROOT.get() {
        return std::fs::canonicalize(r).with_context(|| format!("--root {}", r.display()));
    }
    start
        .ancestors()
        .find(|p| p.join("lakefile.toml").is_file())
        .map(Path::to_path_buf)
        .with_context(|| {
            format!(
                "no lakefile.toml above {}: run inside a Lean project with the Silmaril libraries or pass --root",
                start.display()
            )
        })
}

#[derive(Subcommand)]
enum Cmd {
    /// Print the verification conditions of an entry
    Vcs { entry: PathBuf },
    /// Check the conditions with SMT solvers
    Smt {
        entry: PathBuf,
        #[arg(long, default_value = "z3")]
        solver: Vec<String>,
    },
    /// Generate the `tactic+script` solution module
    Gen {
        entry: PathBuf,
        /// Module name under `Silmaril/Proofs/WasmSpec/<Entry>/`
        #[arg(long, default_value = "Script")]
        name: String,
        /// Skip the SMT oracle (use every hint)
        #[arg(long)]
        no_smt: bool,
    },
    /// Run the agentic `all-in` loop
    Agent(agent::Args),
    /// Solve one Wasm problem (`*.toml`: equiv, post, bmc); see docs/wasm-solvers.md
    Solve {
        problem: PathBuf,
        #[arg(long)]
        solver: Option<String>,
        /// Per-goal solver timeout in seconds
        #[arg(long)]
        timeout: Option<u64>,
        /// Print the report as JSON
        #[arg(long)]
        json: bool,
        /// Write the JSON report to a file
        #[arg(long)]
        out: Option<PathBuf>,
        /// Loop unrolling bound (overrides the problem's)
        #[arg(long)]
        unroll: Option<u32>,
    },
    /// Generate (and check) a Lean statement and proof attempt for an annotated-WAT problem
    Lean {
        problem: PathBuf,
        /// Output file (default: target/wasm-vc/lean/<Name>.lean in the checkout)
        #[arg(long)]
        out: Option<PathBuf>,
        /// Lean namespace prefix
        #[arg(long, default_value = "Silmaril.Wasm.Problems.Generated")]
        namespace: String,
        /// Check the file with `lake env lean`
        #[arg(long)]
        check: bool,
    },
    /// Solve the Wasm leaves of a dag.json and write the DAG with verdicts back
    Dag {
        dag: PathBuf,
        #[arg(short, long, default_value_t = 2)]
        jobs: usize,
        #[arg(long)]
        timeout: Option<u64>,
        #[arg(long)]
        unroll: Option<u32>,
        /// Output DAG (default: overwrite the input)
        #[arg(long)]
        out: Option<PathBuf>,
    },
    /// Solve every problem under a directory, at most `jobs` at a time
    Drive {
        dir: PathBuf,
        #[arg(short, long, default_value_t = 2)]
        jobs: usize,
        #[arg(long)]
        solver: Option<String>,
        #[arg(long)]
        timeout: Option<u64>,
        /// Only problems whose path contains this string
        #[arg(long)]
        filter: Option<String>,
        #[arg(long)]
        unroll: Option<u32>,
        /// Write the JSON summary to a file
        #[arg(long)]
        out: Option<PathBuf>,
    },
    /// Verify one function with the reflective generator (`reflect.toml`)
    Reflect {
        /// The configuration file (`reflect.toml`)
        config: PathBuf,
        /// Output directory (default `target/wasm-vc/reflect/<name>`)
        #[arg(long)]
        out: Option<PathBuf>,
        /// Skip the z3 check
        #[arg(long)]
        no_smt: bool,
    },
}

pub struct Ctx {
    pub root: PathBuf,
    pub entry_dir: PathBuf,
    pub cfg: vc::Config,
    pub module: wat::Module,
}

impl Ctx {
    pub fn load(entry: &Path) -> Result<Self> {
        let entry_dir = std::fs::canonicalize(entry)?;
        let root = lake_root(&entry_dir)?;
        let cfg: vc::Config = toml::from_str(&std::fs::read_to_string(entry_dir.join("vc.toml"))?)
            .context("invalid vc.toml")?;
        let src = std::fs::read_to_string(entry_dir.join(&cfg.source))?;
        let module = wat::parse_module(&src)?;
        Ok(Ctx {
            root,
            entry_dir,
            cfg,
            module,
        })
    }

    pub fn namespace(&self) -> String {
        format!("Silmaril.WasmSpec.{}", self.cfg.entry)
    }

    pub fn work_dir(&self) -> Result<PathBuf> {
        let d = self.root.join("target/wasm-vc").join(&self.cfg.entry);
        std::fs::create_dir_all(&d)?;
        Ok(d)
    }

    /// `lake env lean <file>`: whether it succeeded, and the output.
    pub fn lean(&self, file: &Path) -> Result<(bool, String)> {
        self.lean_with(file, false)
    }

    /// `lake env lean`, with warnings as errors when `strict` (as `lake build --wfail`).
    pub fn lean_with(&self, file: &Path, strict: bool) -> Result<(bool, String)> {
        let mut cmd = Command::new("nice");
        cmd.args(["lake", "env", "lean"]);
        if strict {
            cmd.arg("-DwarningAsError=true");
        }
        let out = cmd
            .arg(file)
            .current_dir(&self.root)
            .output()
            .context("could not run lake")?;
        let mut text = String::from_utf8_lossy(&out.stdout).to_string();
        text.push_str(&String::from_utf8_lossy(&out.stderr));
        Ok((out.status.success(), text))
    }
}

/// Lines with errors in Lean output for `file`.
pub fn error_lines(output: &str, file: &Path) -> Vec<usize> {
    let name = file.to_string_lossy();
    output
        .lines()
        .filter_map(|l| {
            let rest = l.strip_prefix(name.as_ref())?.strip_prefix(':')?;
            let mut parts = rest.splitn(3, ':');
            let line = parts.next()?.parse().ok()?;
            let _col = parts.next()?;
            parts
                .next()?
                .trim_start()
                .starts_with("error")
                .then_some(line)
        })
        .collect()
}

pub struct Generated {
    pub text: String,
    pub residual: Vec<usize>,
    pub tactics: Vec<Option<String>>,
    pub report: String,
}

/// Generate a solution: SMT oracle, candidate trial in Lean, assembly.
/// `extra[i]` are additional candidate tactics for condition `i` (agent proposals),
/// tried before the built-in ones; `prelude` is Lean text (agent lemmas) placed
/// before the conditions.
pub fn generate(
    ctx: &Ctx,
    a: &vc::Analysis,
    sub: &str,
    doc: &str,
    use_smt: bool,
    extra: &[Vec<String>],
    prelude: &str,
) -> Result<Generated> {
    let dir = ctx.work_dir()?;
    let mut report = String::new();
    let mut hint_sets = Vec::new();
    for vc in &a.vcs {
        let mut core: Option<Vec<String>> = None;
        if use_smt && smt::available("z3") {
            let o = smt::run("z3", vc, &ctx.cfg, &dir)?;
            report.push_str(&format!(
                "{}: z3 {} ({:.2}s){}\n",
                vc.name,
                o.status,
                o.seconds,
                if o.core.is_empty() {
                    String::new()
                } else {
                    format!(", core hints {:?}", o.core)
                }
            ));
            if o.status == "sat" {
                report.push_str(&format!("  counterexample:\n{}\n", o.model));
            }
            if o.status == "unsat" {
                core = Some(o.core);
            }
        }
        let names = core.unwrap_or_else(|| ctx.cfg.hint.iter().map(|h| h.name.clone()).collect());
        let hints: Vec<String> = ctx
            .cfg
            .hint
            .iter()
            .filter(|h| names.contains(&h.name) && !h.lean.is_empty())
            .map(|h| h.lean.clone())
            .collect();
        hint_sets.push(hints);
    }
    let cands: Vec<Vec<String>> = a
        .vcs
        .iter()
        .enumerate()
        .map(|(i, vc)| {
            let mut c = extra.get(i).cloned().unwrap_or_default();
            c.extend(lean::candidates(vc, &ctx.cfg, &hint_sets[i]));
            c
        })
        .collect();
    let header = lean::Header {
        cfg: &ctx.cfg,
        namespace: ctx.namespace(),
        sub,
        module: false,
        doc: "Trial of candidate tactics (generated, not kept).".into(),
    };
    let (mut trial, mut ranges) = lean::trial(&header, a, &cands);
    if !prelude.is_empty() {
        // Put agent lemmas right after the `open` lines.
        let at = trial.find("\n\n-- ").map_or(trial.len(), |p| p + 2);
        let shift = prelude.lines().count() + 1;
        trial.insert_str(at, &format!("{prelude}\n"));
        for r in &mut ranges {
            r.2 += shift;
            r.3 += shift;
        }
    }
    let file = dir.join(format!("{sub}Trial.lean"));
    std::fs::write(&file, &trial)?;
    let (_, out) = ctx.lean(&file)?;
    let errors = error_lines(&out, &file);
    let prelude_end = trial
        .find("\n\n-- ")
        .map_or(0, |p| trial[..p].lines().count());
    if errors.iter().any(|&l| l <= prelude_end) {
        bail!("the trial preamble does not compile:\n{out}");
    }
    let mut tactics: Vec<Option<String>> = vec![None; a.vcs.len()];
    for &(i, j, start, end) in &ranges {
        if tactics[i].is_none() && !errors.iter().any(|&l| l >= start && l <= end) {
            tactics[i] = Some(cands[i][j].clone());
        }
    }
    let residual: Vec<usize> = (0..a.vcs.len()).filter(|&i| tactics[i].is_none()).collect();
    for (i, vc) in a.vcs.iter().enumerate() {
        report.push_str(&format!(
            "{}: {}\n",
            vc.name,
            match &tactics[i] {
                Some(t) => format!("Lean accepts `{}`", t.replace('\n', "; ")),
                None => "no candidate accepted (residual)".into(),
            }
        ));
    }
    let chosen: Vec<String> = tactics
        .iter()
        .map(|t| t.clone().unwrap_or_else(|| "sorry".into()))
        .collect();
    let header = lean::Header {
        cfg: &ctx.cfg,
        namespace: ctx.namespace(),
        sub,
        module: true,
        doc: doc.to_string(),
    };
    let theorem = if sub == "Script" {
        "spec_script"
    } else {
        "spec_allin"
    };
    let mut text = lean::solution(&header, a, &chosen, theorem);
    if !prelude.is_empty() {
        let at = text
            .find("/-- The quoted body.")
            .context("solution layout")?;
        text.insert_str(at, &format!("{prelude}\n"));
    }
    Ok(Generated {
        text,
        residual,
        tactics,
        report,
    })
}

fn entry_name(ctx: &Ctx) -> &str {
    &ctx.cfg.entry
}

fn main() -> Result<()> {
    let cli = Cli::parse();
    ROOT.set(cli.root.clone()).ok();
    match cli.command {
        Cmd::Vcs { entry } => {
            let ctx = Ctx::load(&entry)?;
            let a = vc::analyse(&ctx.module, &ctx.cfg, None)?;
            let funs = ctx.cfg.lean_names();
            for v in &a.vcs {
                println!(
                    "-- {}\ntheorem {} {}\n",
                    v.name,
                    v.name,
                    lean::signature(v, &funs)
                );
                println!("{}", smt::script(v, &ctx.cfg, true));
            }
        }
        Cmd::Smt { entry, solver } => {
            let ctx = Ctx::load(&entry)?;
            let a = vc::analyse(&ctx.module, &ctx.cfg, None)?;
            let dir = ctx.work_dir()?;
            for s in &solver {
                for v in &a.vcs {
                    let o = smt::run(s, v, &ctx.cfg, &dir)?;
                    println!(
                        "{} {}: {} ({:.2}s) core {:?}",
                        o.solver, v.name, o.status, o.seconds, o.core
                    );
                    if o.status == "sat" {
                        println!("{}", o.model);
                    }
                }
            }
        }
        Cmd::Gen {
            entry,
            name,
            no_smt,
        } => {
            let ctx = Ctx::load(&entry)?;
            let a = vc::analyse(&ctx.module, &ctx.cfg, None)?;
            let rel = ctx
                .entry_dir
                .strip_prefix(&ctx.root)
                .unwrap_or(&ctx.entry_dir)
                .display()
                .to_string();
            let doc = format!(
                "# `{e}`, mode `tactic+script` (generated)\n\nGenerated by `tools/wasm-vc` {v} from `{rel}/{src}` and `{rel}/vc.toml`:\n`cargo run --manifest-path tools/wasm-vc/Cargo.toml -- gen {rel}`.\nDo not edit; regenerate. The verification conditions `vc_*` come from\nsymbolic execution of the annotated WAT by the script; each tactic was chosen\nby trying candidates in Lean (hints chosen by z3's unsat core). The proof of\n`{s}` replays the execution with the program-logic tactics and uses the\nconditions at its leaves. Solvers and script are untrusted: Lean checks all.",
                e = entry_name(&ctx),
                v = env!("CARGO_PKG_VERSION"),
                src = ctx.cfg.source,
                s = ctx.cfg.spec,
            );
            let g = generate(&ctx, &a, &name, &doc, !no_smt, &[], "")?;
            eprint!("{}", g.report);
            if !g.residual.is_empty() {
                bail!(
                    "{} condition(s) have no accepted tactic; try `wasm-vc agent`",
                    g.residual.len()
                );
            }
            let out = ctx
                .root
                .join("Silmaril/Proofs/WasmSpec")
                .join(&ctx.cfg.entry)
                .join(format!("{name}.lean"));
            std::fs::write(&out, &g.text)?;
            let (ok, text) = ctx.lean_with(&out, true)?;
            if !ok {
                bail!("the generated module does not compile:\n{text}");
            }
            println!("wrote {}", out.display());
        }
        Cmd::Agent(args) => agent::run(args)?,
        Cmd::Solve {
            problem,
            solver,
            timeout,
            json,
            out,
            unroll,
        } => {
            let work = std::env::temp_dir().join("wasm-vc-smt");
            let r = sym::problem::solve_file(
                &problem,
                &sym::problem::Opts {
                    solver,
                    timeout,
                    work,
                    unroll,
                },
            );
            let text = serde_json::to_string_pretty(&r)?;
            if let Some(o) = out {
                std::fs::write(o, &text)?;
            }
            if json {
                println!("{text}");
            } else {
                println!(
                    "{} ({}): {}  [{:.2}s, symex {:.2}s, {} steps, {} terms]",
                    r.problem,
                    r.kind,
                    r.verdict,
                    r.seconds,
                    r.symex_seconds,
                    r.symex_steps,
                    r.terms
                );
                if !r.error.is_empty() {
                    println!("  error: {}", r.error);
                }
                for g in &r.goals {
                    println!(
                        "  {:<24} {:?} {:.2}s ({} nodes){}",
                        g.name,
                        g.status,
                        g.seconds,
                        g.nodes,
                        if g.note.is_empty() {
                            String::new()
                        } else {
                            format!(" {}", g.note)
                        }
                    );
                    for (n, v) in &g.model {
                        println!("      {n} = {v}");
                    }
                }
                if !r.trust.is_empty() {
                    println!("  trust: {}", r.trust);
                }
            }
            if let Some(e) = &r.expect
                && e != &r.verdict
            {
                bail!("expected {e}, got {}", r.verdict);
            }
        }
        Cmd::Lean {
            problem,
            out,
            namespace,
            check,
        } => {
            let g = sym::leangen::generate(&problem, &namespace)?;
            let root = lake_root(&std::env::current_dir()?);
            let out = match out {
                Some(o) => o,
                None => {
                    let d = match &root {
                        Ok(r) => r.join("target/wasm-vc/lean"),
                        Err(e) => bail!("{e:#} (or pass --out)"),
                    };
                    std::fs::create_dir_all(&d)?;
                    d.join(format!("{}.lean", g.name))
                }
            };
            std::fs::write(&out, &g.lean)?;
            println!("wrote {}", out.display());
            if check {
                let root = root.context("--check needs a Lean project")?;
                let t = std::time::Instant::now();
                let o = Command::new("nice")
                    .args(["lake", "env", "lean"])
                    .arg(&out)
                    .current_dir(&root)
                    .output()?;
                let text = format!(
                    "{}{}",
                    String::from_utf8_lossy(&o.stdout),
                    String::from_utf8_lossy(&o.stderr)
                );
                println!(
                    "lean: {} ({:.1}s)",
                    if o.status.success() {
                        "checked"
                    } else {
                        "failed"
                    },
                    t.elapsed().as_secs_f64()
                );
                if !o.status.success() {
                    println!("{}", text.chars().take(4000).collect::<String>());
                    bail!("the generated module does not check");
                }
            }
        }
        Cmd::Dag {
            dag,
            jobs,
            timeout,
            unroll,
            out,
        } => {
            let (d, s) = sym::drive::drive_dag(
                &dag,
                &sym::drive::DriveOpts {
                    jobs,
                    solver: None,
                    timeout,
                    filter: None,
                    unroll,
                },
            )?;
            print!("{}", sym::drive::table(&s));
            let out = out.unwrap_or(dag);
            std::fs::write(&out, serde_json::to_string_pretty(&d)? + "\n")?;
            println!("wrote {}", out.display());
        }
        Cmd::Drive {
            dir,
            jobs,
            solver,
            timeout,
            filter,
            out,
            unroll,
        } => {
            let s = sym::drive::drive(
                &dir,
                &sym::drive::DriveOpts {
                    jobs,
                    solver,
                    timeout,
                    filter,
                    unroll,
                },
            )?;
            print!("{}", sym::drive::table(&s));
            if let Some(o) = out {
                std::fs::write(o, serde_json::to_string_pretty(&s)?)?;
            }
        }
        Cmd::Reflect {
            config,
            out,
            no_smt,
        } => reflect::run(&config, out, !no_smt)?,
    }
    Ok(())
}
