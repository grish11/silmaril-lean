//! The `all-in` loop: script + solvers + an AI model, every step checked.
//!
//! 1. If the loop has no usable invariant (or `--ignore-invariant`), ask the
//!    model for one (`INVARIANT:`/`DECREASES:` in SMT-LIB annotation syntax)
//!    and check its conditions with z3; a counterexample goes back into the
//!    next prompt.
//! 2. Generate the solution as in `gen`: candidate tactics (built-in, hinted
//!    unless `--ignore-hints`, and every tactic the model proposed so far) are
//!    tried in Lean; the conditions no candidate proves are *residual*.
//! 3. For each residual condition, ask the model for a tactic and optionally
//!    helper lemmas (`LEMMA:`/`TACTIC:` Lean blocks). Each lemma is checked by
//!    Lean on its own and kept only if it compiles; accepted lemmas become
//!    named declarations of the solution module, recorded with their round.
//! 4. Repeat until nothing is residual or the round budget is spent. Every
//!    prompt, answer and Lean verdict is appended to the attempt log.
//!
//! The final module is checked by Lean like any other; the model is untrusted.

use crate::sexp;
use crate::term::{B, Env, T};
use crate::{Ctx, generate, vc};
use anyhow::{Context, Result, bail};
use std::fmt::Write as _;
use std::path::PathBuf;
use std::process::Command;

#[derive(clap::Args)]
pub struct Args {
    entry: PathBuf,
    /// Model name passed to the agent command (`{model}`)
    #[arg(long)]
    model: String,
    /// Agent command (required; no default agent is assumed). `{model}`, `{root}` and `{out}`
    /// are substituted, the prompt is in `$WASM_VC_PROMPT`, and the command must write the
    /// model's answer to `{out}`. Run through `zsh -ic` so shell aliases resolve.
    #[arg(long)]
    agent_cmd: String,
    #[arg(long, default_value_t = 4)]
    rounds: u32,
    /// Do not use the `@invariant`/`@decreases` annotations
    #[arg(long)]
    ignore_invariant: bool,
    /// Do not use the Lean texts of `vc.toml` hints, nor its extra imports
    /// (the SMT axioms still define the spec functions for z3)
    #[arg(long)]
    ignore_hints: bool,
    /// Solution module name under `Silmaril/Proofs/WasmSpec/<Entry>/`
    #[arg(long, default_value = "AllIn")]
    name: String,
    /// Directory the model works in (`{root}`), e.g. a copy of the checkout
    /// without the entry's other solutions; Lean checks still run here
    #[arg(long)]
    agent_root: Option<PathBuf>,
}

struct Log {
    path: PathBuf,
    text: String,
}

impl Log {
    fn add(&mut self, s: &str) -> Result<()> {
        self.text.push_str(s);
        self.text.push('\n');
        std::fs::write(&self.path, &self.text)?;
        Ok(())
    }
}

fn ask(ctx: &Ctx, args: &Args, prompt: &str, tag: &str) -> Result<String> {
    let dir = ctx.work_dir()?;
    let out = dir.join(format!("answer-{tag}.md"));
    let _ = std::fs::remove_file(&out);
    let cmd = args
        .agent_cmd
        .replace("{model}", &args.model)
        .replace("{out}", &out.display().to_string())
        .replace(
            "{root}",
            &args
                .agent_root
                .as_ref()
                .unwrap_or(&ctx.root)
                .display()
                .to_string(),
        );
    let status = Command::new("zsh")
        .args(["-ic", &cmd])
        .env("WASM_VC_PROMPT", prompt)
        .current_dir(args.agent_root.as_ref().unwrap_or(&ctx.root))
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null())
        .status()
        .context("could not run the agent command")?;
    if !status.success() {
        bail!("the agent command failed ({status})");
    }
    std::fs::read_to_string(&out).context("the agent wrote no answer")
}

/// The fenced code block after `marker` (or the rest of its line).
fn section(answer: &str, marker: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut rest = answer;
    while let Some(i) = rest.find(marker) {
        let after = &rest[i + marker.len()..];
        let line_end = after.find('\n').unwrap_or(after.len());
        let inline = after[..line_end].trim();
        if !inline.is_empty() && !inline.starts_with("```") {
            out.push(inline.to_string());
            rest = &after[line_end..];
            continue;
        }
        let Some(open) = after.find("```") else { break };
        let body = &after[open + 3..];
        let body = &body[body.find('\n').map_or(0, |n| n + 1)..];
        let Some(close) = body.find("```") else { break };
        out.push(body[..close].trim_end().to_string());
        rest = &body[close..];
    }
    out
}

fn lemma_name(code: &str) -> Option<String> {
    let t = code.split_whitespace().collect::<Vec<_>>();
    t.windows(2)
        .find(|w| w[0] == "theorem" || w[0] == "lemma")
        .map(|w| w[1].to_string())
}

pub fn run(args: Args) -> Result<()> {
    let ctx = Ctx::load(&args.entry)?;
    let ent = ctx.cfg.entry.clone();
    let agentic = ctx.entry_dir.join("agentic");
    std::fs::create_dir_all(&agentic)?;
    let mut log = Log {
        path: agentic.join("log.md"),
        text: String::new(),
    };
    let mut cfg = ctx.cfg.clone();
    if args.ignore_hints {
        for h in &mut cfg.hint {
            h.lean = String::new();
        }
        // Lemma modules named for the hints are not imported either: the
        // model has to supply (and Lean to accept) every lemma it needs.
        cfg.imports.clear();
    }
    let src = std::fs::read_to_string(ctx.entry_dir.join(&ctx.cfg.source))?;
    let shown: String = if args.ignore_invariant {
        src.lines()
            .filter(|l| !l.contains("@invariant") && !l.contains("@decreases"))
            .collect::<Vec<_>>()
            .join("\n")
    } else {
        src.clone()
    };
    let defs = std::fs::read_to_string(
        ctx.root
            .join("Silmaril/WasmSpec")
            .join(&ent)
            .join("Defs.lean"),
    )?;
    log.add(&format!(
        "# Agentic log: `{ent}`, solution `{}`\n\nModel `{}` via `{}`; up to {} rounds; ignore invariant: {}; ignore hints: {}; model working directory: {}.\nGenerated by `tools/wasm-vc agent` {}. Every proposal below was checked by z3 (invariants) or Lean (lemmas, tactics); only accepted ones reach the solution module.\n",
        args.name,
        args.model,
        args.agent_cmd,
        args.rounds,
        args.ignore_invariant,
        args.ignore_hints,
        match &args.agent_root {
            Some(_) => "a copy of the checkout without this entry's other solutions and lemma files (blind)",
            None => "this checkout (other solutions visible)",
        },
        env!("CARGO_PKG_VERSION"),
    ))?;
    let ctx = Ctx { cfg, ..ctx };
    let funs = ctx.cfg.funs();
    let lenv = Env {
        funs: &funs,
        result: false,
    };
    let mut invariant: Option<(B, T, String)> = None;
    let mut inv_feedback = String::new();
    let mut extra: Vec<Vec<String>> = Vec::new();
    let mut prelude = String::new();
    let mut accepted: Vec<(String, u32)> = Vec::new();
    let mut vc_feedback: Vec<String> = Vec::new();
    let needs_inv = |inv: &Option<(B, T, String)>| -> Result<bool> {
        if inv.is_some() {
            return Ok(false);
        }
        if args.ignore_invariant {
            // Does the program have a loop at all?
            return Ok(
                vc::analyse(&ctx.module, &ctx.cfg, Some((B::True, T::Lit(0))))
                    .is_ok_and(|a| matches!(a.shape, vc::Shape::Loop { .. })),
            );
        }
        Ok(false)
    };
    for round in 1..=args.rounds {
        log.add(&format!("\n## Round {round}\n"))?;
        if needs_inv(&invariant)? {
            let prompt = format!(
                "You are helping verify a WebAssembly function in Lean. Propose a loop invariant and a decreasing measure for the loop of ${f} in this WAT (annotations are SMT-LIB terms over i32 bit-vectors; local names denote their current values in the loop, (old x) the initial value of parameter x; spec functions: {funs:?}, see the Lean definitions below).\n\n```wat\n{shown}\n```\n\nLean definitions:\n```lean\n{defs}\n```\n{inv_feedback}\nAnswer with exactly two lines:\nINVARIANT: <SMT-LIB term>\nDECREASES: <SMT-LIB bit-vector term, read unsigned>\n",
                f = ctx.cfg.func,
                funs = funs.keys().collect::<Vec<_>>(),
            );
            log.add(&format!("### Invariant prompt\n\n```text\n{prompt}\n```\n"))?;
            let answer = ask(&ctx, &args, &prompt, &format!("r{round}-inv"))?;
            log.add(&format!(
                "### Answer ({})\n\n```text\n{}\n```\n",
                args.model,
                answer.trim()
            ))?;
            let inv_s = section(&answer, "INVARIANT:");
            let dec_s = section(&answer, "DECREASES:");
            let parsed = (|| -> Result<(B, T, String)> {
                let i = inv_s.first().context("no INVARIANT line")?;
                let d = dec_s.first().context("no DECREASES line")?;
                Ok((
                    B::from_sexp(&sexp::parse(i)?, &lenv)?,
                    T::from_sexp(&sexp::parse(d)?, &lenv)?,
                    format!(";; @invariant {i}\n;; @decreases {d}"),
                ))
            })();
            match parsed {
                Err(e) => {
                    inv_feedback = format!("\nYour previous answer could not be read: {e}\n");
                    log.add(&format!("Rejected: {e}\n"))?;
                    continue;
                }
                Ok((b, t, text)) => {
                    let a = vc::analyse(&ctx.module, &ctx.cfg, Some((b.clone(), t.clone())))?;
                    let dir = ctx.work_dir()?;
                    let mut bad = String::new();
                    for v in &a.vcs {
                        let o = crate::smt::run("z3", v, &ctx.cfg, &dir)?;
                        log.add(&format!(
                            "- z3 on {}: {} ({:.2}s)",
                            v.name, o.status, o.seconds
                        ))?;
                        if o.status != "unsat" {
                            write!(
                                bad,
                                "\n{} is not valid (z3: {}):\n{}\n",
                                v.name, o.status, o.model
                            )
                            .unwrap();
                        }
                    }
                    if bad.is_empty() {
                        log.add(&format!("\nAccepted invariant:\n```text\n{text}\n```\n"))?;
                        invariant = Some((b, t, text));
                    } else {
                        inv_feedback = format!("\nYour previous proposal\n{text}\nfailed:{bad}\n");
                        log.add(&format!("Rejected:{bad}"))?;
                        continue;
                    }
                }
            }
        }
        let a = vc::analyse(
            &ctx.module,
            &ctx.cfg,
            invariant.as_ref().map(|(b, t, _)| (b.clone(), t.clone())),
        )?;
        if extra.len() < a.vcs.len() {
            extra.resize(a.vcs.len(), Vec::new());
            vc_feedback.resize(a.vcs.len(), String::new());
        }
        let doc = doc_text(&ctx, &args, invariant.as_ref().map(|x| x.2.as_str()));
        let g = generate(&ctx, &a, &args.name, &doc, true, &extra, &prelude)?;
        log.add(&format!(
            "### Script and Lean\n\n```text\n{}```\n",
            g.report
        ))?;
        if g.residual.is_empty() {
            let out = ctx
                .root
                .join("Silmaril/Proofs/WasmSpec")
                .join(&ent)
                .join(format!("{}.lean", args.name));
            std::fs::write(&out, &g.text)?;
            let (ok, text) = ctx.lean_with(&out, true)?;
            if !ok {
                bail!("the assembled module does not compile:\n{text}");
            }
            let lemmas: Vec<String> = accepted
                .iter()
                .map(|(n, r)| format!("{n} (round {r})"))
                .collect();
            log.add(&format!(
                "\n## Result\n\nNo residual conditions after round {round}. Wrote `{}`; accepted lemmas: {}.\n",
                out.strip_prefix(&ctx.root).unwrap_or(&out).display(),
                if lemmas.is_empty() { "none".into() } else { lemmas.join(", ") }
            ))?;
            println!("wrote {} after {round} round(s)", out.display());
            return Ok(());
        }
        let funs_l = ctx.cfg.lean_names();
        for &i in &g.residual {
            let v = &a.vcs[i];
            let stmt = format!("theorem {} {}", v.name, crate::lean::signature(v, &funs_l));
            let prompt = format!(
                "You are proving a verification condition in Lean 4 (use the repository lean-toolchain, Mathlib available) for the Wasm spec library entry `{ent}` of this repository (you may read files and run `lake env lean <file>` to test; do not write into the repository). The condition, in namespace `{ns}.{sub}` with `open Silmaril.WasmSpec {ns}`:\n\n```lean\n{stmt} := by\n  sorry\n```\n\nThe entry's definitions (`Silmaril/WasmSpec/{ent}/Defs.lean`):\n```lean\n{defs}\n```\nHelper lemmas already accepted:\n```lean\n{prelude}\n```\n{fb}\nAnswer with optional helper lemmas, each in a block after a line `LEMMA:` (a complete `theorem name ... := by ...` using only Lean core/Std tactics and these definitions), followed by the proof of the condition after a line `TACTIC:` (a fenced block with the tactic script only, no `by`). Hypotheses are named `hc` (branch condition) and `hi` (invariant).",
                ns = ctx.namespace(),
                sub = args.name,
                fb = vc_feedback[i],
            );
            log.add(&format!(
                "### Residual `{}`\n\n```lean\n{stmt}\n```\n",
                v.name
            ))?;
            let answer = match ask(&ctx, &args, &prompt, &format!("r{round}-{}", v.name)) {
                Ok(a) => a,
                Err(e) => {
                    log.add(&format!("Agent error: {e}\n"))?;
                    continue;
                }
            };
            log.add(&format!(
                "Answer ({}):\n\n```text\n{}\n```\n",
                args.model,
                answer.trim()
            ))?;
            let mut fb = String::new();
            for lem in section(&answer, "LEMMA:") {
                let Some(name) = lemma_name(&lem) else {
                    log.add("- lemma without a theorem name: skipped")?;
                    continue;
                };
                let candidate = format!(
                    "{prelude}\n/-- Proposed by `{}` in round {round} for `{}`; checked by Lean. -/\n{lem}\n",
                    args.model, v.name
                );
                let ok = check_prelude(&ctx, &args.name, &candidate)?;
                match ok {
                    Ok(()) => {
                        log.add(&format!("- lemma `{name}`: **accepted** by Lean"))?;
                        prelude = candidate;
                        accepted.push((name, round));
                    }
                    Err(err) => {
                        log.add(&format!(
                            "- lemma `{name}`: rejected by Lean:\n```text\n{err}\n```"
                        ))?;
                        write!(fb, "\nYour lemma `{name}` failed in Lean:\n{err}\n").unwrap();
                    }
                }
            }
            for t in section(&answer, "TACTIC:") {
                log.add(&format!(
                    "- tactic proposed for `{}` (tried next round):\n```lean\n{t}\n```",
                    v.name
                ))?;
                let t = t
                    .lines()
                    .map(|l| l.to_string())
                    .collect::<Vec<_>>()
                    .join("\n  ");
                extra[i].insert(0, t);
            }
            if !fb.is_empty() {
                vc_feedback[i] = fb;
            } else {
                vc_feedback[i] = "\nYour previous tactic was not accepted by Lean (it is retried with the lemmas accepted so far).\n".into();
            }
        }
    }
    log.add("\n## Result\n\nRound budget spent with residual conditions; no module written.\n")?;
    bail!(
        "residual conditions remain after {} rounds; see {}",
        args.rounds,
        log.path.display()
    )
}

/// Check that the accepted helper lemmas compile in the solution's context.
fn check_prelude(ctx: &Ctx, sub: &str, prelude: &str) -> Result<Result<(), String>> {
    let header = crate::lean::Header {
        cfg: &ctx.cfg,
        namespace: ctx.namespace(),
        sub,
        module: false,
        doc: "Lemma check (generated, not kept).".into(),
    };
    let text = format!(
        "{}{prelude}\nend {}.{sub}\n",
        crate::lean::header(&header),
        ctx.namespace()
    );
    let file = ctx.work_dir()?.join(format!("{sub}Lemmas.lean"));
    std::fs::write(&file, text)?;
    let (ok, out) = ctx.lean(&file)?;
    let errs = crate::error_lines(&out, &file);
    Ok(
        if ok && errs.is_empty() && !out.contains("declaration uses `sorry`") {
            Ok(())
        } else {
            Err(out.lines().take(30).collect::<Vec<_>>().join("\n"))
        },
    )
}

fn doc_text(ctx: &Ctx, args: &Args, inv: Option<&str>) -> String {
    let rel = ctx
        .entry_dir
        .strip_prefix(&ctx.root)
        .unwrap_or(&ctx.entry_dir)
        .display()
        .to_string();
    format!(
        "# `{e}`, mode `all-in` (generated)\n\nGenerated by `tools/wasm-vc agent` {v}:\n`cargo run --manifest-path tools/wasm-vc/Cargo.toml -- agent {rel} --model {m}{ii}{ih}{ar}`.\nThe script derives the verification conditions `vc_*` from the annotated WAT\n(`{rel}/{src}`){invs}; z3 checks them; candidate tactics and the\nlemmas and tactics proposed by `{m}` are checked by Lean, and only accepted\nones appear here. The attempt log is `{rel}/agentic/log.md`. The model,\nscript and solvers are untrusted: Lean checks everything below.",
        e = ctx.cfg.entry,
        ar = if args.agent_root.is_some() {
            " --agent-root <blind copy>"
        } else {
            ""
        },
        v = env!("CARGO_PKG_VERSION"),
        m = args.model,
        ii = if args.ignore_invariant {
            " --ignore-invariant"
        } else {
            ""
        },
        ih = if args.ignore_hints {
            " --ignore-hints"
        } else {
            ""
        },
        src = ctx.cfg.source,
        invs = match inv {
            Some(t) => format!(
                " and the loop invariant the model proposed and z3 checked\n(`{}`)",
                t.replace('\n', "`, `")
            ),
            None => String::new(),
        },
    )
}
