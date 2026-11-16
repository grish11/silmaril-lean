//! Parallel driver: solve a directory of Wasm problems with bounded
//! concurrency. Each problem runs as its own `wasm-vc solve` process (one
//! solver process at a time inside it), so at most `jobs` solvers run at once.
//! Problems may name `deps`; they are started after their dependencies, and a
//! problem's *closed* verdict is `proved` only when it and all its transitive
//! dependencies are proved (assume-guarantee composition is recorded by the
//! producer of the problems, not checked here).

use super::problem::{self, Report};
use anyhow::{Context, Result, bail};
use serde::Serialize;
use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Stdio};
use std::time::{Duration, Instant};

#[derive(Serialize)]
pub struct Entry {
    pub file: String,
    pub report: Report,
    /// Verdict including dependencies.
    pub closed: String,
    pub deps: Vec<String>,
}

#[derive(Serialize)]
pub struct Summary {
    pub dir: String,
    pub jobs: usize,
    pub wall_seconds: f64,
    pub cpu_seconds: f64,
    pub counts: BTreeMap<String, usize>,
    pub problems: Vec<Entry>,
}

fn find(dir: &Path, out: &mut Vec<PathBuf>) -> Result<()> {
    let mut items: Vec<_> = std::fs::read_dir(dir)?.collect::<Result<_, _>>()?;
    items.sort_by_key(|e| e.path());
    for e in items {
        let p = e.path();
        if p.is_dir() {
            find(&p, out)?;
        } else if p.extension().is_some_and(|x| x == "wat") {
            // annotated WAT problems (reductions)
            if let Ok(t) = std::fs::read_to_string(&p)
                && t.lines().any(|l| l.trim_start().starts_with(";; @ensures"))
            {
                out.push(p);
            }
        } else if p.extension().is_some_and(|x| x == "toml") {
            // only problem files (with a `kind`)
            if let Ok(t) = std::fs::read_to_string(&p)
                && let Ok(v) = t.parse::<toml::Table>()
                && v.contains_key("kind")
            {
                out.push(p);
            }
        }
    }
    Ok(())
}

pub struct DriveOpts {
    pub jobs: usize,
    pub solver: Option<String>,
    pub timeout: Option<u64>,
    pub filter: Option<String>,
    pub unroll: Option<u32>,
}

pub fn drive(dir: &Path, o: &DriveOpts) -> Result<Summary> {
    let mut files = Vec::new();
    find(dir, &mut files)?;
    drive_files(dir, files, o)
}

pub fn drive_files(dir: &Path, mut files: Vec<PathBuf>, o: &DriveOpts) -> Result<Summary> {
    if o.jobs == 0 {
        bail!("jobs must be positive");
    }
    if let Some(f) = &o.filter {
        files.retain(|p| p.to_string_lossy().contains(f.as_str()));
    }
    let mut probs = Vec::new();
    for f in &files {
        // a problem that does not load is still run (and reported as an error)
        let (name, deps) = match problem::load(f) {
            Ok(p) => (p.name.clone().unwrap_or_default(), p.deps.clone()),
            Err(_) => (f.display().to_string(), vec![]),
        };
        probs.push((f.clone(), name, deps));
    }
    let names: BTreeSet<String> = probs.iter().map(|p| p.1.clone()).collect();
    let exe = std::env::current_exe()?;
    let start = Instant::now();
    let mut done: BTreeMap<usize, Report> = BTreeMap::new();
    let done_name = |done: &BTreeMap<usize, Report>, n: &str| {
        probs
            .iter()
            .enumerate()
            .any(|(i, p)| p.1 == n && done.contains_key(&i))
    };
    let mut started: BTreeSet<usize> = BTreeSet::new();
    let mut running: Vec<(usize, Child, PathBuf)> = Vec::new();
    let tmp = std::env::temp_dir().join(format!("wasm-vc-drive-{}", std::process::id()));
    std::fs::create_dir_all(&tmp)?;
    loop {
        // start ready problems
        while running.len() < o.jobs {
            let ready = (0..probs.len()).find(|&i| {
                !started.contains(&i)
                    && probs[i]
                        .2
                        .iter()
                        .all(|d| !names.contains(d) || done_name(&done, d))
            });
            let Some(i) = ready else { break };
            started.insert(i);
            let out = tmp.join(format!("{i}.json"));
            let mut cmd = Command::new(&exe);
            cmd.arg("solve")
                .arg(&probs[i].0)
                .arg("--json")
                .arg("--out")
                .arg(&out);
            if let Some(s) = &o.solver {
                cmd.arg("--solver").arg(s);
            }
            if let Some(t) = o.timeout {
                cmd.arg("--timeout").arg(t.to_string());
            }
            if let Some(u) = o.unroll {
                cmd.arg("--unroll").arg(u.to_string());
            }
            let child = cmd
                .stdout(Stdio::null())
                .stderr(Stdio::null())
                .spawn()
                .context("spawning wasm-vc solve")?;
            eprintln!("[drive] start {}", probs[i].1);
            running.push((i, child, out));
        }
        if running.is_empty() {
            if started.len() < probs.len() {
                bail!("dependency cycle or missing dependency among the problems");
            }
            break;
        }
        std::thread::sleep(Duration::from_millis(50));
        let mut k = 0;
        while k < running.len() {
            if running[k].1.try_wait()?.is_some() {
                let (i, _, out) = running.remove(k);
                let rep: Report = match std::fs::read_to_string(&out)
                    .ok()
                    .and_then(|t| serde_json::from_str::<serde_json::Value>(&t).ok())
                {
                    Some(v) => report_from_json(&v),
                    None => problem::solve_file(
                        &probs[i].0,
                        &problem::Opts {
                            solver: o.solver.clone(),
                            timeout: o.timeout,
                            work: tmp.clone(),
                            unroll: o.unroll,
                        },
                    ),
                };
                eprintln!(
                    "[drive] {} {} ({:.2}s)",
                    probs[i].1, rep.verdict, rep.seconds
                );
                done.insert(i, rep);
            } else {
                k += 1;
            }
        }
    }
    let wall = start.elapsed().as_secs_f64();
    // closed verdicts
    let mut entries = Vec::new();
    let mut counts = BTreeMap::new();
    let mut cpu = 0.0;
    for (i, (f, _n, deps)) in probs.iter().enumerate() {
        let mut rep = done.remove(&i).unwrap();
        rep.problem = f
            .strip_prefix(dir)
            .unwrap_or(f)
            .with_extension("")
            .display()
            .to_string();
        cpu += rep.seconds;
        let mut closed = rep.verdict.clone();
        let mut stack = deps.clone();
        let mut seen = BTreeSet::new();
        while let Some(d) = stack.pop() {
            if !seen.insert(d.clone()) {
                continue;
            }
            match probs.iter().find(|p| p.1 == d) {
                None => closed = "open-dependency".into(),
                Some(p) => {
                    stack.extend(p.2.clone());
                }
            }
        }
        *counts.entry(rep.verdict.clone()).or_insert(0) += 1;
        entries.push(Entry {
            file: f.strip_prefix(dir).unwrap_or(f).display().to_string(),
            report: rep,
            closed,
            deps: deps.clone(),
        });
    }
    // closed: proved only if all transitive deps are proved
    let verdicts: BTreeMap<String, String> = entries
        .iter()
        .map(|e| (e.report.problem.clone(), e.report.verdict.clone()))
        .collect();
    for e in &mut entries {
        if e.closed == "proved" {
            let mut stack = e.deps.clone();
            let mut seen = BTreeSet::new();
            while let Some(d) = stack.pop() {
                if !seen.insert(d.clone()) {
                    continue;
                }
                if verdicts.get(&d).map(String::as_str) != Some("proved") {
                    e.closed = format!(
                        "depends on {d} ({})",
                        verdicts.get(&d).cloned().unwrap_or_default()
                    );
                    break;
                }
                if let Some(p) = probs.iter().find(|p| p.1 == d) {
                    stack.extend(p.2.clone());
                }
            }
        }
    }
    let _ = std::fs::remove_dir_all(&tmp);
    Ok(Summary {
        dir: dir.display().to_string(),
        jobs: o.jobs,
        wall_seconds: wall,
        cpu_seconds: cpu,
        counts,
        problems: entries,
    })
}

fn report_from_json(v: &serde_json::Value) -> Report {
    let s = |k: &str| v.get(k).and_then(|x| x.as_str()).unwrap_or("").to_string();
    let f = |k: &str| v.get(k).and_then(|x| x.as_f64()).unwrap_or(0.0);
    let goals = v
        .get("goals")
        .and_then(|g| g.as_array())
        .map(|a| {
            a.iter()
                .map(|g| super::solve::Answer {
                    name: g.get("name").and_then(|x| x.as_str()).unwrap_or("").into(),
                    status: match g.get("status").and_then(|x| x.as_str()) {
                        Some("proved") => super::solve::Status::Proved,
                        Some("refuted") => super::solve::Status::Refuted,
                        _ => super::solve::Status::Unknown,
                    },
                    solver: g
                        .get("solver")
                        .and_then(|x| x.as_str())
                        .unwrap_or("")
                        .into(),
                    seconds: g.get("seconds").and_then(|x| x.as_f64()).unwrap_or(0.0),
                    model: g
                        .get("model")
                        .and_then(|m| m.as_array())
                        .map(|m| {
                            m.iter()
                                .filter_map(|p| {
                                    let p = p.as_array()?;
                                    Some((p.first()?.as_str()?.into(), p.get(1)?.as_str()?.into()))
                                })
                                .collect()
                        })
                        .unwrap_or_default(),
                    note: g.get("note").and_then(|x| x.as_str()).unwrap_or("").into(),
                    nodes: g.get("nodes").and_then(|x| x.as_u64()).unwrap_or(0) as usize,
                    bytes: g.get("bytes").and_then(|x| x.as_u64()).unwrap_or(0) as usize,
                })
                .collect()
        })
        .unwrap_or_default();
    Report {
        problem: s("problem"),
        kind: s("kind"),
        verdict: s("verdict"),
        trust: s("trust"),
        seconds: f("seconds"),
        symex_seconds: f("symex_seconds"),
        symex_steps: v.get("symex_steps").and_then(|x| x.as_u64()).unwrap_or(0),
        terms: v.get("terms").and_then(|x| x.as_u64()).unwrap_or(0) as usize,
        goals,
        expect: v.get("expect").and_then(|x| x.as_str()).map(String::from),
        error: s("error"),
    }
}

/// A plain-text table of a summary.
pub fn table(s: &Summary) -> String {
    let mut out = format!(
        "{:<40} {:<7} {:<9} {:>8} {:>8}  {}\n",
        "problem", "kind", "verdict", "seconds", "terms", "closed / note"
    );
    for e in &s.problems {
        let r = &e.report;
        let mut note = if e.closed != r.verdict {
            e.closed.clone()
        } else {
            String::new()
        };
        if let Some(x) = &r.expect
            && x != &r.verdict
        {
            note = format!("{note} EXPECTED {x}");
        }
        if !r.error.is_empty() {
            note = format!("{note} {}", r.error.lines().next().unwrap_or(""));
        }
        out.push_str(&format!(
            "{:<40} {:<7} {:<9} {:>8.2} {:>8}  {}\n",
            r.problem,
            r.kind,
            r.verdict,
            r.seconds,
            r.terms,
            note.trim()
        ));
    }
    out.push_str(&format!(
        "{} problems, jobs {}, wall {:.2}s, sum of problem times {:.2}s, {:?}\n",
        s.problems.len(),
        s.jobs,
        s.wall_seconds,
        s.cpu_seconds,
        s.counts
    ));
    out
}

/// Solve the Wasm leaves of a `silmaril.wasm-sim.dag.v0` DAG (nodes of kind
/// `wasm-piece`/`wasm-problem` whose `files` name an annotated `.wat`) and
/// return the DAG with verdicts written back. Evidence is recorded in a node
/// field `evidence` (`{kind: smt|bounded|lean, tool, verdict, seconds, trust,
/// goals}`); the node `status` keeps the schema's meaning (`solved` needs a
/// Lean theorem): SMT proofs and bounded checks give `tested`, SMT
/// counterexamples (genuine refutations, `problem::solve`) give `refuted`
/// with `refutation` naming the countermodel.
pub fn drive_dag(dag_path: &Path, o: &DriveOpts) -> Result<(serde_json::Value, Summary)> {
    let mut dag: serde_json::Value = serde_json::from_str(&std::fs::read_to_string(dag_path)?)?;
    if dag.get("schema").and_then(|s| s.as_str()) != Some("silmaril.wasm-sim.dag.v0") {
        bail!("not a silmaril.wasm-sim.dag.v0 DAG");
    }
    let base = dag_path.parent().unwrap_or(Path::new(".")).to_path_buf();
    let mut leaves: Vec<(usize, PathBuf)> = Vec::new();
    if let Some(nodes) = dag.get("nodes").and_then(|n| n.as_array()) {
        for (i, n) in nodes.iter().enumerate() {
            let kind = n.get("kind").and_then(|k| k.as_str()).unwrap_or("");
            if kind != "wasm-piece" && kind != "wasm-problem" {
                continue;
            }
            let wat = n.get("files").and_then(|f| f.as_array()).and_then(|fs| {
                fs.iter()
                    .filter_map(|f| f.as_str())
                    .find(|f| f.ends_with(".wat"))
            });
            if let Some(w) = wat {
                let p = base.join(w);
                if p.is_file() {
                    leaves.push((i, p));
                }
            }
        }
    }
    let files: Vec<PathBuf> = leaves.iter().map(|l| l.1.clone()).collect();
    let summary = drive_files(&base, files, o)?;
    let nodes = dag.get_mut("nodes").and_then(|n| n.as_array_mut()).unwrap();
    for ((i, _), e) in leaves.iter().zip(&summary.problems) {
        let r = &e.report;
        let node = nodes[*i].as_object_mut().unwrap();
        let kind = match r.verdict.as_str() {
            "proved" => "smt",
            "bounded" => "bounded",
            _ => "none",
        };
        let goals: Vec<serde_json::Value> = r
            .goals
            .iter()
            .map(|g| serde_json::json!({"goal": g.name, "status": g.status, "seconds": g.seconds}))
            .collect();
        node.insert(
            "evidence".into(),
            serde_json::json!({
                "kind": kind,
                "tool": format!("wasm-vc {}", env!("CARGO_PKG_VERSION")),
                "verdict": r.verdict,
                "seconds": r.seconds,
                "trust": r.trust,
                "goals": goals,
                "error": r.error,
            }),
        );
        let cur = node
            .get("status")
            .and_then(|s| s.as_str())
            .unwrap_or("open")
            .to_string();
        if cur == "solved" {
            continue; // a Lean solution is stronger; keep it
        }
        match r.verdict.as_str() {
            "proved" | "bounded" => {
                node.insert("status".into(), "tested".into());
            }
            "refuted" => {
                let g = r
                    .goals
                    .iter()
                    .find(|g| g.status == super::solve::Status::Refuted);
                let model: Vec<String> = g
                    .map(|g| g.model.iter().map(|(n, v)| format!("{n}={v}")).collect())
                    .unwrap_or_default();
                node.insert("status".into(), "refuted".into());
                node.insert(
                    "refutation".into(),
                    format!(
                        "wasm-vc SMT countermodel (not a Lean theorem) for goal `{}`: {}",
                        g.map(|g| g.name.as_str()).unwrap_or("?"),
                        model.join(" ")
                    )
                    .into(),
                );
            }
            _ => {}
        }
    }
    Ok((dag, summary))
}
