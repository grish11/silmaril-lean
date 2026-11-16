//! `wasm-sim reduce`: an x86-64 problem (a reduction plan, `silmaril.wasm-sim.reduce.v0`) posed as
//! a DAG of small Wasm problems (`docs/projects/wasm-sim-reduction.md`).;
//! the translation is the canonical one (`problem::split`, `pcalls`).
//!
//! Output directory: `sim.wat` (the shared simulator), `modules/<f>.wat` (one P-calls module per
//! function, callees imported), `pieces/<f>.json` (`silmaril.wasm-sim.piece.v0`), `link.json`,
//! `dag.json` (`silmaril.wasm-sim.dag.v0`), and with `--lean DIR` one Wasm spec library entry per
//! function with a `lean_spec` (status `stated`). `--run` links the modules to the simulator and
//! runs the plan's test vectors (compared with `--native EXE` when given).
//!
//! The ELF's `.text` is placed at `CODE_BASE` (the translator's base; the code must be position
//! independent, as the `FnCorrectDet` problems quantify over placements anyway).

use super::difftest::CODE_BASE;
use super::pcalls::decode_all;
use super::problem::{self, Contract, piece_json, split, split_sim};
use crate::harness::{self, Host, PageMem, SENTINEL, Sim};
use crate::reduce::{dag, elf::Elf, insn, plan};
use anyhow::{Context, Result, anyhow, bail};
use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use wasmtime::{Linker, Module, Store};

#[derive(clap::Args)]
pub struct Args {
    /// the reduction plan (`silmaril.wasm-sim.reduce.v0`)
    plan: PathBuf,
    /// output directory
    #[arg(long, short)]
    out: PathBuf,
    /// run the plan's test vectors on the linked modules
    #[arg(long)]
    run: bool,
    /// native executable printing the root's result for the arguments (with --run)
    #[arg(long)]
    native: Option<PathBuf>,
    /// method granularity: `form` (the parametric method API, default) or `insn` (one certified
    /// full step method per instruction, for straight-line leaf functions in the G fragment;
    /// writes `insn/<f>.wat`, difftested against the P-mem simulator with --run)
    #[arg(long, default_value = "form")]
    granularity: String,
}

const GPRS: [&str; 16] = [
    "rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi", "r8", "r9", "r10", "r11", "r12", "r13",
    "r14", "r15",
];
const STACK_TOP: u64 = problem::WINDOW + 0x9008;

fn write(p: &Path, s: &str) -> Result<()> {
    if let Some(d) = p.parent() {
        std::fs::create_dir_all(d)?;
    }
    std::fs::write(p, s).with_context(|| format!("writing {}", p.display()))
}

/// Loop heads: targets of backward branches.
fn loop_heads(f: &super::pcalls::Func) -> BTreeSet<u64> {
    f.insns
        .iter()
        .filter(|(a, i)| {
            matches!(
                i.flow_control(),
                iced_x86::FlowControl::ConditionalBranch
                    | iced_x86::FlowControl::UnconditionalBranch
            ) && i.near_branch_target() <= **a
        })
        .map(|(_, i)| i.near_branch_target())
        .collect()
}

pub fn main(a: Args) -> Result<()> {
    let p = plan::read(&a.plan)?;
    let base = a.plan.parent().unwrap_or(Path::new("."));
    let elf_bytes = std::fs::read(base.join(&p.artifact.elf))?;
    let elf_sha = {
        use std::hash::{Hash, Hasher};
        let mut h = std::collections::hash_map::DefaultHasher::new();
        elf_bytes.hash(&mut h);
        format!("{:016x}", h.finish())
    };
    let elf = Elf::parse(elf_bytes)?;
    let (text_addr, text) = elf.text()?;
    let text = text.to_vec();
    let syms: BTreeMap<String, u64> = elf
        .symbols
        .iter()
        .filter(|s| s.is_func && s.value >= text_addr && s.value < text_addr + text.len() as u64)
        .map(|s| (s.name.clone(), s.value - text_addr))
        .collect();
    let contracts: Vec<Contract> = p
        .functions
        .iter()
        .map(|f| Contract {
            name: f.name.clone(),
            source: p.artifact.elf.clone(),
            requires: f.requires.clone(),
            ensures: f.ensures.clone(),
            footprint: vec![],
            frame: super::problem::STACK_FRAME,
        })
        .collect();
    let by_name: BTreeMap<String, &Contract> =
        contracts.iter().map(|c| (c.name.clone(), c)).collect();
    let engine = harness::engine();
    let sim_text = split_sim()?;
    let sim_m = Module::new(&engine, &sim_text).map_err(|e| anyhow!("{e:?}"))?;
    let root_off = *syms
        .get(&p.root)
        .with_context(|| format!("no function symbol {}", p.root))?;
    let entry = CODE_BASE + root_off;
    let sp = split(entry, &text, &syms, &by_name, &p.defs, &sim_m)?;
    let funcs = decode_all(&text, CODE_BASE, &[entry])?;
    write(&a.out.join("sim.wat"), &sim_text)?;
    let mut modules: BTreeMap<String, (u64, String, Vec<String>, Vec<String>)> = BTreeMap::new();
    for (n, addr, t, sim, callees) in &sp.modules {
        write(&a.out.join(format!("modules/{n}.wat")), t)?;
        let f = funcs
            .iter()
            .find(|f| f.entry == *addr)
            .context("decoded function")?;
        let lo = (f.entry - CODE_BASE) as usize;
        let hi = f
            .insns
            .iter()
            .next_back()
            .map(|(a, i)| (a - CODE_BASE) as usize + i.len())
            .unwrap_or(lo);
        let mut pj = piece_json(
            n,
            *addr,
            &text[lo..hi],
            sim,
            callees,
            by_name.get(n).copied(),
            &by_name,
        );
        pj["id"] = serde_json::json!(format!("{}/ag/{n}", p.id));
        pj["program"]["source"] = serde_json::json!(format!("../modules/{n}.wat"));
        write(
            &a.out.join(format!("pieces/{n}.json")),
            &serde_json::to_string_pretty(&pj)?,
        )?;
        modules.insert(n.clone(), (*addr, t.clone(), sim.clone(), callees.clone()));
    }
    write(
        &a.out.join("link.json"),
        &serde_json::to_string_pretty(&serde_json::json!({
            "schema": "silmaril.wasm-sim.link.v0", "sim": "sim.wat", "order": sp.order, "root": p.root,
            "modules": "modules/<f>.wat", "env": ["mem.load8..64/store8..64", "sys.syscall", "nd.undef"]}))?,
    )?;

    // The DAG.
    let closure = |root: &str| -> Vec<String> {
        let mut seen = BTreeSet::new();
        let mut todo = vec![root.to_string()];
        while let Some(n) = todo.pop() {
            if seen.insert(n.clone())
                && let Some(m) = modules.get(&n)
            {
                todo.extend(m.3.iter().cloned());
            }
        }
        seen.into_iter().collect()
    };
    let mut d = dag::Dag::new(&p.id, &p.title, &format!("isa/{}", p.root));
    let isa = p.isa.clone();
    d.artifact = serde_json::json!({"elf": p.artifact.elf, "hash64": elf_sha, "source": p.artifact.source, "build": p.artifact.build,
        "placement": format!(".text at {CODE_BASE:#x} (ELF {text_addr:#x})")});
    d.isa = serde_json::json!({"model": isa.as_ref().map(|i| i.model.clone()), "machine": isa.as_ref().map(|i| i.machine.clone()), "template": isa.as_ref().map(|i| i.template.clone())});
    let rep = p
        .sim
        .as_ref()
        .map(|s| s.representation.clone())
        .unwrap_or_else(|| "G".into());
    d.sim = serde_json::json!({"representation": rep, "module": "sim.wat", "interface": "x86 method API (examples/wasm-sim/x86/src/core.wat)"});
    let mut all_methods = BTreeSet::new();
    for n in &sp.order {
        let (addr, _, sim, _) = &modules[n];
        let pf = p.functions.iter().find(|f| &f.name == n);
        let f = funcs
            .iter()
            .find(|f| f.entry == *addr)
            .context("decoded function")?;
        let heads = loop_heads(f);
        if let Some(pf) = pf {
            for h in &heads {
                if !pf.cuts.iter().any(|c| addr + c.at == *h) {
                    eprintln!("warning: {n}: loop head {h:#x} has no cut in the plan");
                }
            }
        }
        let methods: Vec<String> = sim
            .iter()
            .filter(|m| *m != "get" && *m != "ea")
            .cloned()
            .collect();
        all_methods.extend(methods.iter().cloned());
        let (wl, ws, wp): (Option<String>, Option<String>, Option<String>) = (None, None, None);
        dag::add_function(
            &mut d,
            &dag::FnInfo {
                name: n.clone(),
                isa_statement: format!(
                    "{} on {}: the System V contract of `{n}` (requires {}; ensures {})",
                    isa.as_ref()
                        .map(|i| i.template.as_str())
                        .unwrap_or("FnContract.Spec.Total"),
                    isa.as_ref()
                        .map(|i| i.machine.as_str())
                        .unwrap_or("Open9.isa"),
                    pf.map(|f| f.requires.as_str()).unwrap_or("true"),
                    pf.map(|f| f.ensures.as_str()).unwrap_or("true")
                ),
                isa_lean: pf.and_then(|f| f.isa_lean.clone()),
                closure: closure(n),
                methods,
                module: format!("modules/{n}.wat"),
                piece: format!("pieces/{n}.json"),
                wasm_lean: wl,
                wasm_solution: ws,
                wasm_problem: wp,
                cuts: pf
                    .map(|f| {
                        f.cuts
                            .iter()
                            .map(|c| format!("{:#x}", addr + c.at))
                            .collect()
                    })
                    .unwrap_or_default(),
            },
        );
    }
    let alts: Vec<String> = p
        .sim
        .as_ref()
        .map(|s| {
            s.alternatives
                .iter()
                .map(|a| a.representation.clone())
                .collect()
        })
        .unwrap_or_default();
    dag::add_simulator(
        &mut d,
        &rep,
        &alts,
        &all_methods.iter().cloned().collect::<Vec<_>>(),
        &sp.order,
    );

    if a.granularity == "insn" {
        for n in &sp.order {
            let (addr, ..) = &modules[n];
            let off = (*addr - CODE_BASE) as usize;
            let size = elf.symbol(n).map(|s| s.size as usize).unwrap_or(0);
            match insn::leaf(n, &text[off..off + size], *addr) {
                Ok(l) => {
                    let (wat, idx) = insn::merged_module(n, &l);
                    write(&a.out.join(format!("insn/{n}.wat")), &wat)?;
                    if let Some(il) = p
                        .functions
                        .iter()
                        .find(|f| &f.name == n)
                        .and_then(|f| f.insn.as_ref())
                    {
                        insn_dag(&mut d, n, il, &l);
                    }
                    println!(
                        "insn: {n}: {} step methods, calls {idx:?}; lean: [{}]",
                        l.steps.len(),
                        l.steps
                            .iter()
                            .map(|s| s.lean.clone())
                            .collect::<Vec<_>>()
                            .join(", ")
                    );
                    if a.run {
                        insn_difftest(&engine, n, &wat, &l, &text, *addr)?;
                    }
                }
                Err(e) => println!("insn: {n}: skipped: {e:#}"),
            }
        }
    }
    for f in &p.functions {
        if let Some(dl) = &f.dispatch {
            dispatch_dag(&mut d, &f.name, dl);
        }
        if let Some(dc) = &f.decomposed {
            let mut pieces = vec![];
            for pc in &dc.pieces {
                d.node(dag::Node {
                    id: pc.id.clone(),
                    kind: "wasm-piece".into(),
                    status: if pc.solution.is_some() {
                        "solved".into()
                    } else {
                        "open".into()
                    },
                    statement: Some(pc.statement.clone()),
                    lean: Some(pc.lean.clone()),
                    solution: pc.solution.clone(),
                    solvers: vec![
                        "dispatcher cut points with a measure (exec per entry)".into(),
                        "agent".into(),
                    ],
                    ..Default::default()
                });
                pieces.push(pc.id.clone());
            }
            pieces.extend(dc.callees.iter().map(|c| format!("isa/{c}")));
            d.edge(&format!("isa/{}", f.name), pieces, &dc.theorem, "proved",
                "per-function assume-guarantee: the calls leave the function's dispatcher; the callees enter through their solved ISA contracts");
        }
        if let Some(t) = &f.task {
            let id = format!("task/{}", f.name);
            d.node(dag::Node {
                id: id.clone(),
                kind: "side-condition".into(),
                status: "open".into(),
                statement: Some(t.clone()),
                ..Default::default()
            });
            d.edge(
                &format!("isa/{}", f.name),
                vec![id],
                "",
                "task",
                "owed: see the task node",
            );
        }
    }
    let st = dag::check(&d)?;
    write(&a.out.join("dag.json"), &serde_json::to_string_pretty(&d)?)?;
    println!(
        "{}: {} functions, {} nodes ({} leaves, {} solved; derived solved {}), edges {:?}; root {}",
        p.id,
        sp.order.len(),
        st.nodes,
        st.leaves,
        st.solved,
        st.derived.len(),
        st.edges,
        if st.root_solved { "SOLVED" } else { "open" }
    );
    let isa_solved: Vec<&String> = st
        .derived
        .iter()
        .filter(|n| n.starts_with("isa/"))
        .collect();
    if !isa_solved.is_empty() {
        println!("solved ISA problems (derived through proved edges): {isa_solved:?}");
    }
    if a.run {
        run(&engine, &sim_m, &p, &sp, entry, a.native.as_deref())?;
    }
    Ok(())
}

/// The DAG of the dispatcher route of `n`: `isa/n ⇐ x86/n, term/n`, `x86/n ⇐ wasm-disp/n`.
fn dispatch_dag(d: &mut dag::Dag, n: &str, dl: &plan::DispatchLean) {
    let mk = |id: String, kind: &str, sol: Option<&String>, lean: &str, stmt: &str| dag::Node {
        id,
        kind: kind.into(),
        status: if sol.is_some() {
            "solved".into()
        } else {
            "open".into()
        },
        statement: Some(stmt.into()),
        lean: Some(lean.into()),
        solution: sol.cloned(),
        ..Default::default()
    };
    d.node(mk(
        format!("x86/{n}"),
        "isa-problem",
        None,
        &dl.x86,
        "the x86 problem of the table of decoded instructions (XLProblem), every placement",
    ));
    let mut w = mk(
        format!("wasm-disp/{n}"),
        "wasm-piece",
        dl.piece_solution.as_ref(),
        &dl.piece,
        "every run of the Wasm dispatcher (certified methods emitX, jumps included) ends in the specified state",
    );
    w.solvers = vec![
        "cut-point rule dispatch_hwp + one straight-line problem per entry".into(),
        "agent".into(),
    ];
    d.node(w);
    let (term_sol, term_stmt) = if dl.rank.is_some() {
        (
            None,
            "termination and frame of the x86 table run (from the Wasm ranking)",
        )
    } else {
        (
            dl.term_solution.as_ref(),
            "x86-side termination and frame (the Wasm piece is partial correctness)",
        )
    };
    d.node(mk(
        format!("term/{n}"),
        "side-condition",
        term_sol,
        &dl.term,
        term_stmt,
    ));
    if let (Some(r), Some(t)) = (&dl.rank, &dl.term_of_rank) {
        let mut w = mk(
            format!("wasm-rank/{n}"),
            "wasm-piece",
            dl.rank_solution.as_ref(),
            r,
            "a ranking of the Wasm dispatcher: every entry's code evaluates to a store of smaller rank (termination)",
        );
        w.solvers = vec![
            "straight-line evaluation per entry (exec) + a measure".into(),
            "agent".into(),
        ];
        d.node(w);
        d.edge(
            &format!("term/{n}"),
            vec![format!("wasm-rank/{n}")],
            t,
            "proved",
            "generic xrun_of_ranked: Wasm ranking + certified methods ⇒ x86 run, frame tabWrites",
        );
    }
    d.edge(
        &format!("x86/{n}"),
        vec![format!("wasm-disp/{n}")],
        &dl.x86_of_piece,
        "proved",
        "xlproblem_of_lproblem (Silmaril.Sim.X86.Loop): dispatcher soundness (methods emitX_sound)",
    );
    d.edge(
        &format!("isa/{n}"),
        vec![format!("x86/{n}"), format!("term/{n}")],
        &dl.isa_of,
        "proved",
        "decoding, run_of_xrun, the final ret, System V contract on the open machine",
    );
}

/// The DAG of the per-instruction route of `n`: `isa/n ⇐ x86/n` (the plan's `isa_of_x86`),
/// `x86/n ⇐ wasm-insn/n, tv-insn/n, method/s_*` (P-calls soundness, `x86_of_piece`).
fn insn_dag(d: &mut dag::Dag, n: &str, il: &plan::InsnLean, l: &insn::Leaf) {
    let node = |id: String,
                kind: &str,
                st: Option<&String>,
                lean: &str,
                stmt: String,
                files: Vec<String>| dag::Node {
        id,
        kind: kind.into(),
        status: if st.is_some() {
            "solved".into()
        } else {
            "open".into()
        },
        statement: Some(stmt),
        lean: Some(lean.into()),
        solution: st.cloned(),
        files,
        ..Default::default()
    };
    d.node(node(
        format!("x86/{n}"),
        "isa-problem",
        None,
        &il.x86,
        format!(
            "the x86 problem of `{n}`'s straight-line body on Silmaril.X86.Ext.exec (XProblem)"
        ),
        vec![],
    ));
    let mut wp = node(
        format!("wasm-insn/{n}"),
        "wasm-piece",
        il.piece_solution.as_ref(),
        &il.piece,
        format!(
            "every run of the P-calls body `{n}_body` (step methods given by their contracts) ends with the specified registers"
        ),
        vec![format!("insn/{n}.wat")],
    );
    wp.problem = il.piece_problem.clone();
    wp.solvers = vec![
        "Hoare call rule (hwp_call_step)".into(),
        "wasm-vc / wpc with spec context".into(),
        "agent".into(),
    ];
    d.node(wp);
    d.node(node(format!("tv-insn/{n}"), "translation-validation", il.fns_solution.as_ref(), &il.fns,
        format!("the calls of `{n}_body` reach the step methods emit(i, len) of the decoded instructions (StepFns)"),
        vec![format!("insn/{n}.wat")]));
    let mut pieces = vec![format!("wasm-insn/{n}"), format!("tv-insn/{n}")];
    let mut seen = std::collections::BTreeSet::new();
    for s in &l.steps {
        if seen.insert(s.name.clone()) {
            let id = format!("method/{}", s.name);
            d.node(node(
                id.clone(),
                "wasm-piece",
                Some(&"Silmaril.Sim.X86.GCert.step_valid".to_string()),
                &format!("Silmaril.Sim.X86.GCert.stepSpec (instruction {})", s.lean),
                format!(
                    "the step method `{}` meets its every-run step specification",
                    s.name
                ),
                vec![format!("insn/{n}.wat")],
            ));
            pieces.push(id);
        }
    }
    d.edge(&format!("x86/{n}"), pieces, &il.x86_of_piece, "proved",
        "P-calls soundness (Silmaril.Sim.Reduce.PCalls.xproblem_of_piece): the every-run piece joined with the existing run of the certified step methods");
    d.edge(&format!("isa/{n}"), vec![format!("x86/{n}")], &il.isa_of_x86, "proved",
        "decoding of the bytes, the final ret, System V contract on the open machine (total_of_ext_returns, Spec.Total.toOpen9)");
}

/// Run the merged insn module and the P-mem simulator (`x86-g.wat`) on the same random states and
/// compare GPRs, RIP and the modelled flags after the straight-line body.
fn insn_difftest(
    engine: &wasmtime::Engine,
    name: &str,
    wat: &str,
    l: &insn::Leaf,
    text: &[u8],
    addr: u64,
) -> Result<()> {
    let m = Module::new(engine, wat).map_err(|e| anyhow!("{name}: {e:?}"))?;
    let pmem = harness::load_module(engine, &super::sim_path("g"))?;
    let mut rng = super::difftest::Rng(0x5eed ^ addr);
    let locs: Vec<(usize, i32)> = (0..17)
        .map(|k| (k, k as i32))
        .chain([(17, 17), (20, 20), (21, 21), (22, 22)])
        .collect();
    for _ in 0..200 {
        let regs: Vec<u64> = (0..16).map(|_| rng.val()).collect();
        let flags: Vec<u64> = (0..4).map(|_| rng.next_u64() & 1).collect();
        // merged insn module
        let mut store = Store::new(engine, ());
        let inst = Linker::new(engine)
            .instantiate(&mut store, &m)
            .map_err(|e| anyhow!("{e:?}"))?;
        let set = |store: &mut Store<()>, g: &str, v: u64| -> Result<()> {
            inst.get_global(&mut *store, g)
                .context("global")?
                .set(&mut *store, wasmtime::Val::I64(v as i64))
                .map_err(|e| anyhow!("{e:?}"))
        };
        for (g, &v) in insn::GLOBALS.iter().zip(&regs).take(16) {
            set(&mut store, g, v)?;
        }
        set(&mut store, "rip", addr)?;
        for (j, g) in ["cf", "zf", "sf", "of"].iter().enumerate() {
            set(&mut store, g, flags[j])?;
        }
        inst.get_typed_func::<(), ()>(&mut store, &format!("{name}_body"))
            .map_err(|e| anyhow!("{e:?}"))?
            .call(&mut store, ())
            .map_err(|e| anyhow!("{name}_body trapped: {e:?}"))?;
        let got: Vec<u64> = locs
            .iter()
            .map(|(k, _)| {
                inst.get_global(&mut store, insn::GLOBALS[*k])
                    .unwrap()
                    .get(&mut store)
                    .i64()
                    .unwrap() as u64
            })
            .collect();
        // P-mem reference
        let mut pm = PageMem::default();
        pm.write(CODE_BASE, text);
        let mut s = Sim::new(engine, &pmem, Host::new(Box::new(pm)))?;
        for (k, &v) in regs.iter().enumerate().take(16) {
            s.set(k as i32, v);
        }
        s.set(16, addr);
        for (j, l) in [17, 20, 21, 22].iter().enumerate() {
            s.set(*l, flags[j]);
        }
        for _ in 0..l.steps.len() {
            let st = s.step();
            if st != 0 {
                bail!("{name}: P-mem status {st}");
            }
        }
        let want: Vec<u64> = locs.iter().map(|(_, l)| s.get(*l)).collect();
        if got != want {
            bail!("{name}: insn module differs from P-mem: {got:x?} vs {want:x?}");
        }
    }
    println!(
        "insn: {name}: 200 random states: step methods = P-mem simulator (GPRs, rip, CF ZF SF OF)"
    );
    Ok(())
}

fn run(
    engine: &wasmtime::Engine,
    sim_m: &Module,
    p: &plan::Plan,
    sp: &problem::Split,
    entry: u64,
    native: Option<&Path>,
) -> Result<()> {
    let args: Vec<usize> = if p.args.is_empty() {
        vec![7, 6]
    } else {
        p.args
            .iter()
            .map(|r| {
                GPRS.iter()
                    .position(|g| g == r)
                    .with_context(|| format!("unknown register {r}"))
            })
            .collect::<Result<_>>()?
    };
    let ms: Vec<(String, Module)> = sp
        .modules
        .iter()
        .map(|(n, _, t, _, _)| {
            Ok((
                n.clone(),
                Module::new(engine, t).map_err(|e| anyhow!("{n}: {e:?}"))?,
            ))
        })
        .collect::<Result<_>>()?;
    let canaries: Vec<(usize, u64)> = [3usize, 5, 12, 13, 14, 15]
        .iter()
        .map(|&r| (r, 0x1111_0000_0000_0000 + r as u64))
        .collect();
    let mut bad = 0;
    for t in &p.tests {
        let mut pm = PageMem::default();
        pm.write(problem::WINDOW, &vec![0u8; problem::WINDOW_LEN as usize]);
        pm.write(STACK_TOP, &SENTINEL.to_le_bytes());
        let mut store = Store::new(engine, Host::new(Box::new(pm)));
        let mut linker = Linker::new(engine);
        harness::add_env(&mut linker)?;
        let si = linker
            .instantiate(&mut store, sim_m)
            .map_err(|e| anyhow!("{e:?}"))?;
        linker
            .instance(&mut store, "sim", si)
            .map_err(|e| anyhow!("{e:?}"))?;
        let mut root = None;
        for (n, m) in &ms {
            let i = linker
                .instantiate(&mut store, m)
                .map_err(|e| anyhow!("link {n}: {e:?}"))?;
            linker
                .instance(&mut store, n, i)
                .map_err(|e| anyhow!("{e:?}"))?;
            root = Some(i);
        }
        let mut s = Sim::from_instance(store, si)?;
        s.set(4, STACK_TOP);
        s.set(16, entry);
        for (r, v) in &canaries {
            s.set(*r as i32, *v);
        }
        for (r, v) in args.iter().zip(&t.args) {
            s.set(*r as i32, *v as u64);
        }
        let rf = root
            .context("no module")?
            .get_typed_func::<(), i32>(&mut s.store, &p.root)
            .map_err(|e| anyhow!("{e:?}"))?;
        let st = rf
            .call(&mut s.store, ())
            .map_err(|e| anyhow!("trap: {e:?}"))?;
        let mut ok = st == 0 && s.get(16) == SENTINEL && s.get(4) == STACK_TOP + 8;
        ok &= canaries.iter().all(|(r, v)| s.get(*r as i32) == *v);
        let rax = s.get(0) as i64;
        let nat = match native {
            Some(n) => {
                let o = std::process::Command::new(n)
                    .args(t.args.iter().map(|x| x.to_string()))
                    .output()?;
                Some(String::from_utf8_lossy(&o.stdout).trim().to_string())
            }
            None => None,
        };
        if let Some(nv) = &nat {
            ok &= *nv == rax.to_string();
        }
        if !ok {
            bad += 1;
        }
        println!(
            "{}({}) = {rax} status {st}{}  {}",
            p.root,
            t.args
                .iter()
                .map(|x| x.to_string())
                .collect::<Vec<_>>()
                .join(", "),
            nat.map(|n| format!("  native {n}")).unwrap_or_default(),
            if ok {
                "ok (ABI return checked)"
            } else {
                "MISMATCH"
            }
        );
    }
    if bad > 0 {
        bail!("{bad} test vectors failed");
    }
    Ok(())
}
