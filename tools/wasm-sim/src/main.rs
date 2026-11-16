//! `wasm-sim`: runtime harness for ISA simulators in Wasm (docs/projects/wasm-sim-abi.md).

use wasm_sim::{harness, x86};

use anyhow::{Result, bail};
use clap::{Parser, Subcommand};
use harness::{Host, PageMem, Sim};
use std::path::PathBuf;
use x86::{STACK_SIZE, STACK_TOP, sim_module_path, sysv_entry};

#[derive(Parser)]
#[command(name = "wasm-sim", about = "Harness for ISA simulators in Wasm")]
struct Cli {
    #[command(subcommand)]
    cmd: Cmd,
}

#[derive(Subcommand)]
enum Cmd {
    /// Regenerate examples/wasm-sim/x86/x86-{g,m}.wat from the sources
    GenX86,
    /// Write (or `--check`) the wat3! quotations of x86-{g,m}.wat in Silmaril/Sim/X86Real/Defs.lean
    LeanQuote {
        #[arg(long)]
        check: bool,
    },
    /// Run raw x86-64 code (P-mem) as a function: SysV args, sentinel return address
    Run {
        /// simulator: g, m, or a path to a .wat/.wasm
        #[arg(long, default_value = "g")]
        sim: String,
        /// raw code bytes (e.g. objcopy -O binary)
        code: PathBuf,
        #[arg(long, default_value_t = 0x400000, value_parser = parse_u64)]
        base: u64,
        /// entry offset into the code
        #[arg(long, default_value_t = 0, value_parser = parse_u64)]
        entry: u64,
        /// integer arguments (rdi rsi rdx rcx r8 r9)
        #[arg(long, value_delimiter = ',', value_parser = parse_u64)]
        args: Vec<u64>,
        /// extra register settings loc=value
        #[arg(long = "set")]
        sets: Vec<String>,
        #[arg(long, default_value_t = 1_000_000)]
        fuel: u64,
        /// print the state after every instruction
        #[arg(long)]
        trace: bool,
    },
    /// Difftest single instructions against the CPU
    DifftestInsn(x86::difftest::InsnArgs),
    /// Difftest functions from .S files against the CPU
    DifftestFn(x86::difftest::FnArgs),
    /// Lockstep G vs M (and P-calls vs P-mem) on functions from .S files
    Lockstep(x86::difftest::LockArgs),
    /// Translate a function (raw code) into a P-calls program module
    Pcalls(x86::pcalls::Args),
    /// Emit (and check) Wasm problems from x86 functions + contracts: closed and split forms
    Problems(x86::problem::Args),
    /// ELF functions: native vs P-mem, the layer stack L0..L4, and their equivalence problems
    Elfv(x86::elfv::Args),
    /// Benchmarks
    Bench(x86::difftest::BenchArgs),
    /// Reduce an x86 problem (reduction plan) to a DAG of Wasm problems (docs/projects/wasm-sim-reduction.md)
    Reduce(x86::reduce::Args),
    /// Problem DAGs (silmaril.wasm-sim.dag.v0): validate and summarise
    Dag {
        #[command(subcommand)]
        cmd: DagCmd,
    },
}

#[derive(Subcommand)]
enum DagCmd {
    /// Validate DAG files and print their statistics and derived status
    Check { files: Vec<PathBuf> },
}

pub fn parse_u64(s: &str) -> Result<u64, String> {
    let s = s.replace('_', "");
    let (neg, t) = if let Some(t) = s.strip_prefix('-') {
        (true, t.to_string())
    } else {
        (false, s)
    };
    let v = if let Some(h) = t.strip_prefix("0x") {
        u64::from_str_radix(h, 16)
    } else {
        t.parse::<u64>()
    }
    .map_err(|e| e.to_string())?;
    Ok(if neg { v.wrapping_neg() } else { v })
}

fn dump(sim: &mut Sim) {
    let st = sim.state(x86::NLOCS);
    let mut line = String::new();
    for (i, v) in st.iter().enumerate() {
        if let Some(v) = v {
            if i < 17 {
                line += &format!("{}={:#x} ", x86::NAMES[i], v);
            } else {
                line += &format!("{}={} ", x86::NAMES[i], v);
            }
        }
    }
    println!("{}", line.trim_end());
}

fn main() -> Result<()> {
    let cli = Cli::parse();
    match cli.cmd {
        Cmd::GenX86 => x86::generate(),
        Cmd::LeanQuote { check } => x86::lean_quote(check),
        Cmd::Run {
            sim,
            code,
            base,
            entry,
            args,
            sets,
            fuel,
            trace,
        } => {
            let engine = harness::engine();
            let module = harness::load_module(&engine, &sim_module_path(&sim))?;
            let bytes = std::fs::read(&code)?;
            let mut mem = PageMem::default();
            mem.write(base, &bytes);
            mem.map(STACK_TOP - STACK_SIZE, STACK_SIZE);
            let mut s = Sim::new(&engine, &module, Host::new(Box::new(mem)))?;
            sysv_entry(&mut s, base + entry, &args);
            for kv in sets {
                let Some((k, v)) = kv.split_once('=') else {
                    bail!("--set loc=value")
                };
                let Some(l) = x86::loc_of(k) else {
                    bail!("unknown location {k}")
                };
                s.set(l, parse_u64(v).map_err(anyhow::Error::msg)?);
            }
            let (st, n) = if trace {
                let mut n = 0;
                loop {
                    if n == fuel {
                        break (harness::ST_FUEL, n);
                    }
                    let st = s.step();
                    if st != 0 {
                        break (st, n);
                    }
                    n += 1;
                    dump(&mut s);
                }
            } else {
                (s.run(fuel), 0)
            };
            println!(
                "status {st}{}",
                if trace {
                    format!(" after {n} instructions")
                } else {
                    String::new()
                }
            );
            if let Some(f) = &s.fault {
                println!("fault: {f}");
            }
            dump(&mut s);
            let out = &s.store.data().stdout;
            if !out.is_empty() {
                println!("stdout: {:?}", String::from_utf8_lossy(out));
            }
            Ok(())
        }
        Cmd::DifftestInsn(a) => x86::difftest::insn(a),
        Cmd::DifftestFn(a) => x86::difftest::functions(a),
        Cmd::Lockstep(a) => x86::difftest::lockstep(a),
        Cmd::Pcalls(a) => x86::pcalls::main(a),
        Cmd::Problems(a) => x86::problem::main(a),
        Cmd::Elfv(a) => x86::elfv::main(a),
        Cmd::Bench(a) => x86::difftest::bench(a),
        Cmd::Reduce(a) => x86::reduce::main(a),
        Cmd::Dag {
            cmd: DagCmd::Check { files },
        } => {
            let mut bad = 0;
            for f in files {
                let r = std::fs::read_to_string(&f)
                    .map_err(anyhow::Error::from)
                    .and_then(|t| Ok(serde_json::from_str::<wasm_sim::reduce::dag::Dag>(&t)?))
                    .and_then(|d| wasm_sim::reduce::dag::check(&d).map(|s| (d, s)));
                match r {
                    Ok((d, s)) => {
                        println!(
                            "{}: ok: {} nodes, {} leaves, {} solved, derived solved {}, edges {:?}, root {} {}",
                            f.display(),
                            s.nodes,
                            s.leaves,
                            s.solved,
                            s.derived.len(),
                            s.edges,
                            d.root,
                            if s.root_solved { "SOLVED" } else { "open" }
                        );
                        let isa: Vec<&String> = s
                            .derived
                            .iter()
                            .filter(|n| {
                                d.nodes
                                    .iter()
                                    .any(|m| &m.id == *n && m.kind == "isa-problem")
                            })
                            .collect();
                        if !isa.is_empty() {
                            println!("  solved ISA-level problems: {isa:?}");
                        }
                    }
                    Err(e) => {
                        bad += 1;
                        println!("{}: INVALID: {e:#}", f.display());
                    }
                }
            }
            if bad > 0 {
                bail!("{bad} invalid DAG files");
            }
            Ok(())
        }
    }
}
