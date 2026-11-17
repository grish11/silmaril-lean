//! RV64 Wasm simulators: tooling (assembler, difftests, reductions, benchmarks).
//!
//! Subcommands:
//!   wat <g|m> <level> [out.wat]          assemble a simulator (levels: base alu nosys full)
//!   run <g|m> <level> <elf> [fuel]       run an ELF on a simulator, print stdout/exit/status
//!   regs <g|m> <level> <elf>             run and print the final registers
//!   difftest <elf>...                    all representations vs qemu-riscv64, plus G/M lockstep
//!   gen-rand <seed> <cases> <out.S>      random per-instruction difftest program
//!   lattice [trials]                     random-step refinement checks base ⊑ alu ⊑ nosys ⊑ full
//!   reduce <plan.toml> <elf> <outdir> [n] RV64 functions + contracts -> Wasm problems, pieces, dag (+ runtime check)
//!   bench <elf> [plan.toml]               speed of all representations
//!   lean-oracle [cases] [lean-dir]       random steps vs the executable Lean model (Ext.MState.step)
//!   lean-prog <elf>...                   whole programs vs the Lean model (env LEAN_DIR)
//!   link-check <elf>                     which lattice points the P-calls program links against
//!   pcalls <elf> [out.wat]               P-calls translation of the ELF text
//!   run-pcalls <g|m> <level> <elf>       run the P-calls translation (mixed mode with `step`)
//!   run-pdata <g|m> <level> <elf>        run on a P-data simulator (code in its data segment)

use asm::{Config, State};
use std::io::Write;
use wasm_sim::rv64;
use wasm_sim::rv64::{asm, bench, check, elf, host, randprog, reduce, translate};
use wasmtime::error::{Context, Result, bail};

fn state(s: &str) -> Result<State> {
    Ok(match s {
        "g" | "G" => State::G,
        "m" | "M" => State::M,
        _ => bail!("state must be g or m"),
    })
}

fn load(path: &str) -> Result<elf::Elf> {
    elf::parse(&std::fs::read(path).with_context(|| path.to_string())?)
}

fn main() -> Result<()> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let a = |i: usize| args.get(i).map(String::as_str).unwrap_or("");
    match a(0) {
        "wat" => {
            let wat = asm::build(&Config::new(state(a(1))?, a(2)), "");
            if args.len() > 3 {
                std::fs::write(a(3), wat)?
            } else {
                print!("{wat}")
            }
        }
        "run" | "regs" => {
            let engine = host::engine();
            let sim =
                wasmtime::Module::new(&engine, asm::build(&Config::new(state(a(1))?, a(2)), ""))?;
            let mem = host::mem_module(&engine)?;
            let mut s = host::Sim::new(&engine, &sim, &mem)?;
            s.load_elf(&load(a(3))?)?;
            let fuel = a(4).parse().unwrap_or(1u64 << 40);
            let (st, n) = s.run(fuel);
            std::io::stdout().write_all(&s.host().out)?;
            eprintln!("status {st} retired {n} exit {:?}", s.host().exit);
            if a(0) == "regs" {
                for (i, r) in s.regs().iter().enumerate() {
                    println!(
                        "{} {r:#018x}",
                        if i == 32 {
                            "pc".to_string()
                        } else {
                            format!("x{i}")
                        }
                    );
                }
            }
            std::process::exit(s.host().exit.unwrap_or(100 + st as i64) as i32);
        }
        "difftest" => {
            let engine = host::engine();
            let mut ok = true;
            for p in &args[1..] {
                ok &= check::difftest(&engine, p)?;
                match check::lockstep(&engine, p, "full") {
                    Ok(n) => println!("ok   {p}: G/M lockstep, {n} steps"),
                    Err(e) => {
                        ok = false;
                        println!("FAIL lockstep {e}")
                    }
                }
            }
            if !ok {
                bail!("difftest failed")
            }
        }
        "gen-rand" => std::fs::write(a(3), randprog::program(a(1).parse()?, a(2).parse()?))?,
        "lattice" => {
            let engine = host::engine();
            let trials = a(1).parse().unwrap_or(100_000);
            for st in [State::G, State::M] {
                for (k, (lo, hi)) in [
                    ("base", "alu"),
                    ("alu", "nosys"),
                    ("nosys", "full"),
                    ("base", "full"),
                ]
                .iter()
                .enumerate()
                {
                    let c = check::lattice(&engine, lo, hi, st, trials, 1000 + k as u64)?;
                    println!(
                        "ok   {st:?}: {lo} ⊑ {hi}: {trials} steps: {} agree, {} only {hi}, {} neither",
                        c[0], c[1], c[2]
                    );
                }
            }
        }
        "bench" => bench::bench(a(1), args.get(2).map(String::as_str))?,
        "reduce" => {
            let e = load(a(2))?;
            let plan = reduce::parse_plan(&std::fs::read_to_string(a(1))?)?;
            let dir = std::path::Path::new(a(3));
            let out = reduce::reduce(&e, &plan, a(2), dir)?;
            let lean_dir = args
                .iter()
                .position(|x| x == "--lean")
                .and_then(|i| args.get(i + 1))
                .cloned();
            if let Some(ld) = &lean_dir {
                for f in &plan.functions {
                    let Some((ent, pre, post)) = &f.lean else {
                        continue;
                    };
                    let callees: Vec<(String, String, bool)> = out.callees[&f.name]
                        .iter()
                        .map(|c| {
                            let ce = plan
                                .functions
                                .iter()
                                .find(|g| &g.name == c)
                                .and_then(|g| g.lean.as_ref())
                                .map(|l| l.0.clone());
                            let pure = !out.modules[c].contains("(import \"env\" \"memory\"");
                            (
                                c.clone(),
                                ce.unwrap_or_else(|| {
                                    panic!("{}: callee {c} has no lean_spec", f.name)
                                }),
                                pure,
                            )
                        })
                        .collect();
                    let ed = std::path::Path::new(ld).join(ent);
                    std::fs::create_dir_all(&ed)?;
                    let wat_file = format!("{}.wat", f.name);
                    std::fs::write(ed.join(&wat_file), &out.modules[&f.name])?;
                    let lf = rv64::lean::LeanFn {
                        entry: ent,
                        func: &f.name,
                        pre,
                        post,
                        summary: format!(
                            "RV64 `{}` ({}), P-locals translation: {}",
                            f.name, plan.id, f.ensures
                        ),
                    };
                    let (defs, man) =
                        rv64::lean::entry(&lf, &out, &wat_file, &plan.lean_prelude, &callees)?;
                    std::fs::write(ed.join("Defs.lean"), defs)?;
                    std::fs::write(ed.join("manifest.toml"), man)?;
                    println!("lean: {} -> {}", f.name, ed.display());
                }
            }
            let samples = a(4).parse().unwrap_or(100);
            let (ok, faults, skipped, runs) = reduce::check(&e, &plan, &out, samples)?;
            let lean_dir = std::env::var("LEAN_DIR")
                .ok()
                .filter(|d| std::path::Path::new(d).join(".lake").exists() && lean_dir.is_some());
            let (so, ss, lo) = rv64::consistency::check(&plan, &out, &runs, lean_dir.as_deref())?;
            println!(
                "ok   contracts {}: on {} returning runs of memory-free functions: SMT requires∧ensures true {so} (z3), skipped {ss} (declared functions); Lean Pre∧Post true {lo}{}",
                plan.id,
                runs.len(),
                if lean_dir.is_none() {
                    " (Lean not run: set LEAN_DIR and --lean)"
                } else {
                    ""
                }
            );
            println!(
                "ok   reduce {}: {} Wasm problems in {}; runtime check vs simulator: {ok} runs return with equal results and memory, {faults} fault in both, {skipped} skipped (fuel)",
                plan.id,
                out.modules.len(),
                dir.display()
            );
        }
        "lean-oracle" => {
            let n = a(1).parse().unwrap_or(2000);
            let lean_dir = std::env::var("LEAN_DIR").unwrap_or_default();
            let dir = if a(2).is_empty() {
                lean_dir.as_str()
            } else {
                a(2)
            };
            if dir.is_empty() {
                bail!(
                    "lean-oracle: pass a Silmaril checkout as the second argument or set LEAN_DIR"
                );
            }
            let t = std::time::Instant::now();
            let k = check::lean_oracle(n, dir, 42)?;
            println!(
                "ok   lean-oracle: {k} random steps agree with Ext.MState.step (G and M nosys), {:.1} s",
                t.elapsed().as_secs_f64()
            );
        }
        "lean-prog" => {
            let Ok(dir) = std::env::var("LEAN_DIR") else {
                bail!("lean-prog: set LEAN_DIR to a Silmaril checkout");
            };
            for p in &args[1..] {
                let t = std::time::Instant::now();
                let n = check::lean_prog(p, &dir, 1_000_000)?;
                println!(
                    "ok   lean-prog {p}: {n} steps to the first non-retired outcome agree with Ext.MState.step (G, M nosys; registers, pc, segment bytes), {:.1} s",
                    t.elapsed().as_secs_f64()
                );
            }
        }
        "link-check" => {
            let engine = host::engine();
            let prog = wasmtime::Module::new(&engine, translate::pcalls(&load(a(1))?))?;
            let mem = host::mem_module(&engine)?;
            for lvl in ["base", "alu", "nosys", "full"] {
                let sim =
                    wasmtime::Module::new(&engine, asm::build(&Config::new(State::G, lvl), ""))?;
                let mut s = host::Sim::new(&engine, &sim, &mem)?;
                match host::Prog::new(&engine, &mut s, &prog) {
                    Ok(_) => println!("{}: links against {lvl}", a(1)),
                    Err(e) => println!(
                        "{}: rejected by {lvl}: {}",
                        a(1),
                        e.to_string().lines().next().unwrap_or("")
                    ),
                }
            }
        }
        "pcalls" => {
            let wat = translate::pcalls(&load(a(1))?);
            if args.len() > 2 {
                std::fs::write(a(2), wat)?
            } else {
                print!("{wat}")
            }
        }
        "run-pcalls" | "run-pdata" => {
            let engine = host::engine();
            let e = load(a(3))?;
            let mut cfg = Config::new(state(a(1))?, a(2));
            let extra = if a(0) == "run-pdata" {
                cfg.fetch = asm::Fetch::Data;
                translate::pdata(&e)
            } else {
                String::new()
            };
            let sim = wasmtime::Module::new(&engine, asm::build(&cfg, &extra))?;
            let mem = host::mem_module(&engine)?;
            let mut s = host::Sim::new(&engine, &sim, &mem)?;
            s.load_elf(&e)?;
            let (st, n) = if a(0) == "run-pcalls" {
                let prog = wasmtime::Module::new(&engine, translate::pcalls(&e))?;
                let mut p = host::Prog::new(&engine, &mut s, &prog)?;
                p.run(&mut s, 1 << 40)
            } else {
                s.run(1 << 40)
            };
            std::io::stdout().write_all(&s.host().out)?;
            eprintln!("status {st} retired {n} exit {:?}", s.host().exit);
            std::process::exit(s.host().exit.unwrap_or(100 + st as i64) as i32);
        }
        _ => bail!("usage: see src/main.rs"),
    }
    Ok(())
}
