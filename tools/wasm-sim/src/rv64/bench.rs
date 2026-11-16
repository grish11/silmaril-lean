//! Speed of the representations on one ELF (instructions retired per second).

use super::asm::{self, Config, Fetch, State};
use super::host::{self, Prog, Sim};
use super::translate;
use std::time::Instant;
use wasmtime::Module;
use wasmtime::error::{Context, Result, bail};

fn report(label: &str, n: u64, secs: f64, st: i32) {
    println!(
        "{label:<34} {n:>12} instr  {secs:>8.3} s  {:>9.1} M instr/s  (status {st})",
        n as f64 / secs / 1e6
    );
}

/// wasm-merge the simulator and the P-calls program into one module and
/// optimise it with wasm-opt -O3 (cross-module inlining of the `i_*` methods).
pub fn merged(sim_wat: &str, prog_wat: &str, tmp: &std::path::Path) -> Result<Vec<u8>> {
    std::fs::write(tmp.join("sim.wasm"), wat::parse_str(sim_wat)?)?;
    std::fs::write(tmp.join("prog.wasm"), wat::parse_str(prog_wat)?)?;
    let st = std::process::Command::new("wasm-merge")
        .args([
            "--enable-multimemory",
            "sim.wasm",
            "sim",
            "prog.wasm",
            "prog",
            "-o",
            "merged.wasm",
        ])
        .current_dir(tmp)
        .status()?;
    if !st.success() {
        bail!("wasm-merge failed");
    }
    let st = std::process::Command::new("wasm-opt")
        .args([
            "--enable-multimemory",
            "-O3",
            "merged.wasm",
            "-o",
            "opt.wasm",
        ])
        .current_dir(tmp)
        .status()?;
    if !st.success() {
        bail!("wasm-opt failed");
    }
    Ok(std::fs::read(tmp.join("opt.wasm"))?)
}

pub fn bench(path: &str, hot_spec: Option<&str>) -> Result<()> {
    let elf = super::elf::parse(&std::fs::read(path)?)?;
    let engine = host::engine();
    let mem = host::mem_module(&engine)?;
    let fuel = 1u64 << 40;
    let tmp = std::env::temp_dir().join(format!("wsim-rv-bench-{}", std::process::id()));
    std::fs::create_dir_all(&tmp)?;
    let t = Instant::now();
    let q = std::process::Command::new("qemu-riscv64")
        .arg(path)
        .output()?;
    report(
        "qemu-riscv64 (native JIT, wall)",
        0,
        t.elapsed().as_secs_f64(),
        q.status.code().unwrap_or(-1),
    );
    for st in [State::G, State::M] {
        for fetch in [Fetch::Import, Fetch::Data] {
            let cfg = Config {
                fetch,
                ..Config::new(st, "full")
            };
            let extra = if fetch == Fetch::Data {
                translate::pdata(&elf)
            } else {
                String::new()
            };
            let m = Module::new(&engine, asm::build(&cfg, &extra))?;
            let mut s = Sim::new(&engine, &m, &mem)?;
            s.load_elf(&elf)?;
            let t = Instant::now();
            let (status, n) = s.run(fuel);
            report(
                &format!(
                    "{st:?} step/run, {}",
                    if fetch == Fetch::Data {
                        "P-data"
                    } else {
                        "P-mem"
                    }
                ),
                n,
                t.elapsed().as_secs_f64(),
                status,
            );
        }
        let prog_wat = translate::pcalls(&elf);
        let m = Module::new(&engine, asm::build(&Config::new(st, "full"), ""))?;
        let prog = Module::new(&engine, &prog_wat)?;
        let mut s = Sim::new(&engine, &m, &mem)?;
        s.load_elf(&elf)?;
        let mut p = Prog::new(&engine, &mut s, &prog)?;
        let t = Instant::now();
        let (status, n) = p.run(&mut s, fuel);
        report(
            &format!("{st:?} P-calls (linked modules)"),
            n,
            t.elapsed().as_secs_f64(),
            status,
        );
        let bytes = merged(&asm::build(&Config::new(st, "full"), ""), &prog_wat, &tmp)?;
        let m = Module::new(&engine, &bytes)?;
        let mut s = Sim::new(&engine, &m, &mem)?;
        s.load_elf(&elf)?;
        let run = s
            .inst
            .get_typed_func::<i64, i32>(&mut s.store, "prog_run")?;
        let left = s
            .inst
            .get_global(&mut s.store, "prog_fuel_left")
            .context("fuel")?;
        let t = Instant::now();
        let status = run.call(&mut s.store, fuel as i64).unwrap_or(3);
        let n = fuel - left.get(&mut s.store).unwrap_i64() as u64;
        report(
            &format!("{st:?} P-calls (wasm-merge + -O3)"),
            n,
            t.elapsed().as_secs_f64(),
            status,
        );
    }
    if let Some(spec) = hot_spec {
        // P-locals: the reduced Wasm function of the hot loop
        let plan = super::reduce::parse_plan(&std::fs::read_to_string(spec)?)?;
        let tmpd = tmp.join("reduce");
        let out = super::reduce::reduce(&elf, &plan, path, &tmpd)?;
        let fname = plan.root.clone();
        let m = Module::new(&engine, &out.modules[&fname])?;
        let mut store = wasmtime::Store::new(&engine, ());
        let inst = wasmtime::Instance::new(&mut store, &m, &[])?;
        let f = inst.get_typed_func::<i64, i64>(&mut store, &fname)?;
        let iters = 20_000_000u64;
        let t = Instant::now();
        f.call(&mut store, iters as i64)?;
        report(
            &format!("P-locals `{fname}` (reduce output)"),
            6 * iters,
            t.elapsed().as_secs_f64(),
            0,
        );
    }
    std::fs::remove_dir_all(&tmp).ok();
    Ok(())
}
