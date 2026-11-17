//! `wsim-proc run [--sim S.wasm] [--wasm-mem mem.wasm] [--wasm-ext libc.wasm] PROG ARGS...`
use std::path::PathBuf;
use wasm_sim::proc::host::{self, EnvOpts};
use wasmtime::error::Context;
use wasmtime::{Engine, Module};
use wasmtime::{Result, bail};

fn proc_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../examples/wasm-sim/proc")
}

fn main() -> Result<()> {
    let mut args: Vec<String> = std::env::args().skip(1).collect();
    if args.is_empty() {
        bail!("usage: wsim-proc run|sysv|bench ...");
    }
    let cmd = args.remove(0);
    let mut sim = proc_dir().join("build/x86-mini.wasm");
    let named = |s: &str| match s {
        "mini" | "g" | "m" => proc_dir().join(format!("build/x86-{s}.wasm")),
        _ => PathBuf::from(s),
    };
    let mut opts = EnvOpts {
        wasm_mem: None,
        wasm_ext: None,
        extrun: Some(proc_dir().join("build/extrun.wasm")),
    };
    while let Some(a) = args.first().cloned() {
        match a.as_str() {
            "--sim" => {
                sim = named(&args[1]);
                args.drain(..2);
            }
            "--wasm-mem" => {
                opts.wasm_mem = Some(args[1].clone().into());
                args.drain(..2);
            }
            "--wasm-ext" => {
                opts.wasm_ext = Some(args[1].clone().into());
                args.drain(..2);
            }
            _ => break,
        }
    }
    if cmd == "componentize" {
        // componentize IN.wasm OUT.wasm iface,iface,...
        let wasm = std::fs::read(&args[0])?;
        let keep: Vec<&str> = args
            .get(2)
            .map(|s| s.split(',').collect())
            .unwrap_or_default();
        std::fs::write(
            &args[1],
            wasm_sim::component::componentize_names(&wasm, &keep)?,
        )?;
        return Ok(());
    }
    let engine = Engine::default();
    let simm = Module::from_file(&engine, &sim).with_context(|| format!("{}", sim.display()))?;
    match cmd.as_str() {
        // glibc [--libc PATH] [--in-sim f,g] [--fuel N] [-v] PROG ARGS...: route (b) of
        // the glibc bridge (real glibc code for the imports listed in --in-sim)
        "glibc" => {
            let mut libc = PathBuf::from("/usr/lib/x86_64-linux-gnu/libc.so.6");
            let (mut in_sim, mut fuel, mut verbose, mut fs) = (vec![], 10_000_000u64, false, false);
            let mut imports: Vec<String> = vec![];
            while let Some(a) = args.first().cloned() {
                match a.as_str() {
                    "--libc" => libc = args[1].clone().into(),
                    "--in-sim" => in_sim = args[1].split(',').map(String::from).collect(),
                    "--import" => imports = args[1].split(',').map(String::from).collect(),
                    "--fuel" => fuel = args[1].parse()?,
                    "--fs" => {
                        fs = true;
                        args.remove(0);
                        continue;
                    }
                    "-v" => {
                        verbose = true;
                        args.remove(0);
                        continue;
                    }
                    _ => break,
                }
                args.drain(..2);
            }
            let file = std::fs::read(&args[0]).context("reading program")?;
            let lib = std::fs::read(&libc).context("reading libc")?;
            let argv: Vec<Vec<u8>> = args.iter().map(|s| s.clone().into_bytes()).collect();
            let r = wasm_sim::proc::glibc::run(
                &engine, &simm, &file, &lib, &argv, &in_sim, fuel, fs, &imports,
            )?;
            wasm_sim::proc::glibc::print(&r, verbose);
            use std::io::Write;
            std::io::stdout().write_all(&r.out)?;
            std::process::exit(r.exit.unwrap_or(100));
        }
        "run" => {
            let file = std::fs::read(&args[0]).context("reading program")?;
            let argv: Vec<Vec<u8>> = args.iter().map(|s| s.clone().into_bytes()).collect();
            let o = host::run_elf(&engine, &opts, &simm, &file, &argv, true)?;
            match o.exit {
                Some(c) => std::process::exit(c),
                None => {
                    eprintln!(
                        "wsim-proc: simulator stopped, status {} at rip {:#x}",
                        o.status, o.rip
                    );
                    std::process::exit(100 + o.status)
                }
            }
        }
        // sysv [N [SEED]]: differential test of sysv.wasm + simulator vs native calls
        "sysv" => {
            // --set x86: examples/wasm-sim/x86/tests/funcs.S instead of progs/sysv_fns
            let x86 = args.first().is_some_and(|a| a == "--set") && args[1] == "x86";
            if args.first().is_some_and(|a| a == "--set") {
                args.drain(..2);
            }
            let n = args.first().map(|s| s.parse()).transpose()?.unwrap_or(200);
            let seed = args.get(1).map(|s| s.parse()).transpose()?.unwrap_or(1);
            let progs = proc_dir().join("progs");
            let (elf, driver, tests) = if x86 {
                ("x86_funcs", "x86_native", wasm_sim::sysv::TESTS_X86)
            } else {
                ("sysv_fns", "sysv_native", wasm_sim::sysv::TESTS)
            };
            let code = std::fs::read(progs.join(elf))?;
            let wrapper = Module::from_file(&engine, proc_dir().join("build/sysv.wasm"))?;
            let mut w = wasm_sim::sysv::Wrapper::new(&engine, &opts, &simm, &wrapper, &code)?;
            let t = std::time::Instant::now();
            let rep = wasm_sim::sysv::difftest(
                &mut w,
                &code,
                progs.join(driver).to_str().unwrap(),
                tests,
                n,
                seed,
            )?;
            for f in rep.failures.iter().take(20) {
                println!("FAIL {f}");
            }
            println!(
                "sysv: {} calls, {} failures, {:?}",
                rep.calls,
                rep.failures.len(),
                t.elapsed()
            );
            std::process::exit(if rep.failures.is_empty() { 0 } else { 1 })
        }
        _ => bail!("unknown command {cmd}"),
    }
}
