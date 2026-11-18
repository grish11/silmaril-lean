//! Differential tests: simulators vs qemu-riscv64, G vs M lockstep, and the
//! lattice refinement check (smaller simulator either reports status 2 with no
//! state change, or agrees with the larger one).

use super::asm::{self, Config, Fetch, State};
use super::elf::Elf;
use super::host::{self, Prog, Sim};
use super::translate;
use wasmtime::error::{Result, bail};
use wasmtime::{Engine, Module};

pub struct Outcome {
    pub out: Vec<u8>,
    pub exit: Option<i64>,
    pub status: i32,
    pub retired: u64,
}

pub fn qemu(path: &str) -> Result<Outcome> {
    let o = std::process::Command::new("qemu-riscv64")
        .arg(path)
        .output()?;
    Ok(Outcome {
        out: o.stdout,
        exit: o.status.code().map(|c| c as i64),
        status: 1,
        retired: 0,
    })
}

#[derive(Clone, Copy, Debug)]
pub enum Repr {
    /// `step`/`run` with code fetched through mem.load32
    Pmem(State),
    /// `run` with code in the simulator's data segment
    Pdata(State),
    /// P-calls program linked against the simulator (mixed mode)
    Pcalls(State),
}

pub fn sim_for(engine: &Engine, cfg: &Config, elf: &Elf) -> Result<Sim> {
    let extra = if cfg.fetch == Fetch::Data {
        translate::pdata(elf)
    } else {
        String::new()
    };
    let m = Module::new(engine, asm::build(cfg, &extra))?;
    let mut s = Sim::new(engine, &m, &host::mem_module(engine)?)?;
    s.load_elf(elf)?;
    Ok(s)
}

pub fn run_repr(
    engine: &Engine,
    r: Repr,
    level: &str,
    elf: &Elf,
    fuel: u64,
) -> Result<(Outcome, Sim)> {
    let (st, cfg) = match r {
        Repr::Pmem(s) | Repr::Pcalls(s) => (s, Config::new(s, level)),
        Repr::Pdata(s) => (
            s,
            Config {
                fetch: Fetch::Data,
                ..Config::new(s, level)
            },
        ),
    };
    let _ = st;
    let mut s = sim_for(engine, &cfg, elf)?;
    let (status, retired) = match r {
        Repr::Pcalls(_) => {
            let prog = Module::new(engine, translate::pcalls(elf))?;
            let mut p = Prog::new(engine, &mut s, &prog)?;
            p.run(&mut s, fuel)
        }
        _ => s.run(fuel),
    };
    let h = s.host();
    Ok((
        Outcome {
            out: h.out.clone(),
            exit: h.exit,
            status,
            retired,
        },
        s,
    ))
}

/// Compare every representation against qemu on one ELF.
pub fn difftest(engine: &Engine, path: &str) -> Result<bool> {
    let elf = super::elf::parse(&std::fs::read(path)?)?;
    let q = qemu(path)?;
    let mut ok = true;
    for r in [
        Repr::Pmem(State::G),
        Repr::Pmem(State::M),
        Repr::Pdata(State::G),
        Repr::Pdata(State::M),
        Repr::Pcalls(State::G),
        Repr::Pcalls(State::M),
    ] {
        let (o, _) = run_repr(engine, r, "full", &elf, 1 << 34)?;
        let same = o.out == q.out && o.exit == q.exit;
        ok &= same;
        if !same {
            println!(
                "  MISMATCH {path} {r:?}: exit {:?} vs qemu {:?}, status {}, stdout {} vs {} bytes",
                o.exit,
                q.exit,
                o.status,
                o.out.len(),
                q.out.len()
            );
            report_dump_diff(&o.out, &q.out);
        }
    }
    println!(
        "{} {path}: stdout {} bytes, exit {:?}",
        if ok { "ok  " } else { "FAIL" },
        q.out.len(),
        q.exit
    );
    Ok(ok)
}

/// Explain the first differing 256-byte register record, if any.
fn report_dump_diff(a: &[u8], b: &[u8]) {
    for (k, (ra, rb)) in a.chunks(256).zip(b.chunks(256)).enumerate() {
        if ra != rb {
            for i in 0..32 {
                let x = ra
                    .get(8 * i..8 * i + 8)
                    .map(|s| u64::from_le_bytes(s.try_into().unwrap()));
                let y = rb
                    .get(8 * i..8 * i + 8)
                    .map(|s| u64::from_le_bytes(s.try_into().unwrap()));
                if x != y {
                    println!("    record {k} x{i}: sim {x:x?} qemu {y:x?}");
                }
            }
            return;
        }
    }
}

/// Step G and M in lockstep, comparing status and all 33 locations after each step.
pub fn lockstep(engine: &Engine, path: &str, level: &str) -> Result<u64> {
    let elf = super::elf::parse(&std::fs::read(path)?)?;
    let mut g = sim_for(engine, &Config::new(State::G, level), &elf)?;
    let mut m = sim_for(engine, &Config::new(State::M, level), &elf)?;
    let mut n = 0;
    loop {
        let (sg, sm) = (g.step(), m.step());
        if sg != sm {
            bail!("{path}: step {n}: status G {sg} M {sm}");
        }
        let (rg, rm) = (g.regs(), m.regs());
        if rg != rm {
            bail!("{path}: step {n}: state differs: G {rg:x?} M {rm:x?}");
        }
        if sg != 0 {
            return Ok(n);
        }
        n += 1;
    }
}

/// A random instruction word: half canonical Ext.Compute encodings, half
/// random words with a valid major opcode (so all groups and the
/// non-canonical funct fields are hit).
fn random_word(r: &mut super::randprog::Rng) -> u32 {
    const OPS: [u32; 13] = [
        0x03, 0x13, 0x17, 0x1B, 0x23, 0x33, 0x37, 0x3B, 0x63, 0x67, 0x6F, 0x73, 0x0F,
    ];
    match r.below(5) {
        0 | 1 => super::decode::encode(&super::randprog::compute(r)),
        4 => {
            // load or store with a small offset (so that data-page bases stay in the page)
            let off = (r.below(128) as u32).wrapping_sub(64) & 0xFFF;
            let (rs1, rd, f3) = (r.below(32) as u32, r.below(32) as u32, r.below(8) as u32);
            if r.below(2) == 0 {
                (off << 20) | (rs1 << 15) | (f3 << 12) | (rd << 7) | 0x03
            } else {
                ((off >> 5) << 25)
                    | (rd << 20)
                    | (rs1 << 15)
                    | (f3 << 12)
                    | ((off & 31) << 7)
                    | 0x23
            }
        }
        2 => (r.next_u64() as u32 & !0x7F) | OPS[r.below(OPS.len() as u64) as usize],
        _ => [0x0010_0073, 0x0000_0073, 0x0000_100F, r.next_u64() as u32][r.below(4) as usize],
    }
}

/// Lattice refinement check `small ⊑ big` on random single steps: from equal
/// states, either `small` reports 2 (unsupported) and leaves its state
/// unchanged, or both report the same status and reach the same state. Also
/// checks that `big` never rejects what `small` accepts, that the Rust decoder
/// agrees with the WAT decoder of `full` on acceptance, and that exports and
/// imports of `small` are included in those of `big`.
pub fn lattice(
    engine: &Engine,
    small: &str,
    big: &str,
    st: State,
    trials: u64,
    seed: u64,
) -> Result<[u64; 3]> {
    let ms = Module::new(engine, asm::build(&Config::new(st, small), ""))?;
    let mb = Module::new(engine, asm::build(&Config::new(st, big), ""))?;
    let names = |m: &Module| -> (Vec<String>, Vec<String>) {
        (
            m.exports().map(|e| e.name().to_string()).collect(),
            m.imports()
                .map(|i| format!("{}.{}", i.module(), i.name()))
                .collect(),
        )
    };
    let ((es, is), (eb, ib)) = (names(&ms), names(&mb));
    if let Some(x) = es.iter().find(|x| !eb.contains(x)) {
        bail!("export {x} of {small} missing in {big}");
    }
    if let Some(x) = is.iter().find(|x| !ib.contains(x)) {
        bail!("import {x} of {small} missing in {big}");
    }
    let mem = host::mem_module(engine)?;
    let mut s = Sim::new(engine, &ms, &mem)?;
    let mut b = Sim::new(engine, &mb, &mem)?;
    let mut r = super::randprog::Rng::new(seed);
    let mut counts = [0u64; 3]; // [both agree, small unsupported, both unsupported]
    for n in 0..trials {
        let pc = 0x10000 + 4 * r.below(1024);
        let w = random_word(&mut r);
        for sim in [&mut s, &mut b] {
            sim.env.data_mut(&mut sim.store)[pc as usize..pc as usize + 4]
                .copy_from_slice(&w.to_le_bytes());
        }
        let mut init = [0u64; 33];
        for (i, x) in init.iter_mut().enumerate().skip(1) {
            *x = if i == 32 {
                pc
            } else if r.below(3) == 0 {
                0x20000 + 8 * r.below(4096)
            } else {
                r.value()
            };
        }
        for sim in [&mut s, &mut b] {
            for (i, &x) in init.iter().enumerate() {
                sim.set(i as i32, x);
            }
        }
        let before = s.regs();
        let (ss, sb) = (s.step(), b.step());
        let (rs, rb) = (s.regs(), b.regs());
        let accepted = super::decode::decode(w).is_some();
        if big == "full" && (sb == 2) == accepted {
            bail!(
                "trial {n}: word {w:#010x}: Rust decoder accepted={accepted}, WAT full status {sb}"
            );
        }
        if ss == 2 {
            if rs != before {
                bail!("trial {n}: word {w:#010x}: {small} status 2 but state changed");
            }
            counts[if sb == 2 { 2 } else { 1 }] += 1;
        } else if ss != sb || rs != rb {
            bail!(
                "trial {n}: word {w:#010x}: {small} status {ss} vs {big} {sb}; states {rs:x?} / {rb:x?}"
            );
        } else {
            counts[0] += 1;
        }
    }
    Ok(counts)
}

/// Environment memory matching `lean/StepOracle.lean`: only the code page
/// [0x10000, 0x11000) and the data page [0x20000, 0x21000) are accessible.
const MEM_STRICT: &str = r#"(module
  (memory (export "memory") 3)
  (func $a (param $a i64) (param $n i64) (result i32)
    (if (i32.eqz (i32.or
      (i32.and (i64.ge_u (local.get $a) (i64.const 0x10000)) (i64.le_u (i64.add (local.get $a) (local.get $n)) (i64.const 0x11000)))
      (i32.and (i64.ge_u (local.get $a) (i64.const 0x20000)) (i64.le_u (i64.add (local.get $a) (local.get $n)) (i64.const 0x21000)))))
      (then (unreachable)))
    (i32.wrap_i64 (local.get $a)))
  (func (export "load8") (param $a i64) (result i64) (i64.load8_u (call $a (local.get $a) (i64.const 1))))
  (func (export "load16") (param $a i64) (result i64) (i64.load16_u (call $a (local.get $a) (i64.const 2))))
  (func (export "load32") (param $a i64) (result i64) (i64.load32_u (call $a (local.get $a) (i64.const 4))))
  (func (export "load64") (param $a i64) (result i64) (i64.load (call $a (local.get $a) (i64.const 8))))
  (func (export "store8") (param $a i64) (param $v i64) (i64.store8 (call $a (local.get $a) (i64.const 1)) (local.get $v)))
  (func (export "store16") (param $a i64) (param $v i64) (i64.store16 (call $a (local.get $a) (i64.const 2)) (local.get $v)))
  (func (export "store32") (param $a i64) (param $v i64) (i64.store32 (call $a (local.get $a) (i64.const 4)) (local.get $v)))
  (func (export "store64") (param $a i64) (param $v i64) (i64.store (call $a (local.get $a) (i64.const 8)) (local.get $v))))"#;

/// Differential test of the `nosys` simulators (= Lean `Ext.Instr`) against the
/// executable Lean model on random single steps. Returns the number of cases.
pub fn lean_oracle(n: u64, lean_dir: &str, seed: u64) -> Result<u64> {
    let engine = host::engine();
    let mem = Module::new(&engine, MEM_STRICT)?;
    let mut r = super::randprog::Rng::new(seed);
    let mut cases = vec![];
    let mut input = String::new();
    for _ in 0..n {
        let pc = 0x10000 + 4 * r.below(1024);
        let w = random_word(&mut r);
        let mut x = [0u64; 32];
        for v in x.iter_mut().skip(1) {
            *v = if r.below(3) == 0 {
                0x20000 + 8 * r.below(512) + [0, 0, 0, 1, 2, 4][r.below(6) as usize]
            } else {
                r.value()
            };
        }
        input.push_str(&format!(
            "{w} {pc} {}\n",
            x.iter()
                .map(|v| v.to_string())
                .collect::<Vec<_>>()
                .join(" ")
        ));
        cases.push((pc, w, x));
    }
    let script = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../examples/wasm-sim/rv64/lean/StepOracle.lean")
        .canonicalize()?;
    let mut child = std::process::Command::new("lake")
        .args(["env", "lean", "--run"])
        .arg(&script)
        .current_dir(lean_dir)
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .spawn()?;
    {
        use std::io::Write;
        let mut stdin = child.stdin.take().unwrap();
        std::thread::spawn(move || stdin.write_all(input.as_bytes()));
    }
    let out = child.wait_with_output()?;
    let lines: Vec<String> = String::from_utf8_lossy(&out.stdout)
        .lines()
        .map(String::from)
        .collect();
    if lines.len() != cases.len() {
        bail!(
            "Lean oracle produced {} lines for {} cases",
            lines.len(),
            cases.len()
        );
    }
    let mut hist = std::collections::BTreeMap::new();
    for l in &lines {
        let tag = if l.starts_with('R') && !l.ends_with(" -") {
            "R+store"
        } else {
            l.split(' ').next().unwrap()
        };
        *hist.entry(tag).or_insert(0u64) += 1;
    }
    println!("     Lean outcomes: {hist:?}");
    for st in [State::G, State::M] {
        let m = Module::new(&engine, asm::build(&Config::new(st, "nosys"), ""))?;
        for (k, ((pc, w, x), lean)) in cases.iter().zip(&lines).enumerate() {
            let mut s = Sim::new(&engine, &m, &mem)?;
            s.env.data_mut(&mut s.store)[*pc as usize..*pc as usize + 4]
                .copy_from_slice(&w.to_le_bytes());
            for (i, &v) in x.iter().enumerate() {
                s.set(i as i32, v);
            }
            s.set(32, *pc);
            let status = s.step();
            let expect = match lean.split(' ').next().unwrap() {
                "R" => 0,
                "S" => 1,
                "U" => 2,
                _ => 3,
            };
            let mut ok = status == expect;
            if ok && status == 0 {
                let f: Vec<&str> = lean.split(' ').collect();
                let regs = s.regs();
                ok = f[1].parse::<u64>()? == regs[32]
                    && (1..32).all(|i| f[1 + i].parse::<u64>().unwrap() == regs[i]);
                if f[33] != "-"
                    && let Some(super::decode::Inst { rs1, imm, .. }) = super::decode::decode(*w)
                {
                    let a = (x[rs1 as usize].wrapping_add(imm as u64) & !7) as usize;
                    let d = &s.env.data(&s.store)[a..a + 8];
                    ok &= u64::from_le_bytes(d.try_into().unwrap()) == f[33].parse::<u64>()?;
                }
            }
            if !ok {
                bail!(
                    "case {k} ({st:?}): word {w:#010x} pc {pc:#x}: sim status {status} {:x?}\n  lean: {lean}",
                    s.regs()
                );
            }
        }
    }
    Ok(n)
}

/// Whole-program differential test against the Lean model (`lean/ProgOracle.lean`):
/// from the ELF image with all registers 0, run `nosys` (G and M) and
/// `Ext.MState.step` until the first non-retired outcome (for the test programs:
/// the first ECALL, undecodable for both) or `limit` steps; compare step count,
/// outcome class, pc, registers and an FNV hash of all segment bytes.
pub fn lean_prog(path: &str, lean_dir: &str, limit: u64) -> Result<u64> {
    let elf = super::elf::parse(&std::fs::read(path)?)?;
    let mut input = format!("{} {limit}\n", elf.entry);
    for sg in &elf.segments {
        let hex: String = sg.data.iter().map(|b| format!("{b:02x}")).collect();
        input.push_str(&format!(
            "{} {} {} {} {} {hex}\n",
            sg.vaddr,
            sg.memsz,
            (sg.flags >> 2) & 1,
            (sg.flags >> 1) & 1,
            sg.flags & 1
        ));
    }
    let script = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../examples/wasm-sim/rv64/lean/ProgOracle.lean")
        .canonicalize()?;
    let mut child = std::process::Command::new("lake")
        .args(["env", "lean", "--run"])
        .arg(&script)
        .current_dir(lean_dir)
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .spawn()?;
    {
        use std::io::Write;
        let mut stdin = child.stdin.take().unwrap();
        std::thread::spawn(move || stdin.write_all(input.as_bytes()));
    }
    let out = child.wait_with_output()?;
    let line = String::from_utf8_lossy(&out.stdout).trim().to_string();
    let f: Vec<&str> = line.split(' ').collect();
    if f.len() != 35 {
        bail!("{path}: Lean oracle output: {line:?}");
    }
    let engine = host::engine();
    for st in [State::G, State::M] {
        let mut s = sim_for(&engine, &Config::new(st, "nosys"), &elf)?;
        s.set(2, 0);
        let (status, n) = s.run(limit);
        let regs = s.regs();
        let class = match f[1] {
            "R" => 4,
            "S" => 1,
            "U" => 2,
            _ => 3,
        };
        let mut h = 0xcbf29ce484222325u64;
        for sg in &elf.segments {
            for &b in &s.env.data(&s.store)[sg.vaddr as usize..(sg.vaddr + sg.memsz) as usize] {
                h = (h ^ b as u64).wrapping_mul(0x100000001b3);
            }
        }
        let ok = n == f[0].parse::<u64>()?
            && status == class
            && regs[32] == f[2].parse::<u64>()?
            && (1..32).all(|i| regs[i] == f[2 + i].parse::<u64>().unwrap())
            && h == f[34].parse::<u64>()?;
        if !ok {
            bail!(
                "{path} ({st:?}): sim {n} steps status {status} regs {regs:x?} hash {h}\n  lean: {line}"
            );
        }
    }
    Ok(f[0].parse()?)
}
