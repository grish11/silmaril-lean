//! Route (b) of the glibc bridge (`examples/wasm-sim/glibc-bridge`, `route-b.sh`): run a
//! glibc-linked ELF on a Wasm simulator
//! with some of its glibc imports bound to the *real* glibc code (the pinned `libc.so.6`,
//! mapped and relocated in the simulated address space) and the rest bound to host
//! implementations (the Rust twins of `examples/wasm-sim/glibc-bridge/wat/glibc.wat`).
//!
//! Loader (eager binding, no `ld.so`):
//! * the program (ET_EXEC) as in [`super::elf`]; its imports: names in `in_sim` resolve to
//!   libc's definition, `__libc_start_main` to the start-up contract (START: `exit(main(argc,
//!   argv, envp))`, as `glibcrun.wat`), everything else to a foreign address (host function);
//! * `libc.so.6` at [`LIBC_BASE`]: RELR + RELATIVE, GLOB_DAT/JUMP_SLOT/64 to its own
//!   definitions; `ld.so`'s symbols (`_rtld_global`, `_rtld_global_ro`, `__libc_stack_end`,
//!   `_dl_argv`, `__libc_enable_secure`, `__tls_get_addr`, ...) to zero-filled fake objects
//!   (data) or foreign addresses (functions); IRELATIVE (ifuncs: `strlen`, `memcpy`, ...) to the
//!   foreign address of the ifunc's *name* (the resolver is not run: the callee becomes an
//!   import); TPOFF64 for a static TLS block whose thread pointer is [`TP`] (the simulators do
//!   not model `fs`, so this only matters once they do).
//!
//! The run steps the simulator's `step` export and performs foreign calls itself (as extrun),
//! logging every entry into an exported libc function, every foreign call and every syscall,
//! and stops at the first unsupported instruction (status 2), fault, or exit.

use super::elf::Elf;
use super::host::{self, EnvOpts, MemBackend, RAX, RDI, RIP, RSP};
use super::mem::Mem;
use std::collections::HashMap;
use wasmtime::error::Context;
use wasmtime::{Engine, Module, Result, bail};

pub const LIBC_BASE: u64 = 0x7e00_0000_0000;
pub const FAKE_BASE: u64 = 0x7d00_0000_0000;
pub const FAKE_SIZE: u64 = 0x1_0000;
pub const TP: u64 = 0x7c00_0001_0000;
pub const FOREIGN_BASE: u64 = 0x7f00_0000_0000;
const START: u64 = 0x7f00_00ff_0000;
const MAINRET: u64 = 0x7f00_00ff_0010;
const RSI: i32 = 6;
const RDX: i32 = 2;

fn rd(d: &[u8], o: usize, n: usize) -> u64 {
    let mut b = [0u8; 8];
    b[..n].copy_from_slice(&d[o..o + n]);
    u64::from_le_bytes(b)
}

fn cstr(d: &[u8], o: usize) -> String {
    let s = &d[o..];
    String::from_utf8_lossy(&s[..s.iter().position(|&b| b == 0).unwrap_or(s.len())]).into_owned()
}

/// A dynamic symbol: name, value, `st_info`, defined.
struct Sym {
    name: String,
    value: u64,
    info: u8,
    defined: bool,
}

/// `.dynsym` of a file (via section headers).
fn dynsyms(d: &[u8]) -> Vec<Sym> {
    let (shoff, shn) = (rd(d, 40, 8) as usize, rd(d, 60, 2) as usize);
    let mut out = vec![];
    for i in 0..shn {
        let s = shoff + 64 * i;
        if rd(d, s + 4, 4) != 11 {
            continue;
        }
        let (off, size, link) = (
            rd(d, s + 24, 8) as usize,
            rd(d, s + 32, 8) as usize,
            rd(d, s + 40, 4) as usize,
        );
        let strs = rd(d, shoff + 64 * link + 24, 8) as usize;
        for k in 0..size / 24 {
            let e = off + 24 * k;
            out.push(Sym {
                name: cstr(d, strs + rd(d, e, 4) as usize),
                value: rd(d, e + 8, 8),
                info: d[e + 4],
                defined: rd(d, e + 6, 2) != 0,
            });
        }
    }
    out
}

/// Map the PT_LOAD segments of `d` at `base`; returns (PT_DYNAMIC vaddr, PT_TLS (vaddr,
/// filesz, memsz, align), end).
fn map(mem: &mut Mem, d: &[u8], base: u64) -> Result<(Option<u64>, Option<[u64; 4]>, u64)> {
    let elf = Elf::parse(d)?;
    let (mut dyn_, mut tls, mut end) = (None, None, 0);
    for p in elf.phdrs()? {
        match p.ty {
            1 => {
                mem.map(base + p.vaddr, p.memsz);
                mem.write_bytes(
                    base + p.vaddr,
                    &d[p.offset as usize..(p.offset + p.filesz) as usize],
                )
                .context("map")?;
                end = end.max(base + p.vaddr + p.memsz);
            }
            2 => dyn_ = Some(p.vaddr),
            7 => {
                let ph = rd(d, 32, 8) as usize
                    + 56 * elf.phdrs()?.iter().position(|q| q.ty == 7).unwrap();
                tls = Some([p.vaddr, p.filesz, p.memsz, rd(d, ph + 48, 8)]);
            }
            _ => {}
        }
    }
    Ok((dyn_, tls, end))
}

/// The dynamic tags of a mapped object.
fn dyn_tags(mem: &Mem, mut a: u64) -> HashMap<u64, u64> {
    let mut t = HashMap::new();
    loop {
        let (tag, val) = (mem.load(a, 8).unwrap(), mem.load(a + 8, 8).unwrap());
        if tag == 0 {
            return t;
        }
        t.insert(tag, val);
        a += 16;
    }
}

/// Where an import goes.
#[derive(Default)]
pub struct Binder {
    /// foreign function names, index i at FOREIGN_BASE + 16 i
    pub foreign: Vec<String>,
    /// fake data objects of ld.so: name -> address
    pub fake: Vec<(String, u64)>,
}

impl Binder {
    fn foreign(&mut self, name: &str) -> u64 {
        let i = match self.foreign.iter().position(|n| n == name) {
            Some(i) => i,
            None => {
                self.foreign.push(name.to_string());
                self.foreign.len() - 1
            }
        };
        FOREIGN_BASE + 16 * i as u64
    }
    fn fake(&mut self, mem: &mut Mem, name: &str) -> u64 {
        if let Some((_, a)) = self.fake.iter().find(|(n, _)| n == name) {
            return *a;
        }
        let a = FAKE_BASE + FAKE_SIZE * self.fake.len() as u64;
        mem.map(a, FAKE_SIZE);
        self.fake.push((name.to_string(), a));
        a
    }
}

/// Relocate a mapped object (RELR, RELA, JMPREL) with `resolve(name, is_func, mem, binder)`
/// for undefined symbols.
#[allow(clippy::too_many_arguments)]
fn relocate(
    mem: &mut Mem,
    base: u64,
    dynv: u64,
    syms: &[Sym],
    tls_off: u64,
    binder: &mut Binder,
    resolve: &dyn Fn(&str, bool, &mut Mem, &mut Binder) -> Result<u64>,
) -> Result<HashMap<u64, usize>> {
    let t = dyn_tags(mem, base + dynv);
    let mut counts: HashMap<u64, usize> = HashMap::new();
    if let (Some(&relr), Some(&sz)) = (t.get(&36), t.get(&35)) {
        let mut where_ = 0u64;
        for k in 0..sz / 8 {
            let e = mem.load(base + relr + 8 * k, 8).unwrap();
            if e & 1 == 0 {
                let a = base + e;
                let v = mem.load(a, 8).unwrap();
                mem.store(a, 8, v + base);
                where_ = e + 8;
            } else {
                let mut bits = e >> 1;
                let mut i = 0;
                while bits != 0 {
                    if bits & 1 != 0 {
                        let a = base + where_ + 8 * i;
                        let v = mem.load(a, 8).unwrap();
                        mem.store(a, 8, v + base);
                    }
                    bits >>= 1;
                    i += 1;
                }
                where_ += 63 * 8;
            }
            *counts.entry(38).or_default() += 1;
        }
    }
    let ifuncs: HashMap<u64, &str> = syms
        .iter()
        .filter(|s| s.info & 15 == 10 && s.defined)
        .map(|s| (s.value, s.name.as_str()))
        .collect();
    for (tr, ts) in [(7u64, 8u64), (23, 2)] {
        let (Some(&rela), Some(&size)) = (t.get(&tr), t.get(&ts)) else {
            continue;
        };
        for r in (rela..rela + size).step_by(24) {
            let (off, info, add) = (
                mem.load(base + r, 8).unwrap(),
                mem.load(base + r + 8, 8).unwrap(),
                mem.load(base + r + 16, 8).unwrap(),
            );
            let (ty, si) = (info & 0xffff_ffff, (info >> 32) as usize);
            *counts.entry(ty).or_default() += 1;
            let sym = syms.get(si);
            let v = match ty {
                8 => base + add,
                1 | 6 | 7 => {
                    let s = sym.context("symbol index")?;
                    let a = if s.defined {
                        base + s.value
                    } else if s.info >> 4 == 2 && s.name.starts_with("__gmon") {
                        0
                    } else {
                        resolve(&s.name, s.info & 15 == 2, mem, binder)?
                    };
                    if ty == 1 { a.wrapping_add(add) } else { a }
                }
                37 => {
                    let n = ifuncs.get(&add).copied().unwrap_or("?ifunc");
                    binder.foreign(&format!("ifunc:{n}"))
                }
                18 => {
                    let s = sym.map(|s| s.value).unwrap_or(0);
                    s.wrapping_add(add).wrapping_sub(tls_off)
                }
                ty => bail!("unsupported relocation type {ty} at {off:#x}"),
            };
            mem.store(base + off, 8, v).context("relocation target")?;
        }
    }
    Ok(counts)
}

/// The result of a run.
#[derive(Default)]
pub struct Report {
    pub out: Vec<u8>,
    pub exit: Option<i32>,
    pub stop: String,
    pub steps: u64,
    pub libc_steps: u64,
    /// events: libc entries, foreign calls, syscalls, in order
    pub log: Vec<String>,
    pub relocs: String,
}

/// Run `prog` with the imports in `in_sim` bound to the real libc code.
// The CLI's run options, passed through one to one.
#[allow(clippy::too_many_arguments)]
pub fn run(
    engine: &Engine,
    sim: &Module,
    prog: &[u8],
    libc: &[u8],
    argv: &[Vec<u8>],
    in_sim: &[String],
    max_steps: u64,
    fs_emul: bool,
    imports: &[String],
) -> Result<Report> {
    let mut mem = Mem::default();
    let mut b = Binder::default();
    // libc
    let lsyms = dynsyms(libc);
    let (ldyn, ltls, _) = map(&mut mem, libc, LIBC_BASE)?;
    // static TLS: [TP - align_up(memsz, align), TP); TCB at TP (self pointer at TP and TP+16)
    let tls_off = match ltls {
        Some([va, fsz, msz, al]) => {
            let off = msz.div_ceil(al.max(1)) * al.max(1);
            mem.map(TP - off, off + 0x1000);
            let init = mem.read_bytes(LIBC_BASE + va, fsz as usize).unwrap();
            mem.write_bytes(TP - off, &init);
            mem.store(TP, 8, TP);
            mem.store(TP + 16, 8, TP);
            off
        }
        None => 0,
    };
    let lcounts = relocate(
        &mut mem,
        LIBC_BASE,
        ldyn.context("libc: no PT_DYNAMIC")?,
        &lsyms,
        tls_off,
        &mut b,
        &|name, is_func, mem, b| {
            Ok(if is_func {
                b.foreign(name)
            } else {
                b.fake(mem, name)
            })
        },
    )?;
    let defs: HashMap<&str, u64> = lsyms
        .iter()
        .filter(|s| s.defined && s.info & 15 == 2)
        .map(|s| (s.name.as_str(), LIBC_BASE + s.value))
        .collect();
    // program: segments, stack, auxv (elf::load), with our own binding
    let pelf = Elf::parse(prog)?;
    let psyms = dynsyms(prog);
    let img = {
        // elf::load relocates with the process stack's table; map a copy without PT_DYNAMIC instead
        let mut p2 = prog.to_vec();
        let phoff = rd(prog, 32, 8) as usize;
        for (i, p) in pelf.phdrs()?.iter().enumerate() {
            if p.ty == 2 {
                // PT_DYNAMIC -> PT_GNU_STACK (ignored by elf::load)
                p2[phoff + 56 * i..phoff + 56 * i + 4]
                    .copy_from_slice(&0x6474_e551u32.to_le_bytes());
            }
        }
        super::elf::load(&mut mem, &p2, argv, &[])?
    };
    let pdyn = pelf.phdrs()?.iter().find(|p| p.ty == 2).map(|p| p.vaddr);
    let pcounts = relocate(
        &mut mem,
        0,
        pdyn.context("program: not dynamically linked")?,
        &psyms,
        0,
        &mut b,
        &|name, _, _, b| {
            Ok(if name == "__libc_start_main" {
                START
            } else if in_sim.iter().any(|n| n == name) {
                *defs
                    .get(name)
                    .with_context(|| format!("libc does not define {name}"))?
            } else {
                b.foreign(name)
            })
        },
    )?;
    let fake = |n: &str| b.fake.iter().find(|(m, _)| m == n).map(|x| x.1);
    // ld.so data the libc code reads: __libc_stack_end, _dl_argv (pointers), page size
    if let Some(a) = fake("__libc_stack_end") {
        mem.store(a, 8, img.sp);
    }
    let mut r = Report {
        relocs: format!("libc {lcounts:?}; program {pcounts:?}"),
        ..Default::default()
    };
    // environment and simulator
    let opts = EnvOpts {
        wasm_mem: None,
        wasm_ext: None,
        extrun: None,
    };
    let (mut store, mut linker) = host::env(engine, &opts)?;
    store.data_mut().mem = MemBackend::Host(mem);
    store.data_mut().brk = img.brk;
    store.data_mut().brk0 = img.brk;
    let s = host::instantiate_sim(&mut store, &mut linker, sim)?;
    for l in 0..24 {
        s.set.call(&mut store, (l, 0))?;
    }
    s.set.call(&mut store, (RSP, img.sp as i64))?;
    s.set.call(&mut store, (RIP, img.entry as i64))?;
    let fnames: HashMap<u64, &str> = lsyms
        .iter()
        .filter(|s| s.defined && s.info & 15 == 2)
        .map(|s| (LIBC_BASE + s.value, s.name.as_str()))
        .collect();
    let libc_end = LIBC_BASE + 0x40_0000;
    let mut nsys = 0;
    let mut sysnr = 0u64;
    let get = |st: &mut wasmtime::Store<host::Proc>, l: i32| s.get.call(st, l).map(|v| v as u64);
    while r.steps < max_steps {
        let rip = get(&mut store, RIP)?;
        if let Some(c) = store.data().exit {
            r.exit = Some(c);
            r.stop = "exit".into();
            break;
        }
        let ns = store.data().stats.syscalls;
        if ns != nsys {
            nsys = ns;
            r.log.push(format!(
                "syscall nr {sysnr} -> {:#x}",
                get(&mut store, RAX)?
            ));
        }
        if let Some(n) = fnames.get(&rip) {
            r.log.push(format!("libc {n}"));
        }
        if rip == START {
            let (argc, argv) = (get(&mut store, RSI)?, get(&mut store, RDX)?);
            let main = get(&mut store, RDI)?;
            s.set.call(&mut store, (RIP, main as i64))?;
            s.set.call(&mut store, (RDI, argc as i64))?;
            s.set.call(&mut store, (RSI, argv as i64))?;
            s.set
                .call(&mut store, (RDX, (argv + 8 * (argc + 1)) as i64))?;
            let sp = get(&mut store, RSP)?;
            host::mstore(&mut store, sp, 8, MAINRET)?;
            r.log.push("start: main(argc, argv, envp)".into());
            continue;
        }
        if rip == MAINRET && in_sim.iter().any(|n| n == "exit") {
            // glibc's own exit(rax) in the simulator (atexit handlers, stdio flush, _exit)
            let v = get(&mut store, RAX)?;
            r.log.push(format!("main returned {v:#x}: libc exit"));
            s.set.call(&mut store, (RDI, v as i64))?;
            s.set.call(&mut store, (RIP, defs["exit"] as i64))?;
            let sp = get(&mut store, RSP)? - 8;
            s.set.call(&mut store, (RSP, sp as i64))?;
            host::mstore(&mut store, sp, 8, host::SENTINEL)?;
            continue;
        }
        if let Some(n) = fnames.get(&rip)
            && imports.iter().any(|f| f == n)
        {
            // an internal libc function bound to an import (callee as import)
            let a: Vec<u64> = [RDI, RSI, RDX]
                .iter()
                .map(|&l| get(&mut store, l))
                .collect::<Result<_>>()?;
            r.log
                .push(format!("import {n}({:#x}, {:#x}, {:#x})", a[0], a[1], a[2]));
            let Some(v) = host_fn(&mut store, n, &a)? else {
                r.stop = format!("no host function {n}");
                break;
            };
            s.set.call(&mut store, (RAX, v as i64))?;
            let sp = get(&mut store, RSP)?;
            let ret = host::mload(&mut store, sp, 8)?;
            s.set.call(&mut store, (RIP, ret as i64))?;
            s.set.call(&mut store, (RSP, (sp + 8) as i64))?;
            continue;
        }
        if rip == MAINRET {
            let v = get(&mut store, RAX)?;
            r.log.push(format!("main returned {v:#x}: exit"));
            r.exit = Some((v & 255) as i32);
            r.stop = "exit (main returned)".into();
            break;
        }
        if (FOREIGN_BASE..FOREIGN_BASE + 0x10000).contains(&rip) {
            let name = b.foreign[((rip - FOREIGN_BASE) / 16) as usize].clone();
            let a: Vec<u64> = [RDI, RSI, RDX]
                .iter()
                .map(|&l| get(&mut store, l))
                .collect::<Result<_>>()?;
            r.log.push(format!(
                "foreign {name}({:#x}, {:#x}, {:#x})",
                a[0], a[1], a[2]
            ));
            let Some(v) = host_fn(&mut store, &name, &a)? else {
                r.stop = format!("unbound foreign function {name}");
                break;
            };
            if let Some(c) = store.data().exit {
                r.exit = Some(c);
                r.stop = format!("exit via {name}");
                break;
            }
            s.set.call(&mut store, (RAX, v as i64))?;
            let sp = get(&mut store, RSP)?;
            let ret = host::mload(&mut store, sp, 8)?;
            s.set.call(&mut store, (RIP, ret as i64))?;
            s.set.call(&mut store, (RSP, (sp + 8) as i64))?;
            continue;
        }
        if (LIBC_BASE..libc_end).contains(&rip) {
            r.libc_steps += 1;
        }
        if let MemBackend::Host(m) = &store.data().mem
            && m.read_bytes(rip, 2).as_deref() == Some(&[0x0f, 0x05][..])
        {
            sysnr = get(&mut store, RAX)?;
        }
        match s.step.call(&mut store, ()) {
            Ok(0) => r.steps += 1,
            Ok(st) => {
                let rip = get(&mut store, RIP)?;
                let bytes = match &store.data().mem {
                    MemBackend::Host(m) => m.read_bytes(rip, 15).unwrap_or_default(),
                    _ => vec![],
                };
                if fs_emul
                    && st == 2
                    && let Some(d) = fs_step(&mut store, &s, rip, &bytes)?
                {
                    r.log.push(format!("fs-ext {} at {}", d, where_(rip)));
                    r.steps += 1;
                    continue;
                }
                r.stop = format!("status {st} at {} : {}", where_(rip), disasm(rip, &bytes));
                break;
            }
            Err(e) => {
                let rip = get(&mut store, RIP)?;
                r.stop = format!("trap at {}: {e}", where_(rip));
                break;
            }
        }
    }
    if r.stop.is_empty() {
        r.stop = format!("fuel ({max_steps} steps)");
    }
    if let Some(c) = store.data().exit {
        r.exit = Some(c);
    }
    r.out = std::mem::take(&mut store.data_mut().out);
    Ok(r)
}

/// `--fs`: a driver-level extension for the `fs`-relative absolute `mov` forms the simulators
/// lack (status 2): `mov r, %fs:d` / `mov %fs:d, r` (8/16/32/64-bit) with the thread pointer
/// [`TP`]. Returns the instruction text if it emulated one.
fn fs_step(
    st: &mut wasmtime::Store<host::Proc>,
    s: &host::Sim,
    rip: u64,
    bytes: &[u8],
) -> Result<Option<String>> {
    use iced_x86::{Code, Decoder, DecoderOptions, Mnemonic, OpKind, Register};
    let mut d = Decoder::with_ip(64, bytes, rip, DecoderOptions::NONE);
    let i = d.decode();
    if i.mnemonic() == Mnemonic::Cmpxchg
        && i.op0_kind() == OpKind::Memory
        && i.memory_segment() != Register::FS
    {
        return cmpxchg(st, s, rip, &i).map(|ok| ok.then(|| disasm(rip, bytes)));
    }
    if i.code() == Code::INVALID
        || i.memory_segment() != Register::FS
        || !matches!(i.mnemonic(), Mnemonic::Mov | Mnemonic::Sub | Mnemonic::Cmp)
    {
        return Ok(None);
    }
    const GPR: [Register; 16] = [
        Register::RAX,
        Register::RCX,
        Register::RDX,
        Register::RBX,
        Register::RSP,
        Register::RBP,
        Register::RSI,
        Register::RDI,
        Register::R8,
        Register::R9,
        Register::R10,
        Register::R11,
        Register::R12,
        Register::R13,
        Register::R14,
        Register::R15,
    ];
    let loc = |r: Register| {
        GPR.iter()
            .position(|&g| g == r.full_register())
            .map(|x| x as i32)
    };
    let mut a = TP.wrapping_add(i.memory_displacement64());
    for (r, k) in [
        (i.memory_base(), 1u64),
        (i.memory_index(), i.memory_index_scale() as u64),
    ] {
        if r != Register::None {
            let Some(l) = loc(r) else { return Ok(None) };
            a = a.wrapping_add((s.get.call(&mut *st, l)? as u64).wrapping_mul(k));
        }
    }
    let next = rip + i.len() as u64;
    match (i.op0_kind(), i.op1_kind()) {
        (OpKind::Register, OpKind::Memory) if i.mnemonic() != Mnemonic::Mov => {
            // sub/cmp r, %fs:m (the stack-protector check): CF ZF SF OF
            let r = i.op0_register();
            let Some(l) = loc(r) else { return Ok(None) };
            let n = r.size();
            if n != 8 && n != 4 {
                return Ok(None);
            }
            let mask = if n == 8 { u64::MAX } else { 0xffff_ffff };
            let x = s.get.call(&mut *st, l)? as u64 & mask;
            let m = host::mload(&mut *st, a, n)?;
            let res = x.wrapping_sub(m) & mask;
            let sign = |v: u64| (v >> (8 * n - 1)) & 1;
            let of = (sign(x) != sign(m)) && (sign(res) != sign(x));
            for (g, v) in [(17, x < m), (20, res == 0), (21, sign(res) == 1), (22, of)] {
                s.set.call(&mut *st, (g, v as i64))?;
            }
            if i.mnemonic() == Mnemonic::Sub {
                s.set.call(&mut *st, (l, res as i64))?;
            }
        }
        (OpKind::Register, OpKind::Memory) => {
            let r = i.op0_register();
            let Some(l) = loc(r) else { return Ok(None) };
            let n = r.size();
            let v = host::mload(&mut *st, a, n)?;
            let v = if n == 4 || n == 8 {
                v
            } else {
                (s.get.call(&mut *st, l)? as u64 & !((1u64 << (8 * n)) - 1)) | v
            };
            s.set.call(&mut *st, (l, v as i64))?;
        }
        (
            OpKind::Memory,
            OpKind::Immediate8
            | OpKind::Immediate16
            | OpKind::Immediate32
            | OpKind::Immediate32to64,
        ) => {
            host::mstore(&mut *st, a, i.memory_size().size(), i.immediate(1))?;
        }
        (OpKind::Memory, OpKind::Register) => {
            let r = i.op1_register();
            let Some(l) = loc(r) else { return Ok(None) };
            let v = s.get.call(&mut *st, l)? as u64;
            host::mstore(&mut *st, a, r.size(), v)?;
        }
        _ => return Ok(None),
    }
    s.set.call(&mut *st, (RIP, next as i64))?;
    Ok(Some(disasm(rip, bytes)))
}

const GPRS: [iced_x86::Register; 16] = {
    use iced_x86::Register::*;
    [
        RAX, RCX, RDX, RBX, RSP, RBP, RSI, RDI, R8, R9, R10, R11, R12, R13, R14, R15,
    ]
};

/// `[lock] cmpxchg m, r` (32/64-bit; single thread, so `lock` is irrelevant): ZF and `rax`/`m`
/// as the SDM says; CF/SF/OF as `cmp rax, m` (PF/AF are unmodelled).
fn cmpxchg(
    st: &mut wasmtime::Store<host::Proc>,
    s: &host::Sim,
    rip: u64,
    i: &iced_x86::Instruction,
) -> Result<bool> {
    use iced_x86::Register;
    let loc = |r: Register| {
        GPRS.iter()
            .position(|&g| g == r.full_register())
            .map(|x| x as i32)
    };
    let mut a = i.memory_displacement64();
    if i.memory_base() == Register::RIP {
        a = i.memory_displacement64();
    } else if i.memory_base() != Register::None {
        let Some(l) = loc(i.memory_base()) else {
            return Ok(false);
        };
        a = a.wrapping_add(s.get.call(&mut *st, l)? as u64);
    }
    if i.memory_index() != Register::None {
        let Some(l) = loc(i.memory_index()) else {
            return Ok(false);
        };
        a = a.wrapping_add((s.get.call(&mut *st, l)? as u64) * i.memory_index_scale() as u64);
    }
    let src = i.op1_register();
    let (n, Some(ls)) = (src.size(), loc(src)) else {
        return Ok(false);
    };
    if n != 4 && n != 8 {
        return Ok(false);
    }
    let mask = if n == 8 { u64::MAX } else { 0xffff_ffff };
    let acc = s.get.call(&mut *st, 0)? as u64 & mask;
    let m = host::mload(&mut *st, a, n)?;
    let r = acc.wrapping_sub(m) & mask;
    let sign = |x: u64| (x >> (8 * n - 1)) & 1;
    let (cf, zf, sf) = ((acc < m) as i64, (acc == m) as i64, sign(r) as i64);
    let of = ((sign(acc) != sign(m)) && (sign(r) != sign(acc))) as i64;
    if acc == m {
        let v = s.get.call(&mut *st, ls)? as u64 & mask;
        host::mstore(&mut *st, a, n, v)?;
    } else {
        s.set.call(&mut *st, (0, m as i64))?;
    }
    for (l, v) in [(17, cf), (20, zf), (21, sf), (22, of)] {
        s.set.call(&mut *st, (l, v))?;
    }
    s.set.call(&mut *st, (RIP, (rip + i.len() as u64) as i64))?;
    Ok(true)
}

fn where_(rip: u64) -> String {
    if (LIBC_BASE..LIBC_BASE + 0x40_0000).contains(&rip) {
        format!("libc.so.6+{:#x}", rip - LIBC_BASE)
    } else {
        format!("{rip:#x}")
    }
}

fn disasm(rip: u64, bytes: &[u8]) -> String {
    use iced_x86::{Decoder, DecoderOptions, Formatter, GasFormatter};
    let mut d = Decoder::with_ip(64, bytes, rip, DecoderOptions::NONE);
    let i = d.decode();
    let mut s = String::new();
    GasFormatter::new().format(&i, &mut s);
    let hex: Vec<String> = bytes[..i.len().min(bytes.len())]
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect();
    format!("{s}  [{}]", hex.join(" "))
}

/// The host implementations of foreign functions (the twins of glibc.wasm); `None` if unknown.
fn host_fn(st: &mut wasmtime::Store<host::Proc>, name: &str, a: &[u64]) -> Result<Option<u64>> {
    let n = name.strip_prefix("ifunc:").unwrap_or(name);
    let rdc = |st: &mut wasmtime::Store<host::Proc>, p: u64| -> Result<Vec<u8>> {
        let mut v = vec![];
        loop {
            match host::mload(&mut *st, p + v.len() as u64, 1)? as u8 {
                0 => return Ok(v),
                c => v.push(c),
            }
        }
    };
    Ok(Some(match n {
        "strlen" => rdc(st, a[0])?.len() as u64,
        "strchrnul" | "strchr" => {
            let s = rdc(st, a[0])?;
            match s.iter().position(|&c| c == a[1] as u8) {
                Some(i) => a[0] + i as u64,
                None if a[1] as u8 == 0 || n == "strchrnul" => a[0] + s.len() as u64,
                None => 0,
            }
        }
        "memcpy" | "memmove" | "mempcpy" | "__mempcpy" => {
            let v = host::read_bytes(&mut *st, a[1], a[2])?;
            for (i, c) in v.iter().enumerate() {
                host::mstore(&mut *st, a[0] + i as u64, 1, *c as u64)?;
            }
            if n.contains("mempcpy") {
                a[0] + a[2]
            } else {
                a[0]
            }
        }
        "memset" => {
            for i in 0..a[2] {
                host::mstore(&mut *st, a[0] + i, 1, a[1] & 255)?;
            }
            a[0]
        }
        "puts" => {
            let mut s = rdc(st, a[0])?;
            s.push(b'\n');
            st.data_mut().out.extend_from_slice(&s);
            s.len() as u64
        }
        "write" => {
            let v = host::read_bytes(&mut *st, a[1], a[2])?;
            if a[0] == 1 {
                st.data_mut().out.extend_from_slice(&v);
            }
            a[2]
        }
        "malloc" | "__libc_malloc" => {
            // bump allocator in [HEAP, HEAP + 64 MiB)
            const HEAP: u64 = 0x7b00_0000_0000;
            let p = st.data().ffi_ret.max(HEAP).div_ceil(16) * 16;
            host::mmap(&mut *st, p, a[0].max(1))?;
            st.data_mut().ffi_ret = p + a[0];
            p
        }
        "exit" | "_exit" => {
            st.data_mut().exit = Some((a[0] & 255) as i32);
            0
        }
        _ => return Ok(None),
    }))
}

/// Print a report.
pub fn print(r: &Report, verbose: bool) {
    eprintln!("relocations: {}", r.relocs);
    let shown: Vec<&String> = if verbose {
        r.log.iter().collect()
    } else {
        r.log
            .iter()
            .filter(|l| !l.starts_with("libc ") || l.len() < 40)
            .collect()
    };
    for l in shown {
        eprintln!("  {l}");
    }
    eprintln!(
        "steps: {} ({} in libc.so.6); stop: {}; exit: {:?}; stdout: {:?}",
        r.steps,
        r.libc_steps,
        r.stop,
        r.exit,
        String::from_utf8_lossy(&r.out)
    );
}
