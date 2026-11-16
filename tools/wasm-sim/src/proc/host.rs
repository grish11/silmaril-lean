//! wasmtime embedding of the process model: the environment of a simulator
//! (`mem.*`, `sys.syscall`, `nd.undef`, `ext.call`) implemented in Rust, or partly by
//! Wasm modules (`mem.wasm`), and a launcher for ELF files.

use super::elf::{self, EXT_BASE, FOREIGN, Image};
use super::mem::Mem;
use wasmtime::error::Context;
use wasmtime::{AsContextMut, Caller, Engine, Instance, Linker, Module, Store, TypedFunc};
use wasmtime::{Result, format_err as anyhow};

/// Locations (docs/projects/wasm-sim-abi.md).
pub const RAX: i32 = 0;
pub const RSP: i32 = 4;
pub const RDI: i32 = 7;
pub const RIP: i32 = 16;
pub const SENTINEL: u64 = 0xFFFF_FFFF_FFFF_F000;

#[derive(Clone)]
pub struct WasmMem {
    pub load: [TypedFunc<i64, i64>; 4],
    pub store: [TypedFunc<(i64, i64), ()>; 4],
    pub map: TypedFunc<(i64, i64), i32>,
}

// One value per process: the size difference between the variants does not matter.
#[allow(clippy::large_enum_variant)]
pub enum MemBackend {
    Host(Mem),
    Wasm(WasmMem),
}

/// Exports of a simulator instance used by the host.
#[derive(Clone)]
pub struct Sim {
    pub get: TypedFunc<i32, i64>,
    pub set: TypedFunc<(i32, i64), ()>,
    pub step: TypedFunc<(), i32>,
    pub run: TypedFunc<i64, i32>,
    pub set_ext: Option<TypedFunc<(i64, i64), ()>>,
    pub instance: Instance,
}

impl Sim {
    pub fn new(store: &mut Store<Proc>, instance: Instance) -> Result<Self> {
        Ok(Sim {
            get: instance.get_typed_func(&mut *store, "get")?,
            set: instance.get_typed_func(&mut *store, "set")?,
            step: instance.get_typed_func(&mut *store, "step")?,
            run: instance.get_typed_func(&mut *store, "run")?,
            set_ext: instance.get_typed_func(&mut *store, "set_ext").ok(),
            instance,
        })
    }
}

#[derive(Default, Debug, Clone, Copy)]
pub struct Stats {
    pub syscalls: u64,
    pub ext_calls: u64,
}

/// Store data: the process environment.
pub struct Proc {
    pub mem: MemBackend,
    pub brk: u64,
    pub brk0: u64,
    pub out: Vec<u8>,
    /// Also copy fd 1/2 output to the host's stdout/stderr.
    pub echo: bool,
    pub exit: Option<i32>,
    pub sim: Option<Sim>,
    pub stats: Stats,
    pub ffi_ret: u64,
}

impl Proc {
    pub fn new(mem: MemBackend) -> Self {
        Proc {
            mem,
            brk: 0,
            brk0: 0,
            out: vec![],
            echo: false,
            exit: None,
            sim: None,
            stats: Stats::default(),
            ffi_ret: 0,
        }
    }
}

fn idx(n: usize) -> usize {
    match n {
        1 => 0,
        2 => 1,
        4 => 2,
        _ => 3,
    }
}

/// Load `n` bytes of process memory (either backend).
pub fn mload(mut cx: impl AsContextMut<Data = Proc>, a: u64, n: usize) -> Result<u64> {
    let mut cx = cx.as_context_mut();
    let f = match &cx.data().mem {
        MemBackend::Host(m) => {
            return m
                .load(a, n)
                .ok_or_else(|| anyhow!("fault: load{} at {a:#x}", 8 * n));
        }
        MemBackend::Wasm(w) => w.load[idx(n)].clone(),
    };
    Ok(f.call(&mut cx, a as i64)? as u64)
}

pub fn mstore(mut cx: impl AsContextMut<Data = Proc>, a: u64, n: usize, v: u64) -> Result<()> {
    let mut cx = cx.as_context_mut();
    let f = match &mut cx.data_mut().mem {
        MemBackend::Host(m) => {
            return m
                .store(a, n, v)
                .ok_or_else(|| anyhow!("fault: store{} at {a:#x}", 8 * n));
        }
        MemBackend::Wasm(w) => w.store[idx(n)].clone(),
    };
    f.call(&mut cx, (a as i64, v as i64))
}

pub fn mmap(mut cx: impl AsContextMut<Data = Proc>, a: u64, len: u64) -> Result<()> {
    let mut cx = cx.as_context_mut();
    let f = match &mut cx.data_mut().mem {
        MemBackend::Host(m) => {
            m.map(a, len);
            return Ok(());
        }
        MemBackend::Wasm(w) => w.map.clone(),
    };
    f.call(&mut cx, (a as i64, len as i64)).map(drop)
}

pub fn read_bytes(mut cx: impl AsContextMut<Data = Proc>, a: u64, len: u64) -> Result<Vec<u8>> {
    let mut cx = cx.as_context_mut();
    if let MemBackend::Host(m) = &cx.data().mem {
        return m
            .read_bytes(a, len as usize)
            .ok_or_else(|| anyhow!("fault: read at {a:#x}"));
    }
    (0..len)
        .map(|i| mload(&mut cx, a.wrapping_add(i), 1).map(|b| b as u8))
        .collect()
}

fn read_cstr(mut cx: impl AsContextMut<Data = Proc>, a: u64) -> Result<Vec<u8>> {
    let mut cx = cx.as_context_mut();
    let mut out = vec![];
    loop {
        match mload(&mut cx, a.wrapping_add(out.len() as u64), 1)? as u8 {
            0 => return Ok(out),
            b => out.push(b),
        }
    }
}

fn emit(p: &mut Proc, fd: u64, bytes: &[u8]) {
    use std::io::Write;
    if fd == 1 {
        p.out.extend_from_slice(bytes);
    }
    if p.echo {
        let _ = if fd == 2 {
            std::io::stderr().write_all(bytes)
        } else {
            std::io::stdout().write_all(bytes)
        };
    }
}

/// One Linux system call (x86-64 numbers): write, exit, exit_group, brk; -ENOSYS otherwise.
pub fn syscall(mut cx: Caller<'_, Proc>, nr: u64, a: [u64; 6]) -> Result<u64> {
    cx.data_mut().stats.syscalls += 1;
    Ok(match nr {
        1 => {
            if a[0] != 1 && a[0] != 2 {
                (-9i64) as u64
            } else {
                let n = a[2].min(1 << 20);
                let bytes = read_bytes(&mut cx, a[1], n)?;
                emit(cx.data_mut(), a[0], &bytes);
                n
            }
        }
        60 | 231 => {
            cx.data_mut().exit = Some((a[0] & 255) as i32);
            0
        }
        12 => {
            let (cur, b0) = (cx.data().brk, cx.data().brk0);
            if a[0] > cur {
                mmap(&mut cx, cur, a[0] - cur)?;
                cx.data_mut().brk = a[0];
            } else if a[0] >= b0 {
                cx.data_mut().brk = a[0];
            }
            cx.data().brk
        }
        _ => (-38i64) as u64,
    })
}

/// The host "libc": function `i` of `FOREIGN` with first argument `rdi`; `None` if unknown.
fn host_libc_c(cx: &mut Caller<'_, Proc>, i: u64, rdi: u64) -> Result<Option<u64>> {
    cx.data_mut().stats.ext_calls += 1;
    Ok(Some(match FOREIGN.get(i as usize).copied() {
        Some("puts") => {
            let mut s = read_cstr(&mut *cx, rdi)?;
            s.push(b'\n');
            emit(cx.data_mut(), 1, &s);
            s.len() as u64
        }
        Some("strlen") => read_cstr(&mut *cx, rdi)?.len() as u64,
        Some("putchar") => {
            emit(cx.data_mut(), 1, &[rdi as u8]);
            rdi & 0xff
        }
        _ => return Ok(None),
    }))
}

/// The simulator ABI's `ext.call` (callback style): arguments and results go through the simulator's
/// `get`/`set` (SysV: rdi in, rax out); the simulator performs `ret`.
pub fn ext_call(mut cx: Caller<'_, Proc>, target: u64) -> Result<i32> {
    let sim = cx
        .data()
        .sim
        .clone()
        .context("ext.call before the simulator is registered")?;
    let rdi = sim.get.call(&mut cx, RDI)? as u64;
    let Some(rax) = host_libc_c(&mut cx, target.wrapping_sub(EXT_BASE) / 16, rdi)? else {
        return Ok(2);
    };
    sim.set.call(&mut cx, (RAX, rax as i64))?;
    Ok(0)
}

pub struct EnvOpts {
    /// Use a Wasm memory model (`mem.wasm`) instead of the host one.
    pub wasm_mem: Option<std::path::PathBuf>,
    /// Use a Wasm foreign library for the `ffi` interface (e.g. `libc.wasm`, which imports
    /// `mem.*`, `io.memory` and WASI `fd_write`) instead of the host one.
    pub wasm_ext: Option<std::path::PathBuf>,
    /// `extrun.wasm`: foreign-call driver used when the simulator has no `set_ext` of its own.
    pub extrun: Option<std::path::PathBuf>,
}

/// Build a store and a linker providing the simulator's imports.
pub fn env(engine: &Engine, opts: &EnvOpts) -> Result<(Store<Proc>, Linker<Proc>)> {
    let mut store = Store::new(engine, Proc::new(MemBackend::Host(Mem::default())));
    let mut linker = Linker::new(engine);
    if let Some(path) = &opts.wasm_mem {
        let m = Module::from_file(engine, path)?;
        let inst = linker.instantiate(&mut store, &m)?;
        let l = |s: &mut Store<Proc>, n: &str| inst.get_typed_func::<i64, i64>(s, n);
        let st = |s: &mut Store<Proc>, n: &str| inst.get_typed_func::<(i64, i64), ()>(s, n);
        let w = WasmMem {
            load: [
                l(&mut store, "load8")?,
                l(&mut store, "load16")?,
                l(&mut store, "load32")?,
                l(&mut store, "load64")?,
            ],
            store: [
                st(&mut store, "store8")?,
                st(&mut store, "store16")?,
                st(&mut store, "store32")?,
                st(&mut store, "store64")?,
            ],
            map: inst.get_typed_func(&mut store, "map")?,
        };
        store.data_mut().mem = MemBackend::Wasm(w);
        linker.instance(&mut store, "mem", inst)?;
    } else {
        for (n, sz) in [("load8", 1), ("load16", 2), ("load32", 4), ("load64", 8)] {
            linker.func_wrap(
                "mem",
                n,
                move |cx: Caller<'_, Proc>, a: i64| -> Result<i64> {
                    mload(cx, a as u64, sz).map(|v| v as i64)
                },
            )?;
        }
        for (n, sz) in [
            ("store8", 1),
            ("store16", 2),
            ("store32", 4),
            ("store64", 8),
        ] {
            linker.func_wrap(
                "mem",
                n,
                move |cx: Caller<'_, Proc>, a: i64, v: i64| -> Result<()> {
                    mstore(cx, a as u64, sz, v as u64)
                },
            )?;
        }
        linker.func_wrap(
            "mem",
            "map",
            |cx: Caller<'_, Proc>, a: i64, l: i64| -> Result<i32> {
                mmap(cx, a as u64, l as u64).map(|_| 0)
            },
        )?;
    }
    linker.func_wrap(
        "sys",
        "syscall",
        |cx: Caller<'_, Proc>,
         nr: i64,
         a1: i64,
         a2: i64,
         a3: i64,
         a4: i64,
         a5: i64,
         a6: i64|
         -> Result<i64> {
            syscall(cx, nr as u64, [a1, a2, a3, a4, a5, a6].map(|x| x as u64)).map(|v| v as i64)
        },
    )?;
    linker.func_wrap("nd", "undef", |_: Caller<'_, Proc>, _loc: i32| -> i64 { 0 })?;
    // minimal WASI: fd_write (for Wasm modules such as libc.wasm), on the caller's "memory"
    linker.func_wrap(
        "wasi_snapshot_preview1",
        "fd_write",
        |mut cx: Caller<'_, Proc>, fd: i32, iovs: i32, n: i32, nw: i32| -> Result<i32> {
            let m = cx
                .get_export("memory")
                .and_then(|e| e.into_memory())
                .context("no memory export")?;
            let mut total = 0u32;
            for i in 0..n as usize {
                let mut iov = [0u8; 8];
                m.read(&cx, iovs as usize + 8 * i, &mut iov)?;
                let (p, l) = (
                    u32::from_le_bytes(iov[..4].try_into().unwrap()),
                    u32::from_le_bytes(iov[4..].try_into().unwrap()),
                );
                let mut buf = vec![0u8; l as usize];
                m.read(&cx, p as usize, &mut buf)?;
                emit(cx.data_mut(), fd as u64, &buf);
                total += l;
            }
            m.write(&mut cx, nw as usize, &total.to_le_bytes())?;
            Ok(0)
        },
    )?;
    linker.func_wrap("ext", "call", |cx: Caller<'_, Proc>, t: i64| {
        ext_call(cx, t as u64)
    })?;
    let io = wasmtime::Memory::new(&mut store, wasmtime::MemoryType::new(33, None))?;
    linker.define(&mut store, "io", "memory", io)?;
    if let Some(libc) = &opts.wasm_ext {
        let libc = linker.instantiate(&mut store, &Module::from_file(engine, libc)?)?;
        linker.instance(&mut store, "ffi", libc)?;
    } else {
        linker.func_wrap(
            "ffi",
            "call",
            |mut cx: Caller<'_, Proc>,
             t: i64,
             a1: i64,
             _: i64,
             _: i64,
             _: i64,
             _: i64,
             _: i64|
             -> Result<i32> {
                match host_libc_c(&mut cx, (t as u64).wrapping_sub(EXT_BASE) / 16, a1 as u64)? {
                    Some(r) => {
                        cx.data_mut().ffi_ret = r;
                        Ok(0)
                    }
                    None => Ok(2),
                }
            },
        )?;
        linker.func_wrap("ffi", "ret", |cx: Caller<'_, Proc>| -> i64 {
            cx.data().ffi_ret as i64
        })?;
    }
    Ok((store, linker))
}

/// Instantiate the simulator and register it.
/// Without `set_ext` in the simulator and with `extrun`, the registered simulator is the
/// `extrun` wrapper around it (foreign calls handled outside the simulator).
pub fn instantiate_sim_ext(
    store: &mut Store<Proc>,
    linker: &mut Linker<Proc>,
    sim: &Module,
    extrun: Option<&Module>,
) -> Result<Sim> {
    let mut inst = linker.instantiate(&mut *store, sim)?;
    if let Some(x) = extrun
        && inst.get_func(&mut *store, "set_ext").is_none()
    {
        let mut l2 = linker.clone();
        l2.instance(&mut *store, "core", inst)?;
        inst = l2.instantiate(&mut *store, x)?; // exports get/set/step/run/set_ext
    }
    let s = Sim::new(store, inst)?;
    store.data_mut().sim = Some(s.clone());
    Ok(s)
}

pub fn instantiate_sim(
    store: &mut Store<Proc>,
    linker: &mut Linker<Proc>,
    sim: &Module,
) -> Result<Sim> {
    instantiate_sim_ext(store, linker, sim, None)
}

/// Copy a host-built memory image into the store's memory backend.
pub fn install(store: &mut Store<Proc>, image: Mem) -> Result<()> {
    if let MemBackend::Host(m) = &mut store.data_mut().mem {
        *m = image;
        return Ok(());
    }
    for (base, page) in image.pages() {
        mmap(&mut *store, base, 4096)?;
        for (i, w) in page.chunks(8).enumerate() {
            let v = u64::from_le_bytes(w.try_into().unwrap());
            if v != 0 {
                mstore(&mut *store, base + 8 * i as u64, 8, v)?;
            }
        }
    }
    Ok(())
}

pub struct Outcome {
    pub out: Vec<u8>,
    pub exit: Option<i32>,
    pub status: i32,
    pub rip: u64,
    pub stats: Stats,
}

/// Load the ELF `file` with `argv` into a fresh environment and run it on `sim`.
pub fn run_elf(
    engine: &Engine,
    opts: &EnvOpts,
    sim: &Module,
    file: &[u8],
    argv: &[Vec<u8>],
    echo: bool,
) -> Result<Outcome> {
    let (mut store, mut linker) = env(engine, opts)?;
    store.data_mut().echo = echo;
    let mut mem = Mem::default();
    let Image {
        entry,
        sp,
        brk,
        ext,
    } = elf::load(&mut mem, file, argv, &[])?;
    install(&mut store, mem)?;
    store.data_mut().brk = brk;
    store.data_mut().brk0 = brk;
    let x = match (&ext, &opts.extrun) {
        (Some(_), Some(p)) => Some(Module::from_file(engine, p)?),
        _ => None,
    };
    let s = instantiate_sim_ext(&mut store, &mut linker, sim, x.as_ref())?;
    for l in 0..24 {
        s.set.call(&mut store, (l, 0))?;
    }
    s.set.call(&mut store, (RSP, sp as i64))?;
    s.set.call(&mut store, (RIP, entry as i64))?;
    if let (Some((lo, hi)), Some(f)) = (ext, &s.set_ext) {
        f.call(&mut store, (lo as i64, hi as i64))?;
    }
    let status = s.run.call(&mut store, i64::MAX)?;
    let rip = s.get.call(&mut store, RIP)? as u64;
    let p = store.data_mut();
    Ok(Outcome {
        out: std::mem::take(&mut p.out),
        exit: p.exit,
        status,
        rip,
        stats: p.stats,
    })
}
