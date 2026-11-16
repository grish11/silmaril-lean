//! Generic wasmtime harness for simulators following the ABI of `docs/projects/wasm-sim-abi.md`:
//! host-provided `mem.*`, `sys.syscall` and `nd.undef` imports, and a typed view of the
//! state API (`get`/`set`/`modelled`/`step`/`run`). ISA-independent.

use anyhow::{Result, anyhow, bail};
use std::collections::HashMap;
use std::path::Path;
use wasmtime::{Caller, Engine, Instance, Linker, Module, Store, TypedFunc};

/// Status codes of `step`/`run`.
pub const ST_OK: i32 = 0;
pub const ST_HALT: i32 = 1;
pub const ST_UNSUPPORTED: i32 = 2;
pub const ST_FAULT: i32 = 3;
pub const ST_FUEL: i32 = 4;

/// Return address that halts the simulator (`step` returns 1 when rip reaches it).
pub const SENTINEL: u64 = 0xFFFF_FFFF_FFFF_F000;

/// Host memory seen through the `mem.*` imports. `None` = fault (trap).
pub trait Memory: Send {
    fn load(&mut self, addr: u64, n: usize) -> Option<u64>;
    fn store(&mut self, addr: u64, n: usize, v: u64) -> Option<()>;
}

/// Sparse paged memory (4 KiB pages, mapped explicitly).
#[derive(Default, Clone)]
pub struct PageMem {
    pages: HashMap<u64, Box<[u8; 4096]>>,
}

impl PageMem {
    pub fn map(&mut self, addr: u64, len: u64) {
        let mut p = addr & !0xfff;
        while p < addr + len {
            self.pages.entry(p).or_insert_with(|| Box::new([0; 4096]));
            p += 4096;
        }
    }
    pub fn write(&mut self, addr: u64, bytes: &[u8]) {
        self.map(addr, bytes.len() as u64);
        for (i, b) in bytes.iter().enumerate() {
            let a = addr + i as u64;
            self.pages.get_mut(&(a & !0xfff)).unwrap()[(a & 0xfff) as usize] = *b;
        }
    }
    pub fn read(&self, addr: u64, len: usize) -> Option<Vec<u8>> {
        (0..len as u64)
            .map(|i| {
                let a = addr + i;
                self.pages
                    .get(&(a & !0xfff))
                    .map(|p| p[(a & 0xfff) as usize])
            })
            .collect()
    }
}

impl Memory for PageMem {
    fn load(&mut self, addr: u64, n: usize) -> Option<u64> {
        let off = (addr & 0xfff) as usize;
        if off + n <= 4096 {
            let p = self.pages.get(&(addr & !0xfff))?;
            let mut b = [0u8; 8];
            b[..n].copy_from_slice(&p[off..off + n]);
            return Some(u64::from_le_bytes(b));
        }
        let mut v = 0u64;
        for i in 0..n as u64 {
            let a = addr.wrapping_add(i);
            v |= (self.pages.get(&(a & !0xfff))?[(a & 0xfff) as usize] as u64) << (8 * i);
        }
        Some(v)
    }
    fn store(&mut self, addr: u64, n: usize, v: u64) -> Option<()> {
        for i in 0..n as u64 {
            let a = addr.wrapping_add(i);
            self.pages.get_mut(&(a & !0xfff))?[(a & 0xfff) as usize] = (v >> (8 * i)) as u8;
        }
        Some(())
    }
}

/// The real memory of this process, restricted to a list of `[start, end)` ranges
/// (used by difftests, so that simulator and CPU see the same addresses).
pub struct RawMem {
    pub ranges: Vec<(u64, u64)>,
}

impl RawMem {
    fn ok(&self, a: u64, n: usize) -> bool {
        self.ranges
            .iter()
            .any(|&(s, e)| a >= s && a.checked_add(n as u64).is_some_and(|x| x <= e))
    }
}

impl Memory for RawMem {
    fn load(&mut self, addr: u64, n: usize) -> Option<u64> {
        if !self.ok(addr, n) {
            return None;
        }
        let mut b = [0u8; 8];
        // SAFETY: the range was registered by the caller as readable memory of this process.
        unsafe { std::ptr::copy_nonoverlapping(addr as *const u8, b.as_mut_ptr(), n) };
        Some(u64::from_le_bytes(b))
    }
    fn store(&mut self, addr: u64, n: usize, v: u64) -> Option<()> {
        if !self.ok(addr, n) {
            return None;
        }
        let b = v.to_le_bytes();
        // SAFETY: as above, writable.
        unsafe { std::ptr::copy_nonoverlapping(b.as_ptr(), addr as *mut u8, n) };
        Some(())
    }
}

/// How `nd.undef` answers.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Undef {
    Zero,
    Ones,
    /// splitmix64 sequence from a seed
    Random(u64),
}

/// Host state of one store.
pub struct Host {
    pub mem: Box<dyn Memory>,
    pub undef: Undef,
    /// every `nd.undef` query (location) since the last clear
    pub undef_log: Vec<i32>,
    /// exit code once `exit`/`exit_group` was called
    pub exit: Option<i64>,
    pub stdout: Vec<u8>,
    /// optional per-instruction trace hook used by P-calls lockstep (`trace.insn` import)
    pub trace: Vec<u64>,
}

impl Host {
    pub fn new(mem: Box<dyn Memory>) -> Self {
        Host {
            mem,
            undef: Undef::Zero,
            undef_log: vec![],
            exit: None,
            stdout: vec![],
            trace: vec![],
        }
    }
}

fn splitmix(s: &mut u64) -> u64 {
    *s = s.wrapping_add(0x9E3779B97F4A7C15);
    let mut z = *s;
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
    z ^ (z >> 31)
}

/// Minimal Linux syscall host: write(1|2), exit, exit_group; everything else -ENOSYS.
fn syscall(c: &mut Caller<'_, Host>, nr: i64, a: [i64; 6]) -> wasmtime::Result<i64> {
    let h = c.data_mut();
    Ok(match nr {
        1 if a[0] == 1 || a[0] == 2 => {
            let mut out = vec![];
            for i in 0..a[2] as u64 {
                match h.mem.load(a[1] as u64 + i, 1) {
                    Some(b) => out.push(b as u8),
                    None => return Ok(-14),
                }
            }
            h.stdout.extend_from_slice(&out);
            a[2]
        }
        60 | 231 => {
            h.exit = Some(a[0]);
            0
        }
        _ => -38,
    })
}

/// Add the environment imports (`mem`, `sys`, `nd`, `trace`) to a linker.
pub fn add_env(linker: &mut Linker<Host>) -> Result<()> {
    macro_rules! ld {
        ($name:expr, $n:expr) => {
            linker.func_wrap(
                "mem",
                $name,
                |mut c: Caller<'_, Host>, a: i64| -> wasmtime::Result<i64> {
                    c.data_mut()
                        .mem
                        .load(a as u64, $n)
                        .map(|v| v as i64)
                        .ok_or_else(|| {
                            wasmtime::Error::msg(format!("fault: load{} at {:#x}", 8 * $n, a))
                        })
                },
            )?;
        };
    }
    macro_rules! st {
        ($name:expr, $n:expr) => {
            linker.func_wrap(
                "mem",
                $name,
                |mut c: Caller<'_, Host>, a: i64, v: i64| -> wasmtime::Result<()> {
                    c.data_mut()
                        .mem
                        .store(a as u64, $n, v as u64)
                        .ok_or_else(|| {
                            wasmtime::Error::msg(format!("fault: store{} at {:#x}", 8 * $n, a))
                        })
                },
            )?;
        };
    }
    ld!("load8", 1);
    ld!("load16", 2);
    ld!("load32", 4);
    ld!("load64", 8);
    st!("store8", 1);
    st!("store16", 2);
    st!("store32", 4);
    st!("store64", 8);
    linker.func_wrap(
        "sys",
        "syscall",
        |mut c: Caller<'_, Host>, nr: i64, a1: i64, a2: i64, a3: i64, a4: i64, a5: i64, a6: i64| {
            syscall(&mut c, nr, [a1, a2, a3, a4, a5, a6])
        },
    )?;
    linker.func_wrap("nd", "undef", |mut c: Caller<'_, Host>, loc: i32| -> i64 {
        let h = c.data_mut();
        h.undef_log.push(loc);
        match &mut h.undef {
            Undef::Zero => 0,
            Undef::Ones => -1,
            Undef::Random(s) => splitmix(s) as i64,
        }
    })?;
    linker.func_wrap("trace", "insn", |mut c: Caller<'_, Host>, a: i64| {
        c.data_mut().trace.push(a as u64);
    })?;
    linker.func_wrap("trace", "val", |mut c: Caller<'_, Host>, a: i64| {
        c.data_mut().trace.push(a as u64);
    })?;
    Ok(())
}

pub fn engine() -> Engine {
    Engine::default()
}

/// Compile a module from `.wat` or `.wasm`.
pub fn load_module(engine: &Engine, path: &Path) -> Result<Module> {
    Module::from_file(engine, path).map_err(|e| anyhow!("loading {}: {e:?}", path.display()))
}

/// One simulator instance with its store.
pub struct Sim {
    pub store: Store<Host>,
    pub inst: Instance,
    get: TypedFunc<i32, i64>,
    set: TypedFunc<(i32, i64), ()>,
    modelled: TypedFunc<i32, i32>,
    step: Option<TypedFunc<(), i32>>,
    run: Option<TypedFunc<i64, i32>>,
    /// last trap message (status 3)
    pub fault: Option<String>,
}

impl Sim {
    pub fn new(engine: &Engine, module: &Module, host: Host) -> Result<Sim> {
        let mut linker = Linker::new(engine);
        add_env(&mut linker)?;
        let mut store = Store::new(engine, host);
        let inst = linker.instantiate(&mut store, module)?;
        Self::from_instance(store, inst)
    }

    pub fn from_instance(mut store: Store<Host>, inst: Instance) -> Result<Sim> {
        Ok(Sim {
            get: inst.get_typed_func(&mut store, "get")?,
            set: inst.get_typed_func(&mut store, "set")?,
            modelled: inst.get_typed_func(&mut store, "modelled")?,
            step: inst.get_typed_func(&mut store, "step").ok(),
            run: inst.get_typed_func(&mut store, "run").ok(),
            store,
            inst,
            fault: None,
        })
    }

    pub fn get(&mut self, loc: i32) -> u64 {
        self.get.call(&mut self.store, loc).unwrap() as u64
    }
    pub fn set(&mut self, loc: i32, v: u64) {
        self.set.call(&mut self.store, (loc, v as i64)).unwrap()
    }
    pub fn modelled(&mut self, loc: i32) -> bool {
        self.modelled.call(&mut self.store, loc).unwrap() != 0
    }
    fn status(&mut self, r: wasmtime::Result<i32>) -> i32 {
        match r {
            Ok(s) => s,
            Err(e) => {
                self.fault = Some(format!("{e:#}"));
                ST_FAULT
            }
        }
    }
    pub fn step(&mut self) -> i32 {
        let r = self
            .step
            .as_ref()
            .expect("simulator has no decoder (step)")
            .call(&mut self.store, ());
        self.status(r)
    }
    pub fn run(&mut self, fuel: u64) -> i32 {
        let r = self
            .run
            .as_ref()
            .expect("simulator has no decoder (run)")
            .call(&mut self.store, fuel as i64);
        self.status(r)
    }
    /// All modelled locations with values (abstraction into `loc -> option i64`).
    pub fn state(&mut self, nlocs: i32) -> Vec<Option<u64>> {
        (0..nlocs)
            .map(|l| {
                if self.modelled(l) {
                    Some(self.get(l))
                } else {
                    None
                }
            })
            .collect()
    }
    /// Call an exported `i_*`-style function with i64-convertible arguments (by signature).
    pub fn call(&mut self, name: &str, args: &[i64]) -> Result<Option<i64>> {
        let f = self
            .inst
            .get_func(&mut self.store, name)
            .ok_or_else(|| anyhow!("no export {name}"))?;
        let ty = f.ty(&self.store);
        let params: Vec<wasmtime::Val> = ty
            .params()
            .zip(args)
            .map(|(t, &a)| match t {
                wasmtime::ValType::I32 => wasmtime::Val::I32(a as i32),
                _ => wasmtime::Val::I64(a),
            })
            .collect();
        if params.len() != args.len() {
            bail!("{name}: arity mismatch");
        }
        let mut res = vec![wasmtime::Val::I32(0); ty.results().len()];
        f.call(&mut self.store, &params, &mut res)?;
        Ok(res.first().map(|v| match v {
            wasmtime::Val::I32(x) => *x as i64,
            wasmtime::Val::I64(x) => *x,
            _ => 0,
        }))
    }
}
