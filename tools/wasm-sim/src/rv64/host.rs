//! wasmtime embedding: environment memory module (`mem.wat`), a Linux-like
//! `sys.syscall` host function (write, exit, exit_group), ELF loading, and a
//! thin typed wrapper around a simulator instance.

use super::elf::Elf;
use std::path::Path;
use wasmtime::error::{Context, Result};
use wasmtime::*;

pub const NLOC: i32 = 33;
pub const SENTINEL: u64 = 0xFFFF_FFFF_FFFF_F000;
pub const STACK_TOP: u64 = 0x3FF_0000;

#[derive(Default)]
pub struct Host {
    pub out: Vec<u8>,
    pub exit: Option<i64>,
    pub mem: Option<Memory>,
    pub nsys: u64,
}

pub fn engine() -> Engine {
    let mut c = Config::new();
    c.wasm_multi_memory(true);
    Engine::new(&c).unwrap()
}

pub fn rv64_dir() -> std::path::PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/wasm-sim/rv64")
}

pub fn mem_module(engine: &Engine) -> Result<Module> {
    Module::from_file(engine, rv64_dir().join("mem.wat"))
}

// The Linux syscall import: number and six argument registers.
#[allow(clippy::too_many_arguments)]
pub fn syscall(
    mut caller: Caller<'_, Host>,
    nr: i64,
    a0: i64,
    a1: i64,
    a2: i64,
    _a3: i64,
    _a4: i64,
    _a5: i64,
) -> i64 {
    caller.data_mut().nsys += 1;
    match nr {
        64 => {
            // write(fd, buf, len)
            let mem = caller.data().mem.unwrap();
            let (s, e) = (a1 as usize, a1 as usize + a2 as usize);
            let bytes = match mem.data(&caller).get(s..e) {
                Some(b) => b.to_vec(),
                None => return -14, // EFAULT
            };
            if a0 == 1 || a0 == 2 {
                caller.data_mut().out.extend_from_slice(&bytes);
                a2
            } else {
                -9 // EBADF
            }
        }
        93 | 94 => {
            caller.data_mut().exit = Some(a0 & 0xff);
            0
        }
        _ => -38, // ENOSYS
    }
}

/// A simulator instance with its own environment memory.
pub struct Sim {
    pub store: Store<Host>,
    pub inst: Instance,
    pub env: Memory,
    step: TypedFunc<(), i32>,
    run: TypedFunc<i64, i32>,
    get: TypedFunc<i32, i64>,
    set: TypedFunc<(i32, i64), ()>,
    fuel_left: Global,
}

impl Sim {
    pub fn new(engine: &Engine, sim: &Module, mem: &Module) -> Result<Sim> {
        let mut store = Store::new(engine, Host::default());
        let mut linker = Linker::new(engine);
        let mem_inst = linker.instantiate(&mut store, mem)?;
        let env = mem_inst.get_memory(&mut store, "memory").unwrap();
        store.data_mut().mem = Some(env);
        linker.instance(&mut store, "mem", mem_inst)?;
        linker.func_wrap("sys", "syscall", syscall)?;
        let inst = linker.instantiate(&mut store, sim)?;
        let step = inst.get_typed_func(&mut store, "step")?;
        let run = inst.get_typed_func(&mut store, "run")?;
        let get = inst.get_typed_func(&mut store, "get")?;
        let set = inst.get_typed_func(&mut store, "set")?;
        let fuel_left = inst
            .get_global(&mut store, "fuel_left")
            .context("fuel_left")?;
        Ok(Sim {
            store,
            inst,
            env,
            step,
            run,
            get,
            set,
            fuel_left,
        })
    }

    pub fn load_elf(&mut self, elf: &Elf) -> Result<()> {
        for s in &elf.segments {
            let d = self.env.data_mut(&mut self.store);
            let a = s.vaddr as usize;
            d.get_mut(a..a + s.data.len())
                .context("segment outside guest window")?
                .copy_from_slice(&s.data);
        }
        self.set(32, elf.entry);
        self.set(2, STACK_TOP);
        Ok(())
    }

    pub fn get(&mut self, loc: i32) -> u64 {
        self.get.call(&mut self.store, loc).unwrap() as u64
    }
    pub fn set(&mut self, loc: i32, v: u64) {
        self.set.call(&mut self.store, (loc, v as i64)).unwrap()
    }
    pub fn regs(&mut self) -> [u64; 33] {
        let mut r = [0; 33];
        for (i, x) in r.iter_mut().enumerate() {
            *x = self.get(i as i32);
        }
        r
    }
    /// One step; a trap (in a `mem.*` import) is status 3.
    pub fn step(&mut self) -> i32 {
        self.step.call(&mut self.store, ()).unwrap_or(3)
    }
    /// Run with fuel; returns (status, retired instructions).
    pub fn run(&mut self, fuel: u64) -> (i32, u64) {
        let st = self.run.call(&mut self.store, fuel as i64).unwrap_or(3);
        let left = self.fuel_left.get(&mut self.store).unwrap_i64() as u64;
        (st, fuel - left)
    }
    pub fn host(&self) -> &Host {
        self.store.data()
    }
}

/// A P-calls program instance linked against a simulator instance.
pub struct Prog {
    run: TypedFunc<i64, i32>,
    blk: TypedFunc<i64, i32>,
    fuel_left: Global,
    pub steps: u64,
}

impl Prog {
    pub fn new(engine: &Engine, sim: &mut Sim, prog: &Module) -> Result<Prog> {
        let mut linker = Linker::new(engine);
        linker.instance(&mut sim.store, "sim", sim.inst)?;
        let inst = linker.instantiate(&mut sim.store, prog)?;
        Ok(Prog {
            run: inst.get_typed_func(&mut sim.store, "prog_run")?,
            blk: inst.get_typed_func(&mut sim.store, "prog_blk")?,
            fuel_left: inst
                .get_global(&mut sim.store, "prog_fuel_left")
                .context("prog_fuel_left")?,
            steps: 0,
        })
    }

    /// Mixed mode: run translated blocks; when control reaches a pc that is not
    /// a block leader (status 2), interpret with `step` until it is.
    pub fn run(&mut self, sim: &mut Sim, fuel: u64) -> (i32, u64) {
        let mut left = fuel;
        loop {
            let st = self.run.call(&mut sim.store, left as i64).unwrap_or(3);
            left = self.fuel_left.get(&mut sim.store).unwrap_i64() as u64;
            if st != 2 {
                return (st, fuel - left);
            }
            // fall back to the interpreter until the next leader
            loop {
                if left == 0 {
                    return (4, fuel);
                }
                let s = sim.step();
                self.steps += 1;
                if s != 0 {
                    return (s, fuel - left);
                }
                left -= 1;
                let pc = sim.get(32);
                if self.blk.call(&mut sim.store, pc as i64).unwrap_or(-1) >= 0 {
                    break;
                }
            }
        }
    }
}
