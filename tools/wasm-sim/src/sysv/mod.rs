//! System V AMD64 call wrapper (docs/projects/wasm-sim-abi.md): descriptor serialization, and a
//! differential test of `sysv.wasm` + a simulator against native calls.
//!
//! The wrapper's status word (see `examples/wasm-sim/proc/wat/sysv.wat`) is 0 exactly when
//! the run returned to the sentinel with `AbiReturn` (rsp popped, callee-saved preserved).

use crate::proc::elf::{self, STACK_SIZE, STACK_TOP};
use crate::proc::host::{self, EnvOpts, Proc, RSP};
use crate::proc::mem::Mem;
use std::io::Write;
use std::process::{Command, Stdio};
use wasmtime::error::Context;
use wasmtime::{Engine, Module, Result, Store, TypedFunc, bail};

/// A call descriptor: target, integer register arguments (<= 6), stack arguments.
#[derive(Debug, Clone, Default)]
pub struct Desc {
    pub target: u64,
    pub int_args: Vec<u64>,
    pub stack_args: Vec<u64>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CallResult {
    pub rax: u64,
    pub rdx: u64,
    pub status: u64,
}

impl Desc {
    /// ABI layout (docs/projects/wasm-sim-abi.md): `u64 target, u64 nint, u64 int_args[6], u64 nstack,
    /// u64 stack_args[nstack]`, then the result area `rax, rdx, status` (zeroed).
    pub fn encode(&self) -> Vec<u8> {
        let mut w = vec![self.target, self.int_args.len() as u64];
        let mut ia = self.int_args.clone();
        ia.resize(6, 0);
        w.extend(ia);
        w.push(self.stack_args.len() as u64);
        w.extend(&self.stack_args);
        w.extend([0, 0, 0]);
        w.iter().flat_map(|x| x.to_le_bytes()).collect()
    }
    pub fn result_offset(&self) -> usize {
        8 * (9 + self.stack_args.len())
    }
}

pub const ST_NOT_SENTINEL: u64 = 1;
pub const ST_RSP: u64 = 2;
pub const CALLEE_SAVED: [&str; 6] = ["rbx", "rbp", "r12", "r13", "r14", "r15"];
pub const ST_BAD_DESC: u64 = 1 << 16;
pub const ST_ENTRY: u64 = 1 << 17;

pub fn status_str(s: u64) -> String {
    if s == 0 {
        return "ok".into();
    }
    let mut v = vec![];
    if s & ST_NOT_SENTINEL != 0 {
        v.push(format!("stopped(sim status {})", (s >> 8) & 0xff));
    }
    if s & ST_RSP != 0 {
        v.push("rsp".into());
    }
    for (i, r) in CALLEE_SAVED.iter().enumerate() {
        if s & (4 << i) != 0 {
            v.push(format!("{r} clobbered"));
        }
    }
    if s & ST_BAD_DESC != 0 {
        v.push("bad descriptor".into());
    }
    if s & ST_ENTRY != 0 {
        v.push("AbiEntry".into());
    }
    v.join(",")
}

/// A simulator + wrapper instance with a loaded code image.
pub struct Wrapper {
    pub store: Store<Proc>,
    pub sim: host::Sim,
    call: TypedFunc<i32, i64>,
    memory: wasmtime::Memory,
}

pub const DESC_AT: usize = 64;

impl Wrapper {
    pub fn new(
        engine: &Engine,
        opts: &EnvOpts,
        sim: &Module,
        wrapper: &Module,
        code: &[u8],
    ) -> Result<Self> {
        let (mut store, mut linker) = host::env(engine, opts)?;
        let mut mem = Mem::default();
        elf::map_segments(&mut mem, &elf::Elf::parse(code)?)?;
        mem.map(STACK_TOP - STACK_SIZE, STACK_SIZE);
        host::install(&mut store, mem)?;
        let s = host::instantiate_sim(&mut store, &mut linker, sim)?;
        linker.instance(&mut store, "sim", s.instance)?;
        let w = linker.instantiate(&mut store, wrapper)?;
        // bounded runs: a broken simulator must not loop for 2^32 steps
        w.get_typed_func::<i64, ()>(&mut store, "set_fuel")?
            .call(&mut store, 1_000_000)?;
        Ok(Wrapper {
            call: w.get_typed_func(&mut store, "sysv_call")?,
            memory: w
                .get_memory(&mut store, "memory")
                .context("wrapper memory")?,
            sim: s,
            store,
        })
    }

    pub fn call(&mut self, d: &Desc) -> Result<CallResult> {
        let bytes = d.encode();
        self.memory.write(&mut self.store, DESC_AT, &bytes)?;
        self.call.call(&mut self.store, DESC_AT as i32)?;
        let mut r = [0u8; 24];
        self.memory
            .read(&self.store, DESC_AT + d.result_offset(), &mut r)?;
        let w = |i: usize| u64::from_le_bytes(r[8 * i..8 * i + 8].try_into().unwrap());
        Ok(CallResult {
            rax: w(0),
            rdx: w(1),
            status: w(2),
        })
    }
}

/// One test function: name, argument shape, meaningful result bits, expected status.
pub struct TestFn {
    pub name: &'static str,
    pub nint: usize,
    pub nstack: usize,
    /// Meaningful bits of rax (the ABI leaves bits above a narrow return type unspecified).
    pub rax_bits: u32,
    /// Is rdx part of the result (two INTEGER eightbytes)?
    pub rdx: bool,
    pub expect_status: u64,
    /// Compare with a native call (false for functions that break the ABI on purpose).
    pub native: bool,
    /// Restrict the random arguments to the function's precondition.
    pub fix: fn(&mut [u64; 8]),
}

fn any(_: &mut [u64; 8]) {}

const fn t(name: &'static str, nint: usize, nstack: usize, rax_bits: u32, rdx: bool) -> TestFn {
    TestFn {
        name,
        nint,
        nstack,
        rax_bits,
        rdx,
        expect_status: 0,
        native: true,
        fix: any,
    }
}

const fn tf(name: &'static str, nint: usize, rax_bits: u32, fix: fn(&mut [u64; 8])) -> TestFn {
    TestFn {
        name,
        nint,
        nstack: 0,
        rax_bits,
        rdx: false,
        expect_status: 0,
        native: true,
        fix,
    }
}

/// `examples/wasm-sim/x86/tests/funcs.S` (pointer functions excluded), with
/// arguments restricted to each precondition (bounded loops/recursion, no #DE).
pub const TESTS_X86: &[TestFn] = &[
    t("add2", 2, 0, 64, false),
    t("max2", 2, 0, 64, false),
    t("abs1", 1, 0, 64, false),
    tf("sum_to", 1, 64, |a| a[0] %= 5000),
    t("gcd", 2, 0, 64, false),
    tf("popcount1", 1, 32, any),
    tf("popcount2", 1, 32, any),
    tf("fact", 1, 64, |a| a[0] %= 30),
    tf("sw", 1, 64, |a| a[0] %= 12),
    t("mix", 3, 0, 64, false),
    tf("divs", 2, 64, |a| {
        if a[1] == 0 || (a[1] == u64::MAX && a[0] == 1 << 63) {
            a[1] = 7;
        }
    }),
];

pub const TESTS: &[TestFn] = &[
    t("add2", 2, 0, 64, false),
    t("entry_rsp", 0, 0, 64, false),
    t("sum8_asm", 6, 2, 64, false),
    t("mix", 6, 0, 64, false),
    t("sum8", 6, 2, 64, false),
    t("addsub", 2, 0, 64, true),
    t("collatz", 1, 0, 64, false),
    t("fib", 1, 0, 64, false),
    t("clamp", 3, 0, 64, false),
    t("popc", 1, 0, 32, false),
    t("callsave", 2, 0, 64, false),
    t("cmp3", 2, 0, 32, false),
    t("lowbyte", 2, 0, 8, false),
    TestFn {
        name: "bad_rbx",
        nint: 1,
        nstack: 0,
        rax_bits: 64,
        rdx: false,
        expect_status: 4,
        native: false,
        fix: any,
    },
    TestFn {
        name: "bad_r12",
        nint: 0,
        nstack: 0,
        rax_bits: 0,
        rdx: false,
        expect_status: 16,
        native: false,
        fix: any,
    },
    TestFn {
        name: "bad_rsp",
        nint: 0,
        nstack: 0,
        rax_bits: 0,
        rdx: false,
        expect_status: 2,
        native: false,
        fix: any,
    },
];

/// xorshift64* (deterministic test vectors).
pub struct Rng(pub u64);
impl Rng {
    pub fn next_u64(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545F4914F6CDD1D)
    }
    /// Mix of small, boundary and full-width values.
    pub fn arg(&mut self) -> u64 {
        match self.next_u64() % 4 {
            0 => self.next_u64() % 64,
            1 => [0, 1, u64::MAX, 1 << 63, (1 << 63) - 1, 0xffff_ffff]
                [(self.next_u64() % 6) as usize],
            2 => (self.next_u64() as i64 >> (self.next_u64() % 60)) as u64,
            _ => self.next_u64(),
        }
    }
}

fn native_results(driver: &str, lines: &str) -> Result<Vec<(u64, u64)>> {
    let mut c = Command::new(driver)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()?;
    c.stdin.take().unwrap().write_all(lines.as_bytes())?;
    let out = c.wait_with_output()?;
    let mut v = vec![];
    for l in String::from_utf8_lossy(&out.stdout).lines() {
        let w: Vec<u64> = l
            .split(' ')
            .filter_map(|x| u64::from_str_radix(x, 16).ok())
            .collect();
        if w.len() != 2 {
            bail!("native driver output: {l}");
        }
        v.push((w[0], w[1]));
    }
    Ok(v)
}

pub struct Report {
    pub calls: usize,
    pub failures: Vec<String>,
}

/// Differential test: `n` random calls per function, simulator (through the wrapper) vs
/// native, with randomized caller state (all GPRs, flags, caller rsp alignment).
pub fn difftest(
    w: &mut Wrapper,
    code: &[u8],
    driver: &str,
    tests: &[TestFn],
    n: usize,
    seed: u64,
) -> Result<Report> {
    let syms = elf::Elf::parse(code)?.symbols()?;
    let mut rng = Rng(seed | 1);
    let mut rep = Report {
        calls: 0,
        failures: vec![],
    };
    for tf in tests {
        let Some(&(_, addr)) = syms.iter().find(|(s, _)| s == tf.name) else {
            bail!("no symbol {}", tf.name)
        };
        let vecs: Vec<[u64; 8]> = (0..n)
            .map(|_| {
                let mut a = std::array::from_fn(|_| rng.arg());
                (tf.fix)(&mut a);
                a
            })
            .collect();
        let native = if tf.native {
            let lines: String = vecs
                .iter()
                .map(|a| {
                    format!(
                        "{} {}\n",
                        tf.name,
                        a.iter()
                            .map(|x| format!("{x:x}"))
                            .collect::<Vec<_>>()
                            .join(" ")
                    )
                })
                .collect();
            Some(native_results(driver, &lines)?)
        } else {
            None
        };
        for (k, a) in vecs.iter().enumerate() {
            for l in 0..24 {
                if l != RSP {
                    let v = rng.next_u64();
                    w.sim.set.call(
                        &mut w.store,
                        (l, if l >= 16 { (v & 1) as i64 } else { v as i64 }),
                    )?;
                }
            }
            w.sim.set.call(
                &mut w.store,
                (RSP, (STACK_TOP - 0x8000 - rng.next_u64() % 64) as i64),
            )?;
            let d = Desc {
                target: addr,
                int_args: a[..tf.nint].to_vec(),
                stack_args: a[6..6 + tf.nstack].to_vec(),
            };
            let r = w.call(&d)?;
            rep.calls += 1;
            let mask = if tf.rax_bits == 64 {
                u64::MAX
            } else {
                (1u64 << tf.rax_bits) - 1
            };
            let mut bad = r.status != tf.expect_status;
            if let Some(nat) = &native {
                let (x, y) = nat[k];
                bad |= (r.rax & mask) != (x & mask) || (tf.rdx && r.rdx != y);
                if bad {
                    rep.failures.push(format!(
                        "{}({:x?}): sim rax={:#x} rdx={:#x} [{}], native rax={x:#x} rdx={y:#x}",
                        tf.name,
                        &a[..tf.nint + tf.nstack.min(2)],
                        r.rax,
                        r.rdx,
                        status_str(r.status)
                    ));
                }
            } else if bad {
                rep.failures.push(format!(
                    "{}: status [{}], expected [{}]",
                    tf.name,
                    status_str(r.status),
                    status_str(tf.expect_status)
                ));
            }
            if tf.name == "entry_rsp" && r.rax != 8 {
                rep.failures
                    .push(format!("entry_rsp: rsp mod 16 = {} at entry", r.rax));
            }
        }
    }
    Ok(rep)
}
