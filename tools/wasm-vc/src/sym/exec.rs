//! Symbolic execution of linked core Wasm instances into SMT terms.
//!
//! Execution is path-merging: a single symbolic state flows through the
//! structured code under a *guard* (the path condition); branches record the
//! state at their target label, and labels merge their incoming states with
//! `ite`s on the (mutually exclusive) guards. Calls of module functions are
//! inlined (bounded depth), loops are unrolled (bounded), and the guards under
//! which a bound was hit are recorded as *cutoffs*: a result is complete only
//! when every cutoff guard is unsatisfiable.
//!
//! Imports that are neither linked to another instance nor given a built-in
//! model are *opaque* (game semantics): every call is recorded as an event and
//! its results are unconstrained. In history mode (relational problems) the
//! results are an uninterpreted function of the import-call history
//! (`Hist` datatype), so two programs that make the same calls receive the
//! same answers, and comparing final histories compares the traces of calls.

use super::module::{BinOp, CmpOp, FnTy, Ins, Module, Ty, UnOp};
use super::term::{Bv2, Id, N, Rel, Sort, Terms};
use anyhow::{Result, bail};
use std::rc::Rc;

#[derive(Clone, Debug)]
pub struct Limits {
    /// Iterations of each loop entry before a cutoff.
    pub unroll: u32,
    /// Inlining depth of calls before a cutoff.
    pub depth: u32,
    /// Answers of opaque imports depend on the call history (relational mode).
    pub hist: bool,
}

impl Default for Limits {
    fn default() -> Self {
        Limits {
            unroll: 4,
            depth: 32,
            hist: false,
        }
    }
}

/// How an imported function behaves.
#[derive(Clone, Debug)]
pub enum HostModel {
    /// Unconstrained answers; the call is an event.
    Opaque,
    /// Linked to a function of another instance.
    Wasm(usize, u32),
    /// `(addr i64) -> i64`: little-endian zero-extended load from the environment memory.
    EnvLoad(u32),
    /// `(addr i64, v i64)`: little-endian store to the environment memory.
    EnvStore(u32),
    /// Replaced by its contract (assume-guarantee): `Machine::contracts[k]`.
    Contract(usize),
}

/// A callee contract (assume-guarantee). The caller must establish `pre`
/// (an obligation at each call); the callee's effect is havoc plus the
/// assumption `post`.
#[derive(Clone, Debug)]
pub struct Contract {
    pub name: String,
    pub pre: String,
    pub post: String,
    pub style: ContractStyle,
}

#[derive(Clone, Debug)]
pub enum ContractStyle {
    /// Values in, values out (P-locals): parameters and results named; the
    /// callee does not change Wasm state (assumption: memory is preserved).
    Values {
        params: Vec<String>,
        results: Vec<String>,
    },
    /// x86 P-calls: the callee runs on the simulator state. Registers
    /// `(name, slot, is_flag)`; on return rsp = rsp + 8, rip = [rsp], the
    /// callee-saved registers keep their values, the others and the flags are
    /// arbitrary, memory changes only in `[rsp - 0x1000, rsp)` (assumption:
    /// the callee's footprint), the status is 0. Names: `old.R` before, `R` after.
    X86 {
        regs: Vec<(String, usize, bool)>,
        mem: Option<usize>,
    },
}

#[derive(Clone, Debug)]
pub struct Host {
    pub module: String,
    pub name: String,
    pub ty: FnTy,
    pub model: HostModel,
}

impl Host {
    pub fn key(&self) -> String {
        format!("{}.{}", self.module, self.name)
    }
}

pub struct Inst {
    pub name: String,
    pub m: Rc<Module>,
    /// Function index space: `Err(host)` for imports, `Ok(i)` for local function `i`.
    pub funcs: Vec<std::result::Result<u32, usize>>,
    /// Global index space → slot in `State::g`.
    pub globals: Vec<usize>,
    /// Memory index space → slot in `State::m`.
    pub mems: Vec<usize>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct State {
    pub g: Vec<Id>,
    pub m: Vec<Id>,
    pub h: Id,
}

/// One call of an opaque import.
#[derive(Clone, Debug)]
pub struct Event {
    pub guard: Id,
    pub host: usize,
    pub args: Vec<Id>,
    /// State when the call is made.
    pub state: State,
}

#[derive(Clone)]
struct Cur {
    guard: Id,
    st: State,
    locals: Vec<Id>,
    stack: Vec<Id>,
    /// Function (index space of its instance) and its locals on entry.
    func: u32,
    entry: Rc<Vec<Id>>,
}

/// A loop annotation: invariant (SMT-LIB over local names, `old.NAME` for
/// values on function entry, `g.NAME` for globals) and an optional 64-bit
/// measure that decreases (unsigned) on every back edge.
#[derive(Clone, Debug)]
pub struct LoopSpec {
    pub inv: String,
    pub decreases: Option<String>,
    /// Inference: candidate conjuncts (the invariant is their conjunction;
    /// obligations are per candidate, named `#j`) and candidate measures.
    pub parts: Vec<String>,
    pub measures: Vec<String>,
}

/// Locals, global slots and memory slots a piece of code may write.
#[derive(Default)]
struct Writes {
    locals: std::collections::BTreeSet<u32>,
    globals: std::collections::BTreeSet<usize>,
    mems: std::collections::BTreeSet<usize>,
    hist: bool,
}

struct Snap {
    guard: Id,
    st: State,
    locals: Vec<Id>,
    vals: Vec<Id>,
}

struct Label {
    arity: usize,
    pending: Vec<Snap>,
    /// Some path left the construct other than through this label.
    leaked: bool,
}

/// Slots of the global state.
#[derive(Clone, Debug)]
pub struct Slot {
    pub name: String,
    pub sort: Sort,
    pub init: Option<Id>,
}

pub struct Machine {
    pub t: Terms,
    pub lim: Limits,
    pub insts: Vec<Inst>,
    pub hosts: Vec<Host>,
    pub gslots: Vec<Slot>,
    pub mslots: Vec<Slot>,
    /// Memory sizes in bytes (`None` for the environment memory: unbounded).
    pub msize: Vec<Option<u64>>,
    pub contracts: Vec<Contract>,
    /// A checking loop was summarised.
    pub summarised: bool,
    /// A loop was cut by its invariant (paths over-approximated).
    pub cut: bool,
    /// A cut loop has no measure: only partial correctness is shown.
    pub partial: bool,
    /// Slots of imported memories not provided by an instance, by `module.name`.
    pub mem_imports: std::collections::HashMap<String, usize>,
    /// Slot of the environment memory, if any import uses it.
    pub env_mem: Option<usize>,
    pub events: Vec<Event>,
    /// Trap guards with the history at the trap.
    pub traps: Vec<(Id, Id)>,
    /// Guards under which a loop or call bound was hit.
    pub cutoffs: Vec<Id>,
    /// Loop annotations by (instance, function, loop pre-order number).
    pub invariants: std::collections::HashMap<(usize, u32, u32), LoopSpec>,
    /// Formulas that must be valid (invariant entry/preservation, measures).
    pub obligations: Vec<(String, Id)>,
    /// Count of traps and cutoffs (paths leaving every construct).
    leaks: u64,
    pub steps: u64,
}

/// Result of a top-level call.
pub struct Outcome {
    pub guard: Id,
    pub st: State,
    pub results: Vec<Id>,
}

/// `(old x)` in annotations is the name `old.x`.
pub fn old_syntax(text: &str) -> String {
    let mut out = String::new();
    let mut rest = text;
    while let Some(i) = rest.find("(old ") {
        out.push_str(&rest[..i]);
        let after = &rest[i + 5..];
        match after.find(')') {
            Some(j) => {
                out.push_str("old.");
                out.push_str(after[..j].trim());
                rest = &after[j + 1..];
            }
            None => {
                out.push_str(&rest[i..]);
                rest = "";
            }
        }
    }
    out.push_str(rest);
    out
}

fn rel_of(op: CmpOp) -> (Option<Rel>, bool, bool) {
    // (relation, swap arguments, negate); None = equality
    match op {
        CmpOp::Eq => (None, false, false),
        CmpOp::Ne => (None, false, true),
        CmpOp::LtS => (Some(Rel::Slt), false, false),
        CmpOp::LtU => (Some(Rel::Ult), false, false),
        CmpOp::GtS => (Some(Rel::Slt), true, false),
        CmpOp::GtU => (Some(Rel::Ult), true, false),
        CmpOp::LeS => (Some(Rel::Sle), false, false),
        CmpOp::LeU => (Some(Rel::Ule), false, false),
        CmpOp::GeS => (Some(Rel::Sle), true, false),
        CmpOp::GeU => (Some(Rel::Ule), true, false),
    }
}

impl Machine {
    pub fn new(lim: Limits) -> Self {
        Machine {
            t: Terms::new(),
            lim,
            insts: Vec::new(),
            hosts: Vec::new(),
            gslots: Vec::new(),
            mslots: Vec::new(),
            msize: Vec::new(),
            env_mem: None,
            mem_imports: Default::default(),
            contracts: Vec::new(),
            summarised: false,
            cut: false,
            partial: false,
            events: Vec::new(),
            traps: Vec::new(),
            cutoffs: Vec::new(),
            invariants: Default::default(),
            obligations: Vec::new(),
            leaks: 0,
            steps: 0,
        }
    }

    /// Add an instance named `name`. Function imports `module.name` are linked
    /// to the export `name` of an existing instance called `module`, else get
    /// the model `model(module, name)`. Global imports are linked likewise, or
    /// become fresh state slots.
    pub fn instantiate(
        &mut self,
        name: &str,
        m: Module,
        model: &dyn Fn(&str, &str) -> HostModel,
    ) -> Result<usize> {
        let m = Rc::new(m);
        let mut funcs = Vec::new();
        for imp in &m.imports {
            let linked = self.insts.iter().position(|i| i.name == imp.module);
            let model = match linked {
                Some(k) => {
                    let f = self.insts[k].m.find_func(&imp.name)?;
                    match self.insts[k].funcs[f as usize] {
                        Ok(_) => HostModel::Wasm(k, f),
                        Err(h) => self.hosts[h].model.clone(),
                    }
                }
                None => model(&imp.module, &imp.name),
            };
            if matches!(model, HostModel::EnvLoad(_) | HostModel::EnvStore(_))
                && self.env_mem.is_none()
            {
                self.env_mem = Some(self.mslots.len());
                self.mslots.push(Slot {
                    name: "env.mem".into(),
                    sort: Sort::Mem(64),
                    init: None,
                });
                self.msize.push(None);
            }
            funcs.push(Err(self.hosts.len()));
            self.hosts.push(Host {
                module: imp.module.clone(),
                name: imp.name.clone(),
                ty: m.types[imp.ty as usize].clone(),
                model,
            });
        }
        for i in 0..m.funcs.len() {
            funcs.push(Ok(i as u32));
        }
        let mut globals = Vec::new();
        for (gi, g) in m.globals.iter().enumerate() {
            let sort = Sort::Bv(g.ty.width());
            // imported global: `module.name`
            if g.init.is_none()
                && let Some((md, nm)) = g.name.as_deref().and_then(|n| n.split_once('.'))
                && let Some(k) = self.insts.iter().position(|i| i.name == md)
                && let Ok(gk) = self.insts[k].m.find_global(nm)
            {
                globals.push(self.insts[k].globals[gk as usize]);
                continue;
            }
            let init = g.init.map(|v| self.t.lit(v, g.ty.width()));
            globals.push(self.gslots.len());
            self.gslots.push(Slot {
                name: format!("{name}.g.{}", m.global_name(gi as u32)),
                sort,
                init,
            });
        }
        let mut mems = Vec::new();
        for (k, mem) in m.memories.iter().enumerate() {
            if let Some(key) = &mem.import {
                // linked to an exported memory of an instance, or shared by key
                let (md, nm) = key.split_once('.').unwrap_or((key, ""));
                let linked = self.insts.iter().find(|i| i.name == md).and_then(|i| {
                    match i.m.exports.get(nm) {
                        Some((wasmparser::ExternalKind::Memory, x)) => Some(i.mems[*x as usize]),
                        _ => None,
                    }
                });
                let slot = match linked.or_else(|| self.mem_imports.get(key).copied()) {
                    Some(s) => s,
                    None => {
                        let s = self.mslots.len();
                        let v = self.t.var(key, Sort::Mem(32));
                        self.mslots.push(Slot {
                            name: key.clone(),
                            sort: Sort::Mem(32),
                            init: Some(v),
                        });
                        self.msize.push(Some(mem.min_pages * 65536));
                        self.mem_imports.insert(key.clone(), s);
                        s
                    }
                };
                // active data segments write into the imported memory
                let mut init = self.mslots[slot].init.unwrap();
                for d in m.data.iter().filter(|d| d.mem as usize == k) {
                    for (j, &b) in d.bytes.iter().enumerate() {
                        let a = self.t.lit(d.offset + j as u64, 32);
                        let v = self.t.lit(b as u64, 8);
                        init = self.t.store(init, a, v);
                    }
                }
                self.mslots[slot].init = Some(init);
                mems.push(slot);
                continue;
            }
            mems.push(self.mslots.len());
            let mut init = self.t.const_mem(0, 32);
            for d in m.data.iter().filter(|d| d.mem as usize == k) {
                for (j, &b) in d.bytes.iter().enumerate() {
                    if b != 0 {
                        let a = self.t.lit(d.offset + j as u64, 32);
                        let v = self.t.lit(b as u64, 8);
                        init = self.t.store(init, a, v);
                    }
                }
            }
            self.mslots.push(Slot {
                name: format!("{name}.mem{k}"),
                sort: Sort::Mem(32),
                init: Some(init),
            });
            self.msize.push(Some(mem.min_pages * 65536));
        }
        self.insts.push(Inst {
            name: name.to_string(),
            m,
            funcs,
            globals,
            mems,
        });
        Ok(self.insts.len() - 1)
    }

    /// The initial state: module initial values (`symbolic = false`) or fresh
    /// variables for every global and memory (`symbolic = true`, an arbitrary
    /// state). The environment memory is always a fresh variable.
    pub fn initial(&mut self, symbolic: bool, prefix: &str) -> State {
        let mut g = Vec::new();
        for s in self.gslots.clone() {
            g.push(match (symbolic, s.init) {
                (false, Some(i)) => i,
                _ => self.t.var(&format!("{prefix}{}", s.name), s.sort),
            });
        }
        let mut m = Vec::new();
        for s in self.mslots.clone() {
            m.push(match (symbolic, s.init) {
                (false, Some(i)) => i,
                _ => self.t.var(&format!("{prefix}{}", s.name), s.sort),
            });
        }
        let h = self.t.hist_nil();
        State { g, m, h }
    }

    /// Call function `f` of instance `inst` under `guard` from state `st`.
    pub fn call(
        &mut self,
        inst: usize,
        f: u32,
        args: Vec<Id>,
        guard: Id,
        st: State,
    ) -> Result<Outcome> {
        let mut cur = Cur {
            guard,
            st,
            locals: vec![],
            stack: args,
            func: f,
            entry: Rc::new(vec![]),
        };
        self.call_fn(inst, f, &mut cur, 0)?;
        Ok(Outcome {
            guard: cur.guard,
            st: cur.st,
            results: cur.stack,
        })
    }

    fn leak(&mut self, labels: &mut [Label]) {
        self.leaks += 1;
        for l in labels.iter_mut() {
            l.leaked = true;
        }
    }

    fn trap(&mut self, cur: &mut Cur, cond: Id, labels: &mut [Label]) {
        let g = self.t.and2(cur.guard, cond);
        if self.t.is_false(g) {
            return;
        }
        self.traps.push((g, cur.st.h));
        self.leak(labels);
        let nc = self.t.not(cond);
        cur.guard = self.t.and2(cur.guard, nc);
    }

    fn cutoff(&mut self, g: Id, labels: &mut [Label]) {
        if !self.t.is_false(g) {
            self.cutoffs.push(g);
            self.leak(labels);
        }
    }

    fn merge(&mut self, mut snaps: Vec<Snap>) -> Snap {
        let mut acc = snaps.pop().expect("non-empty");
        while let Some(s) = snaps.pop() {
            let c = s.guard;
            acc.guard = self.t.or2(c, acc.guard);
            for (a, b) in acc.st.g.iter_mut().zip(&s.st.g) {
                *a = self.t.ite(c, *b, *a);
            }
            for (a, b) in acc.st.m.iter_mut().zip(&s.st.m) {
                *a = self.t.ite(c, *b, *a);
            }
            acc.st.h = self.t.ite(c, s.st.h, acc.st.h);
            for (a, b) in acc.locals.iter_mut().zip(&s.locals) {
                *a = self.t.ite(c, *b, *a);
            }
            for (a, b) in acc.vals.iter_mut().zip(&s.vals) {
                *a = self.t.ite(c, *b, *a);
            }
        }
        acc
    }

    fn snap(cur: &Cur, n: usize) -> Snap {
        Snap {
            guard: cur.guard,
            st: cur.st.clone(),
            locals: cur.locals.clone(),
            vals: cur.stack[cur.stack.len() - n..].to_vec(),
        }
    }

    /// Join the paths reaching the end of a construct: `pending` plus the
    /// fall-through `cur`. `entry` is the guard on entry, used as the merged
    /// guard when no path leaked (so guards do not grow with every split).
    fn join(
        &mut self,
        cur: &mut Cur,
        outer: Vec<Id>,
        mut pending: Vec<Snap>,
        n: usize,
        entry: Option<Id>,
        tys: &[Ty],
    ) {
        if !self.t.is_false(cur.guard) {
            pending.push(Self::snap(cur, n));
        }
        if pending.is_empty() {
            cur.guard = self.t.ff();
            cur.stack = outer;
            for k in 0..n {
                let w = tys.get(k).map_or(64, |t| t.width());
                let z = self.t.lit(0, w);
                cur.stack.push(z);
            }
            return;
        }
        let s = self.merge(pending);
        cur.guard = entry.unwrap_or(s.guard);
        cur.st = s.st;
        cur.locals = s.locals;
        cur.stack = outer;
        cur.stack.extend(s.vals);
    }

    fn call_fn(&mut self, inst: usize, f: u32, cur: &mut Cur, depth: u32) -> Result<()> {
        let ty = self.insts[inst].m.func_ty(f).clone();
        let n = ty.params.len();
        let args = cur.stack.split_off(cur.stack.len() - n);
        match self.insts[inst].funcs[f as usize] {
            Err(h) => self.call_host(h, args, cur, depth),
            Ok(i) => {
                if depth >= self.lim.depth {
                    let g = cur.guard;
                    self.cutoff(g, &mut []);
                    cur.guard = self.t.ff();
                    for r in &ty.results {
                        let z = self.t.lit(0, r.width());
                        cur.stack.push(z);
                    }
                    return Ok(());
                }
                let m = self.insts[inst].m.clone();
                let func = &m.funcs[i as usize];
                let mut locals = args;
                for l in &func.locals {
                    let z = self.t.lit(0, l.width());
                    locals.push(z);
                }
                let entry_leaks = self.leaks;
                let mut c = Cur {
                    guard: cur.guard,
                    st: cur.st.clone(),
                    entry: Rc::new(locals.clone()),
                    locals,
                    stack: vec![],
                    func: f,
                };
                let mut labels = vec![Label {
                    arity: ty.results.len(),
                    pending: vec![],
                    leaked: false,
                }];
                self.exec(inst, depth + 1, &func.body, &mut c, &mut labels)?;
                let lab = labels.pop().unwrap();
                let entry = (!lab.leaked && self.leaks == entry_leaks).then_some(cur.guard);
                let outer = std::mem::take(&mut cur.stack);
                c.locals.clear();
                let saved_locals = std::mem::take(&mut cur.locals);
                self.join(
                    &mut c,
                    outer,
                    lab.pending,
                    ty.results.len(),
                    entry,
                    &ty.results,
                );
                cur.guard = c.guard;
                cur.st = c.st;
                cur.stack = c.stack;
                cur.locals = saved_locals;
                Ok(())
            }
        }
    }

    fn call_host(&mut self, h: usize, args: Vec<Id>, cur: &mut Cur, depth: u32) -> Result<()> {
        let host = self.hosts[h].clone();
        match host.model {
            HostModel::Wasm(k, f) => {
                cur.stack.extend(args);
                self.call_fn(k, f, cur, depth)
            }
            HostModel::EnvLoad(n) => {
                let slot = self.env_mem.unwrap();
                let v = self.t.load_le(cur.st.m[slot], args[0], n);
                let v = self.t.zext(64 - 8 * n, v);
                cur.stack.push(v);
                Ok(())
            }
            HostModel::EnvStore(n) => {
                let slot = self.env_mem.unwrap();
                let v = self.t.extract(8 * n - 1, 0, args[1]);
                cur.st.m[slot] = self.t.store_le(cur.st.m[slot], args[0], v, n);
                Ok(())
            }
            HostModel::Contract(k) => {
                let c = self.contracts[k].clone();
                self.call_contract(&c, &host, args, cur);
                Ok(())
            }
            HostModel::Opaque => {
                let state = cur.st.clone();
                let mut results = Vec::new();
                if self.lim.hist {
                    let h2 = self.t.hist_cons(h as u32, &args, cur.st.h);
                    for (k, r) in host.ty.results.iter().enumerate() {
                        let f = format!("ans.{}.{k}", host.key());
                        let v = self.t.app(&f, vec![h2], Sort::Bv(r.width()));
                        results.push(v);
                    }
                    cur.st.h = h2;
                } else {
                    for r in &host.ty.results {
                        let v = self
                            .t
                            .fresh(&format!("ans.{}", host.key()), Sort::Bv(r.width()));
                        results.push(v);
                    }
                }
                if !self.t.is_false(cur.guard) {
                    self.events.push(Event {
                        guard: cur.guard,
                        host: h,
                        args,
                        state,
                    });
                }
                cur.stack.extend(results);
                Ok(())
            }
        }
    }

    fn i32_bool(&mut self, v: Id) -> Id {
        let z = self.t.lit(0, self.t.width(v));
        self.t.ne(v, z)
    }

    fn bool_i32(&mut self, b: Id) -> Id {
        let one = self.t.lit(1, 32);
        let z = self.t.lit(0, 32);
        self.t.ite(b, one, z)
    }

    /// Branch to relative label `l` under `g` (a sub-guard of the current guard).
    fn branch(&mut self, cur: &Cur, g: Id, l: u32, labels: &mut [Label]) {
        if self.t.is_false(g) {
            return;
        }
        let k = labels.len() - 1 - l as usize;
        let n = labels[k].arity;
        let mut s = Self::snap(cur, n);
        s.guard = g;
        labels[k].pending.push(s);
        for lab in labels[k + 1..].iter_mut() {
            lab.leaked = true;
        }
    }

    fn exec(
        &mut self,
        inst: usize,
        depth: u32,
        body: &[Ins],
        cur: &mut Cur,
        labels: &mut Vec<Label>,
    ) -> Result<()> {
        for ins in body {
            if self.t.is_false(cur.guard) {
                return Ok(());
            }
            self.steps += 1;
            self.step(inst, depth, ins, cur, labels)?;
        }
        Ok(())
    }

    fn block_tys(&self, inst: usize, n: usize) -> Vec<Ty> {
        let _ = inst;
        vec![Ty::I64; n]
    }

    fn step(
        &mut self,
        inst: usize,
        depth: u32,
        ins: &Ins,
        cur: &mut Cur,
        labels: &mut Vec<Label>,
    ) -> Result<()> {
        let t = &mut self.t;
        match ins {
            Ins::Nop => {}
            Ins::Unreachable => {
                let tt = t.tt();
                self.trap(cur, tt, labels);
            }
            Ins::Unsupported(s) => bail!("unsupported instruction: {s}"),
            Ins::Const32(v) => {
                let x = t.lit(*v as u64, 32);
                cur.stack.push(x);
            }
            Ins::Const64(v) => {
                let x = t.lit(*v, 64);
                cur.stack.push(x);
            }
            Ins::LocalGet(i) => cur.stack.push(cur.locals[*i as usize]),
            Ins::LocalSet(i) => cur.locals[*i as usize] = cur.stack.pop().unwrap(),
            Ins::LocalTee(i) => cur.locals[*i as usize] = *cur.stack.last().unwrap(),
            Ins::GlobalGet(i) => {
                let s = self.insts[inst].globals[*i as usize];
                cur.stack.push(cur.st.g[s]);
            }
            Ins::GlobalSet(i) => {
                let s = self.insts[inst].globals[*i as usize];
                cur.st.g[s] = cur.stack.pop().unwrap();
            }
            Ins::Drop => {
                cur.stack.pop();
            }
            Ins::Select => {
                let c = cur.stack.pop().unwrap();
                let b = cur.stack.pop().unwrap();
                let a = cur.stack.pop().unwrap();
                let cb = self.i32_bool(c);
                let v = self.t.ite(cb, a, b);
                cur.stack.push(v);
            }
            Ins::Un(ty, op) => {
                let a = cur.stack.pop().unwrap();
                let w = ty.width();
                let v = match op {
                    UnOp::Eqz => {
                        let z = t.lit(0, w);
                        let e = t.eq(a, z);
                        self.bool_i32(e)
                    }
                    UnOp::Clz => t.clz(a),
                    UnOp::Ctz => t.ctz(a),
                    UnOp::Popcnt => t.popcnt(a),
                    UnOp::Ext8S | UnOp::Ext16S | UnOp::Ext32S => {
                        let n = match op {
                            UnOp::Ext8S => 8,
                            UnOp::Ext16S => 16,
                            _ => 32,
                        };
                        let e = t.extract(n - 1, 0, a);
                        t.sext(w - n, e)
                    }
                };
                cur.stack.push(v);
            }
            Ins::Cmp(op) => {
                let b = cur.stack.pop().unwrap();
                let a = cur.stack.pop().unwrap();
                let (r, swap, neg) = rel_of(*op);
                let (x, y) = if swap { (b, a) } else { (a, b) };
                let c = match r {
                    None => t.eq(x, y),
                    Some(r) => t.rel(r, x, y),
                };
                let c = if neg { t.not(c) } else { c };
                let v = self.bool_i32(c);
                cur.stack.push(v);
            }
            Ins::Bin(ty, op) => {
                let b = cur.stack.pop().unwrap();
                let a = cur.stack.pop().unwrap();
                let w = ty.width();
                let v = self.binop(*op, w, a, b, cur, labels);
                cur.stack.push(v);
            }
            Ins::Wrap => {
                let a = cur.stack.pop().unwrap();
                let v = t.extract(31, 0, a);
                cur.stack.push(v);
            }
            Ins::ExtendS => {
                let a = cur.stack.pop().unwrap();
                let v = t.sext(32, a);
                cur.stack.push(v);
            }
            Ins::ExtendU => {
                let a = cur.stack.pop().unwrap();
                let v = t.zext(32, a);
                cur.stack.push(v);
            }
            Ins::Load {
                ty,
                bytes,
                signed,
                mem,
                offset,
            } => {
                let a = cur.stack.pop().unwrap();
                let slot = self.insts[inst].mems[*mem as usize];
                let addr = self.addr(slot, a, *offset, *bytes, cur, labels);
                let v = self.t.load_le(cur.st.m[slot], addr, *bytes);
                let ext = ty.width() - 8 * bytes;
                let v = if *signed {
                    self.t.sext(ext, v)
                } else {
                    self.t.zext(ext, v)
                };
                cur.stack.push(v);
            }
            Ins::Store { bytes, mem, offset } => {
                let v = cur.stack.pop().unwrap();
                let a = cur.stack.pop().unwrap();
                let slot = self.insts[inst].mems[*mem as usize];
                let addr = self.addr(slot, a, *offset, *bytes, cur, labels);
                let v = self.t.extract(8 * bytes - 1, 0, v);
                cur.st.m[slot] = self.t.store_le(cur.st.m[slot], addr, v, *bytes);
            }
            Ins::MemorySize(mem) => {
                let slot = self.insts[inst].mems[*mem as usize];
                let pages = self.msize[slot].unwrap_or(0) / 65536;
                let v = self.t.lit(pages, 32);
                cur.stack.push(v);
            }
            Ins::MemoryGrow(mem) => bail!("memory.grow (memory {mem}) is not supported"),
            Ins::MemoryCopy { dst, src } => {
                let n = cur.stack.pop().unwrap();
                let s = cur.stack.pop().unwrap();
                let d = cur.stack.pop().unwrap();
                let sd = self.insts[inst].mems[*dst as usize];
                let ss = self.insts[inst].mems[*src as usize];
                self.range_check(ss, s, n, cur, labels);
                self.range_check(sd, d, n, cur, labels);
                let (md, ms) = (cur.st.m[sd], cur.st.m[ss]);
                cur.st.m[sd] = self.t.copy(md, ms, d, s, n);
            }
            Ins::MemoryFill(mem) => {
                let n = cur.stack.pop().unwrap();
                let v = cur.stack.pop().unwrap();
                let d = cur.stack.pop().unwrap();
                let sd = self.insts[inst].mems[*mem as usize];
                self.range_check(sd, d, n, cur, labels);
                let b = self.t.extract(7, 0, v);
                let m = cur.st.m[sd];
                cur.st.m[sd] = self.t.fill(m, d, b, n);
            }
            Ins::Block {
                params,
                results,
                body,
            } => {
                let outer = cur.stack.split_off(cur.stack.len() - params);
                let outer = std::mem::replace(&mut cur.stack, outer);
                let entry_guard = cur.guard;
                let entry_leaks = self.leaks;
                labels.push(Label {
                    arity: *results,
                    pending: vec![],
                    leaked: false,
                });
                self.exec(inst, depth, body, cur, labels)?;
                let lab = labels.pop().unwrap();
                let entry = (!lab.leaked && self.leaks == entry_leaks).then_some(entry_guard);
                let tys = self.block_tys(inst, *results);
                self.join(cur, outer, lab.pending, *results, entry, &tys);
            }
            Ins::If {
                params,
                results,
                then,
                els,
            } => {
                let c = cur.stack.pop().unwrap();
                let cb = self.i32_bool(c);
                let outer = cur.stack.split_off(cur.stack.len() - params);
                let outer = std::mem::replace(&mut cur.stack, outer);
                let entry_guard = cur.guard;
                let entry_leaks = self.leaks;
                labels.push(Label {
                    arity: *results,
                    pending: vec![],
                    leaked: false,
                });
                let mut ce = cur.clone();
                cur.guard = self.t.and2(entry_guard, cb);
                self.exec(inst, depth, then, cur, labels)?;
                if !self.t.is_false(cur.guard) {
                    let s = Self::snap(cur, *results);
                    labels.last_mut().unwrap().pending.push(s);
                }
                let ncb = self.t.not(cb);
                ce.guard = self.t.and2(entry_guard, ncb);
                self.exec(inst, depth, els, &mut ce, labels)?;
                let lab = labels.pop().unwrap();
                let entry = (!lab.leaked && self.leaks == entry_leaks).then_some(entry_guard);
                let tys = self.block_tys(inst, *results);
                *cur = ce;
                self.join(cur, outer, lab.pending, *results, entry, &tys);
            }
            Ins::Loop {
                params,
                results,
                body,
                id,
            } if self.invariants.contains_key(&(inst, cur.func, *id)) => {
                let mut spec = self.invariants[&(inst, cur.func, *id)].clone();
                self.cut = true;
                if !spec.parts.is_empty() {
                    spec.inv = format!("(and true {})", spec.parts.join(" "));
                }
                if spec.decreases.is_none() {
                    self.partial = true;
                }
                let lname = format!("{} loop {id}", self.insts[inst].m.func_name(cur.func));
                let outer = cur.stack.split_off(cur.stack.len() - params);
                let outer = std::mem::replace(&mut cur.stack, outer);
                // the invariant holds on entry
                if spec.parts.is_empty() {
                    let inv0 = self.loop_formula(inst, &spec.inv, cur, None);
                    let ob = self.t.implies(cur.guard, inv0);
                    self.obligations
                        .push((format!("{lname}: invariant on entry"), ob));
                } else {
                    for (j, part) in spec.parts.iter().enumerate() {
                        let f = self.loop_formula(inst, part, cur, None);
                        let ob = self.t.implies(cur.guard, f);
                        self.obligations
                            .push((format!("{lname}: invariant on entry #{j}"), ob));
                    }
                }
                // an arbitrary iteration: havoc what the loop writes, assume the invariant
                let mut w = Writes::default();
                self.writes(inst, body, &mut w, &mut Default::default());
                for &l in &w.locals {
                    let sort = self.t.sort(cur.locals[l as usize]);
                    cur.locals[l as usize] = self.t.fresh(&format!("{lname}.l{l}"), sort);
                }
                for &g in &w.globals {
                    let sort = self.t.sort(cur.st.g[g]);
                    cur.st.g[g] = self
                        .t
                        .fresh(&format!("{lname}.{}", self.gslots[g].name), sort);
                }
                for &m in &w.mems {
                    let sort = self.t.sort(cur.st.m[m]);
                    cur.st.m[m] = self
                        .t
                        .fresh(&format!("{lname}.{}", self.mslots[m].name), sort);
                }
                if w.hist && self.lim.hist {
                    cur.st.h = self.t.fresh(&format!("{lname}.hist"), Sort::Hist);
                }
                for v in cur.stack.iter_mut() {
                    let sort = self.t.sort(*v);
                    *v = self.t.fresh(&format!("{lname}.param"), sort);
                }
                let invh = self.loop_formula(inst, &spec.inv, cur, None);
                let head_measure = spec
                    .decreases
                    .as_ref()
                    .map(|d| self.loop_formula(inst, d, cur, Some(Sort::Bv(64))));
                let head_cands: Vec<Id> = spec
                    .measures
                    .iter()
                    .map(|d| self.loop_formula(inst, d, cur, Some(Sort::Bv(64))))
                    .collect();
                cur.guard = self.t.and2(cur.guard, invh);
                let head = cur.clone();
                labels.push(Label {
                    arity: *params,
                    pending: vec![],
                    leaked: false,
                });
                self.exec(inst, depth, body, cur, labels)?;
                let lab = labels.pop().unwrap();
                for s in &lab.pending {
                    let mut c = head.clone();
                    c.st = s.st.clone();
                    c.locals = s.locals.clone();
                    if spec.parts.is_empty() {
                        let inv1 = self.loop_formula(inst, &spec.inv, &c, None);
                        let ob = self.t.implies(s.guard, inv1);
                        self.obligations
                            .push((format!("{lname}: invariant preserved"), ob));
                    } else {
                        for (j, part) in spec.parts.iter().enumerate() {
                            let f = self.loop_formula(inst, part, &c, None);
                            let ob = self.t.implies(s.guard, f);
                            self.obligations
                                .push((format!("{lname}: invariant preserved #{j}"), ob));
                        }
                    }
                    for (j, (d, &m0)) in spec.measures.iter().zip(&head_cands).enumerate() {
                        let m1 = self.loop_formula(inst, d, &c, Some(Sort::Bv(64)));
                        let lt = self.t.rel(Rel::Ult, m1, m0);
                        let ob = self.t.implies(s.guard, lt);
                        self.obligations
                            .push((format!("{lname}: measure decreases #{j}"), ob));
                    }
                    if let (Some(d), Some(m0)) = (&spec.decreases, head_measure) {
                        let m1 = self.loop_formula(inst, d, &c, Some(Sort::Bv(64)));
                        let lt = self.t.rel(Rel::Ult, m1, m0);
                        let ob = self.t.implies(s.guard, lt);
                        self.obligations
                            .push((format!("{lname}: measure decreases"), ob));
                    }
                }
                self.leak(labels);
                let mut exits = Vec::new();
                if !self.t.is_false(cur.guard) {
                    exits.push(Self::snap(cur, *results));
                }
                cur.guard = self.t.ff();
                let tys = self.block_tys(inst, *results);
                self.join(cur, outer, exits, *results, None, &tys);
            }
            Ins::Loop {
                params: 0,
                results: 0,
                body,
                ..
            } if !self.lim.hist && self.try_summarise(inst, depth, body, cur, labels)? => {}
            Ins::Loop {
                params,
                results,
                body,
                ..
            } => {
                let outer = cur.stack.split_off(cur.stack.len() - params);
                let outer = std::mem::replace(&mut cur.stack, outer);
                let entry_guard = cur.guard;
                let entry_leaks = self.leaks;
                let mut exits = Vec::new();
                let mut iter = 0;
                let mut any_leak = false;
                loop {
                    labels.push(Label {
                        arity: *params,
                        pending: vec![],
                        leaked: false,
                    });
                    self.exec(inst, depth, body, cur, labels)?;
                    let lab = labels.pop().unwrap();
                    any_leak |= lab.leaked;
                    if !self.t.is_false(cur.guard) {
                        exits.push(Self::snap(cur, *results));
                    }
                    if lab.pending.is_empty() {
                        break;
                    }
                    iter += 1;
                    if iter >= self.lim.unroll {
                        let gs: Vec<Id> = lab.pending.iter().map(|s| s.guard).collect();
                        let g = self.t.or(&gs);
                        self.cutoff(g, labels);
                        any_leak = true;
                        break;
                    }
                    let s = self.merge(lab.pending);
                    cur.guard = s.guard;
                    cur.st = s.st;
                    cur.locals = s.locals;
                    cur.stack = s.vals;
                }
                cur.guard = self.t.ff();
                let entry = (!any_leak && self.leaks == entry_leaks).then_some(entry_guard);
                let tys = self.block_tys(inst, *results);
                self.join(cur, outer, exits, *results, entry, &tys);
            }
            Ins::Br(l) => {
                let g = cur.guard;
                self.branch(cur, g, *l, labels);
                cur.guard = self.t.ff();
            }
            Ins::BrIf(l) => {
                let c = cur.stack.pop().unwrap();
                let cb = self.i32_bool(c);
                let g = self.t.and2(cur.guard, cb);
                self.branch(cur, g, *l, labels);
                let ncb = self.t.not(cb);
                cur.guard = self.t.and2(cur.guard, ncb);
            }
            Ins::BrTable(ts, d) => {
                let i = cur.stack.pop().unwrap();
                if let Some(k) = self.t.as_lit(i) {
                    let l = ts.get(k as usize).copied().unwrap_or(*d);
                    let g = cur.guard;
                    self.branch(cur, g, l, labels);
                } else {
                    // group the indices by target label
                    let mut targets: Vec<(u32, Vec<Id>)> = Vec::new();
                    for (k, &l) in ts.iter().enumerate() {
                        let kk = self.t.lit(k as u64, 32);
                        let c = self.t.eq(i, kk);
                        match targets.iter_mut().find(|(m, _)| *m == l) {
                            Some((_, cs)) => cs.push(c),
                            None => targets.push((l, vec![c])),
                        }
                    }
                    let n = self.t.lit(ts.len() as u64, 32);
                    let dc = self.t.rel(Rel::Ule, n, i);
                    match targets.iter_mut().find(|(m, _)| *m == *d) {
                        Some((_, cs)) => cs.push(dc),
                        None => targets.push((*d, vec![dc])),
                    }
                    for (l, cs) in targets {
                        let c = self.t.or(&cs);
                        let g = self.t.and2(cur.guard, c);
                        self.branch(cur, g, l, labels);
                    }
                }
                cur.guard = self.t.ff();
            }
            Ins::Return => {
                let g = cur.guard;
                let l = labels.len() as u32 - 1;
                self.branch(cur, g, l, labels);
                cur.guard = self.t.ff();
            }
            Ins::Call(f) => {
                self.call_fn(inst, *f, cur, depth)?;
            }
            Ins::CallIndirect { ty, table } => {
                let i = cur.stack.pop().unwrap();
                let m = self.insts[inst].m.clone();
                let tab = &m.tables[*table as usize];
                let want = &m.types[*ty as usize];
                let ok_ty = |f: u32| {
                    let ft = m.func_ty(f);
                    ft.params == want.params && ft.results == want.results
                };
                // candidates: (index, function) with a matching type
                let cands: Vec<(u64, u32)> = match self.t.as_lit(i) {
                    Some(k) => tab
                        .get(k as usize)
                        .copied()
                        .flatten()
                        .filter(|&f| ok_ty(f))
                        .map(|f| vec![(k, f)])
                        .unwrap_or_default(),
                    None => tab
                        .iter()
                        .enumerate()
                        .filter_map(|(k, f)| f.filter(|&f| ok_ty(f)).map(|f| (k as u64, f)))
                        .collect(),
                };
                let mut conds = Vec::new();
                let mut snaps = Vec::new();
                let entry = cur.clone();
                let leaks0 = self.leaks;
                for (k, f) in cands {
                    let kk = self.t.lit(k, 32);
                    let c = self.t.eq(i, kk);
                    conds.push(c);
                    let mut c2 = entry.clone();
                    c2.guard = self.t.and2(entry.guard, c);
                    if self.t.is_false(c2.guard) {
                        continue;
                    }
                    self.call_fn(inst, f, &mut c2, depth)?;
                    if !self.t.is_false(c2.guard) {
                        snaps.push(Self::snap(&c2, want.results.len()));
                    }
                }
                let any = self.t.or(&conds);
                let bad = self.t.not(any);
                let mut base = entry.clone();
                self.trap(&mut base, bad, labels);
                let outer = entry.stack[..entry.stack.len() - want.params.len()].to_vec();
                let mut c3 = base;
                c3.guard = self.t.ff();
                let _ = leaks0;
                self.join(
                    &mut c3,
                    outer,
                    snaps,
                    want.results.len(),
                    None,
                    &want.results,
                );
                c3.locals = entry.locals;
                *cur = c3;
            }
        }
        Ok(())
    }

    /// An annotation formula (Bool, or `sort`) over the current frame:
    /// local names, `old.NAME` (entry values) and `g.NAME` (globals).
    fn loop_formula(&mut self, inst: usize, text: &str, cur: &Cur, sort: Option<Sort>) -> Id {
        let m = self.insts[inst].m.clone();
        let names = m.local_names.get(&cur.func);
        let mut binds = Vec::new();
        for (i, &v) in cur.locals.iter().enumerate() {
            let n = names
                .and_then(|ns| ns.get(&(i as u32)).cloned())
                .unwrap_or_else(|| format!("l{i}"));
            binds.push((n.clone(), v));
            if let Some(&e) = cur.entry.get(i) {
                binds.push((format!("old.{n}"), e));
            }
        }
        for (gi, &slot) in self.insts[inst].globals.iter().enumerate() {
            binds.push((format!("g.{}", m.global_name(gi as u32)), cur.st.g[slot]));
        }
        let text = old_syntax(text);
        self.t.raw_let(&text, binds, sort.unwrap_or(Sort::Bool))
    }

    /// What `body` (and the functions it calls) may write.
    fn writes(
        &self,
        inst: usize,
        body: &[Ins],
        w: &mut Writes,
        seen: &mut std::collections::HashSet<(usize, u32)>,
    ) {
        for ins in body {
            match ins {
                Ins::LocalSet(l) | Ins::LocalTee(l) => {
                    w.locals.insert(*l);
                }
                Ins::GlobalSet(g) => {
                    w.globals.insert(self.insts[inst].globals[*g as usize]);
                }
                Ins::Store { mem, .. }
                | Ins::MemoryCopy { dst: mem, .. }
                | Ins::MemoryFill(mem) => {
                    w.mems.insert(self.insts[inst].mems[*mem as usize]);
                }
                Ins::Block { body, .. } | Ins::Loop { body, .. } => {
                    self.writes(inst, body, w, seen)
                }
                Ins::If { then, els, .. } => {
                    self.writes(inst, then, w, seen);
                    self.writes(inst, els, w, seen);
                }
                Ins::Call(f) => self.writes_call(inst, *f, w, seen),
                Ins::CallIndirect { table, .. } => {
                    let fs: Vec<u32> = self.insts[inst].m.tables[*table as usize]
                        .iter()
                        .flatten()
                        .copied()
                        .collect();
                    for f in fs {
                        self.writes_call(inst, f, w, seen);
                    }
                }
                _ => {}
            }
        }
    }

    fn writes_call(
        &self,
        inst: usize,
        f: u32,
        w: &mut Writes,
        seen: &mut std::collections::HashSet<(usize, u32)>,
    ) {
        if !seen.insert((inst, f)) {
            return;
        }
        match self.insts[inst].funcs[f as usize] {
            Ok(i) => {
                let m = self.insts[inst].m.clone();
                let mut inner = Writes::default();
                self.writes(inst, &m.funcs[i as usize].body, &mut inner, seen);
                w.globals.extend(inner.globals);
                w.mems.extend(inner.mems);
                w.hist |= inner.hist;
            }
            Err(h) => match self.hosts[h].model {
                HostModel::Wasm(k, g) => self.writes_call(k, g, w, seen),
                HostModel::EnvStore(_) => {
                    if let Some(e) = self.env_mem {
                        w.mems.insert(e);
                    }
                }
                HostModel::EnvLoad(_) => {}
                HostModel::Opaque => w.hist = true,
                HostModel::Contract(k) => {
                    if let ContractStyle::X86 { regs, mem } = &self.contracts[k].style {
                        w.globals.extend(regs.iter().map(|r| r.1));
                        w.mems.extend(mem.iter().copied());
                    }
                }
            },
        }
    }

    /// Summarise a *checking loop*: a loop that writes only locals, makes no
    /// calls of imports, and runs a counter `c` up to a literal bound
    /// (`c := c + 1; br_if (c <u N)`), every other local it writes being
    /// recomputed in each iteration. Its only effect besides the locals is to
    /// trap; the summary traps iff some `k` in the counter's range traps, with
    /// `k` a fresh constant (sound for validity queries: the existential is
    /// skolemised where it occurs positively, the universal instantiated
    /// where it occurs negatively; counterexamples become inconclusive,
    /// `summarised`).
    fn try_summarise(
        &mut self,
        inst: usize,
        depth: u32,
        body: &[Ins],
        cur: &mut Cur,
        labels: &mut Vec<Label>,
    ) -> Result<bool> {
        let mut w = Writes::default();
        self.writes(inst, body, &mut w, &mut Default::default());
        if !w.globals.is_empty() || !w.mems.is_empty() || w.hist || w.locals.is_empty() {
            return Ok(false);
        }
        let (traps0, leaks0, events0, cut0, obl0) = (
            self.traps.len(),
            self.leaks,
            self.events.len(),
            self.cutoffs.len(),
            self.obligations.len(),
        );
        let pend0: Vec<usize> = labels.iter().map(|l| l.pending.len()).collect();
        let mut c2 = cur.clone();
        let mut fresh = Vec::new();
        for &l in &w.locals {
            let so = self.t.sort(c2.locals[l as usize]);
            let v = self.t.fresh("sum.l", so);
            c2.locals[l as usize] = v;
            fresh.push((l, v));
        }
        labels.push(Label {
            arity: 0,
            pending: vec![],
            leaked: false,
        });
        let r = self.exec(inst, depth, body, &mut c2, labels);
        let lab = labels.pop().unwrap();
        let restore = |me: &mut Self, labels: &mut Vec<Label>| {
            me.traps.truncate(traps0);
            me.leaks = leaks0;
            me.events.truncate(events0);
            me.cutoffs.truncate(cut0);
            me.obligations.truncate(obl0);
            for (l, &n) in labels.iter_mut().zip(&pend0) {
                l.pending.truncate(n);
            }
        };
        let ok = r.is_ok()
            && lab.pending.len() == 1
            && self.events.len() == events0
            && self.cutoffs.len() == cut0
            && self.obligations.len() == obl0
            && labels
                .iter()
                .zip(&pend0)
                .all(|(l, &n)| l.pending.len() == n);
        if !ok {
            restore(self, labels);
            return Ok(false);
        }
        let back = &lab.pending[0];
        // the counter and the bound
        let mut found = None;
        for &(l, v) in &fresh {
            let one = self.t.lit(1, self.t.width(v));
            let next = self.t.bin(Bv2::Add, v, one);
            if back.locals[l as usize] != next {
                continue;
            }
            let conj: Vec<Id> = match self.t.node(back.guard) {
                N::And(xs) => xs.clone(),
                _ => vec![back.guard],
            };
            for &cj in &conj {
                if let N::Rel(Rel::Ult, a, nb) = self.t.node(cj).clone()
                    && a == next
                    && self.t.as_lit(nb).is_some()
                {
                    let rest: Vec<Id> = conj.iter().copied().filter(|&x| x != cj).collect();
                    found = Some((l, v, next, nb, cj, rest));
                }
            }
        }
        let Some((cl, cv, _next, nb, rcond, rest)) = found else {
            restore(self, labels);
            return Ok(false);
        };
        let x = self.t.and(&rest);
        let nr = self.t.not(rcond);
        let exit = self.t.and2(x, nr);
        let new_traps: Vec<Id> = self.traps[traps0..].iter().map(|t| t.0).collect();
        let tr = self.t.or(&new_traps);
        // the exit is the complement of the back edge among non-trapping paths
        let ntr = self.t.not(tr);
        let x_expect = self.t.and2(cur.guard, ntr);
        let _ = x_expect;
        if c2.guard != exit {
            restore(self, labels);
            return Ok(false);
        }
        // independence of the other written locals
        let roots = [tr, rcond];
        for &(l, v) in &fresh {
            if l != cl && roots.iter().any(|&r| self.t.occurs(v, r)) {
                restore(self, labels);
                return Ok(false);
            }
        }
        restore(self, labels);
        let wdt = self.t.width(cv);
        let k = self.t.fresh("sum.k", Sort::Bv(wdt));
        let mut map = std::collections::HashMap::new();
        map.insert(cv, k);
        let tk = self.t.subst(tr, &map);
        let c0 = cur.locals[cl as usize];
        let e0 = self.t.eq(k, c0);
        let a1 = self.t.rel(Rel::Ule, c0, k);
        let a2 = self.t.rel(Rel::Ult, k, nb);
        let inr = self.t.and2(a1, a2);
        let dom = self.t.or2(e0, inr);
        let tsum = self.t.and2(dom, tk);
        self.summarised = true;
        let tt = self.t.tt();
        let _ = tt;
        self.trap(cur, tsum, labels);
        // locals after the loop
        let c0lt = self.t.rel(Rel::Ult, c0, nb);
        let one = self.t.lit(1, wdt);
        let c1 = self.t.bin(Bv2::Add, c0, one);
        cur.locals[cl as usize] = self.t.ite(c0lt, nb, c1);
        for &(l, v) in &fresh {
            if l != cl {
                let so = self.t.sort(v);
                cur.locals[l as usize] = self.t.fresh("sum.after", so);
            }
        }
        Ok(true)
    }

    fn call_contract(&mut self, c: &Contract, host: &Host, args: Vec<Id>, cur: &mut Cur) {
        match &c.style {
            ContractStyle::Values { params, results } => {
                let mut binds: Vec<(String, Id)> =
                    params.iter().cloned().zip(args.iter().copied()).collect();
                let pre = self.t.raw_let(&c.pre, binds.clone(), Sort::Bool);
                let ob = self.t.implies(cur.guard, pre);
                self.obligations
                    .push((format!("call {}: requires", c.name), ob));
                let mut rs = Vec::new();
                for (k, r) in host.ty.results.iter().enumerate() {
                    let v = self
                        .t
                        .fresh(&format!("{}.result{k}", c.name), Sort::Bv(r.width()));
                    if k == 0 {
                        binds.push(("result".into(), v));
                    }
                    if let Some(n) = results.get(k) {
                        binds.push((format!("result.{n}"), v));
                    }
                    rs.push(v);
                }
                let post = self.t.raw_let(&c.post, binds, Sort::Bool);
                cur.guard = self.t.and2(cur.guard, post);
                cur.stack.extend(rs);
            }
            ContractStyle::X86 { regs, mem } => {
                let wide = |t: &mut Terms, v: Id| {
                    let w = t.width(v);
                    t.zext(64 - w, v)
                };
                let mut binds = Vec::new();
                let old: Vec<Id> = regs.iter().map(|r| cur.st.g[r.1]).collect();
                for (r, &v) in regs.iter().zip(&old) {
                    let x = wide(&mut self.t, v);
                    binds.push((format!("old.{}", r.0), x));
                }
                let pre = self.t.raw_let(&c.pre, binds.clone(), Sort::Bool);
                let ob = self.t.implies(cur.guard, pre);
                self.obligations
                    .push((format!("call {}: requires", c.name), ob));
                let find = |n: &str| regs.iter().position(|r| r.0 == n);
                let rsp_old = find("rsp").map(|i| old[i]);
                for (i, r) in regs.iter().enumerate() {
                    let keep =
                        ["rbx", "rbp", "r12", "r13", "r14", "r15", "df"].contains(&r.0.as_str());
                    let v = if keep {
                        old[i]
                    } else if r.0 == "rsp" {
                        let k = self.t.lit(8, 64);
                        self.t.bin(Bv2::Add, old[i], k)
                    } else if r.0 == "rip"
                        && let Some(mi) = mem
                        && let Some(a) = rsp_old
                    {
                        let m = cur.st.m[*mi];
                        let aw = match self.t.sort(m) {
                            Sort::Mem(aw) => aw,
                            _ => 64,
                        };
                        let a = if aw < 64 {
                            self.t.extract(aw - 1, 0, a)
                        } else {
                            a
                        };
                        self.t.load_le(m, a, 8)
                    } else {
                        let so = self.t.sort(old[i]);
                        self.t.fresh(&format!("{}.{}", c.name, r.0), so)
                    };
                    cur.st.g[r.1] = v;
                    let x = wide(&mut self.t, v);
                    binds.push((r.0.clone(), x));
                }
                if let (Some(ms), Some(sp)) = (mem, rsp_old) {
                    let m = cur.st.m[*ms];
                    let so = self.t.sort(m);
                    let aw = match so {
                        Sort::Mem(aw) => aw,
                        _ => 64,
                    };
                    let f = self.t.fresh(&format!("{}.mem", c.name), so);
                    let spw = if aw < 64 {
                        self.t.extract(aw - 1, 0, sp)
                    } else {
                        sp
                    };
                    let text = format!(
                        "(lambda ((a!f (_ BitVec {aw}))) (ite (bvult (bvsub a!f (bvsub sp (_ bv4096 {aw}))) (_ bv4096 {aw})) (select f a!f) (select m a!f)))"
                    );
                    let nm = self.t.raw_let(
                        &text,
                        vec![("sp".into(), spw), ("f".into(), f), ("m".into(), m)],
                        so,
                    );
                    cur.st.m[*ms] = nm;
                }
                let post = self.t.raw_let(&c.post, binds, Sort::Bool);
                cur.guard = self.t.and2(cur.guard, post);
                for r in &host.ty.results {
                    let z = self.t.lit(0, r.width());
                    cur.stack.push(z);
                }
            }
        }
    }

    /// Trap unless `[a, a + n)` lies in the memory.
    fn range_check(&mut self, slot: usize, a: Id, n: Id, cur: &mut Cur, labels: &mut [Label]) {
        let size = self.msize[slot].unwrap_or(1 << 32);
        let a64 = self.t.zext(32, a);
        let n64 = self.t.zext(32, n);
        let e = self.t.bin(Bv2::Add, a64, n64);
        let sz = self.t.lit(size, 64);
        let oob = self.t.rel(Rel::Ult, sz, e);
        self.trap(cur, oob, labels);
    }

    /// Effective address (32-bit) of an access of `n` bytes, with the
    /// out-of-bounds trap.
    fn addr(
        &mut self,
        slot: usize,
        a: Id,
        offset: u64,
        n: u32,
        cur: &mut Cur,
        labels: &mut [Label],
    ) -> Id {
        let size = self.msize[slot].unwrap_or(1 << 32);
        let a64 = self.t.zext(32, a);
        let end = self.t.lit(offset + n as u64, 64);
        let e = self.t.bin(Bv2::Add, a64, end);
        let sz = self.t.lit(size, 64);
        let oob = self.t.rel(Rel::Ult, sz, e);
        self.trap(cur, oob, labels);
        let off = self.t.lit(offset, 64);
        let ea = self.t.bin(Bv2::Add, a64, off);
        self.t.extract(31, 0, ea)
    }

    fn binop(
        &mut self,
        op: BinOp,
        w: u32,
        a: Id,
        b: Id,
        cur: &mut Cur,
        labels: &mut [Label],
    ) -> Id {
        let t = &mut self.t;
        let shift_amount = |t: &mut Terms, b: Id| {
            let m = t.lit((w - 1) as u64, w);
            t.bin(Bv2::And, b, m)
        };
        match op {
            BinOp::Add => t.bin(Bv2::Add, a, b),
            BinOp::Sub => t.bin(Bv2::Sub, a, b),
            BinOp::Mul => t.bin(Bv2::Mul, a, b),
            BinOp::And => t.bin(Bv2::And, a, b),
            BinOp::Or => t.bin(Bv2::Or, a, b),
            BinOp::Xor => t.bin(Bv2::Xor, a, b),
            BinOp::Shl => {
                let k = shift_amount(t, b);
                t.bin(Bv2::Shl, a, k)
            }
            BinOp::ShrU => {
                let k = shift_amount(t, b);
                t.bin(Bv2::Lshr, a, k)
            }
            BinOp::ShrS => {
                let k = shift_amount(t, b);
                t.bin(Bv2::Ashr, a, k)
            }
            BinOp::Rotl | BinOp::Rotr => {
                let k = shift_amount(t, b);
                let wl = t.lit(w as u64, w);
                let k2 = t.bin(Bv2::Sub, wl, k);
                let k2 = shift_amount(t, k2);
                let (l, r) = if op == BinOp::Rotl { (k, k2) } else { (k2, k) };
                let x = t.bin(Bv2::Shl, a, l);
                let y = t.bin(Bv2::Lshr, a, r);
                t.bin(Bv2::Or, x, y)
            }
            BinOp::DivU | BinOp::RemU | BinOp::DivS | BinOp::RemS => {
                let z = t.lit(0, w);
                let mut bad = t.eq(b, z);
                if op == BinOp::DivS {
                    let min = t.lit(1u64 << (w - 1), w);
                    let m1 = t.lit(u64::MAX, w);
                    let e1 = t.eq(a, min);
                    let e2 = t.eq(b, m1);
                    let ov = t.and2(e1, e2);
                    bad = t.or2(bad, ov);
                }
                self.trap(cur, bad, labels);
                let o = match op {
                    BinOp::DivU => Bv2::Udiv,
                    BinOp::RemU => Bv2::Urem,
                    BinOp::DivS => Bv2::Sdiv,
                    _ => Bv2::Srem,
                };
                self.t.bin(o, a, b)
            }
        }
    }
}
