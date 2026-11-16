//! Core Wasm modules for symbolic execution: a WAT/Wasm file is parsed and
//! validated with `wasmparser`, and function bodies are turned into a
//! structured instruction tree over the integer fragment (i32/i64 numerics,
//! locals, globals, memories, `block`/`loop`/`if`/`br*`/`br_table`, calls,
//! `call_indirect` through constant tables). Floats, SIMD, references and the
//! other proposals are rejected when a function using them is executed.

use anyhow::{Context, Result, bail};
use std::collections::BTreeMap;
use std::path::Path;
use wasmparser::{
    BlockType, DataKind, ElementItems, ElementKind, ExternalKind, KnownCustom, Name, Operator,
    Parser, Payload, TypeRef, ValType,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Ty {
    I32,
    I64,
}

impl Ty {
    pub fn width(self) -> u32 {
        match self {
            Ty::I32 => 32,
            Ty::I64 => 64,
        }
    }
}

fn ty_of(v: ValType) -> Result<Ty> {
    match v {
        ValType::I32 => Ok(Ty::I32),
        ValType::I64 => Ok(Ty::I64),
        other => bail!("unsupported value type {other:?} (integer fragment only)"),
    }
}

#[derive(Clone, Debug)]
pub struct FnTy {
    pub params: Vec<Ty>,
    pub results: Vec<Ty>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    DivS,
    DivU,
    RemS,
    RemU,
    And,
    Or,
    Xor,
    Shl,
    ShrS,
    ShrU,
    Rotl,
    Rotr,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UnOp {
    Clz,
    Ctz,
    Popcnt,
    Eqz,
    Ext8S,
    Ext16S,
    Ext32S,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CmpOp {
    Eq,
    Ne,
    LtS,
    LtU,
    GtS,
    GtU,
    LeS,
    LeU,
    GeS,
    GeU,
}

/// A structured instruction.
#[derive(Clone, Debug)]
pub enum Ins {
    Unreachable,
    Nop,
    Block {
        params: usize,
        results: usize,
        body: Vec<Ins>,
    },
    /// `id`: pre-order number of the loop in its function.
    Loop {
        params: usize,
        results: usize,
        body: Vec<Ins>,
        id: u32,
    },
    If {
        params: usize,
        results: usize,
        then: Vec<Ins>,
        els: Vec<Ins>,
    },
    Br(u32),
    BrIf(u32),
    BrTable(Vec<u32>, u32),
    Return,
    Call(u32),
    CallIndirect {
        ty: u32,
        table: u32,
    },
    Drop,
    Select,
    LocalGet(u32),
    LocalSet(u32),
    LocalTee(u32),
    GlobalGet(u32),
    GlobalSet(u32),
    /// `bytes`, sign-extending load into `ty`.
    Load {
        ty: Ty,
        bytes: u32,
        signed: bool,
        mem: u32,
        offset: u64,
    },
    Store {
        bytes: u32,
        mem: u32,
        offset: u64,
    },
    MemorySize(u32),
    MemoryGrow(u32),
    MemoryCopy {
        dst: u32,
        src: u32,
    },
    MemoryFill(u32),
    Const32(u32),
    Const64(u64),
    Un(Ty, UnOp),
    Bin(Ty, BinOp),
    /// Comparison; the operand width comes from the operands themselves.
    Cmp(CmpOp),
    Wrap,
    ExtendS,
    ExtendU,
    /// An operator outside the fragment; executing it is an error.
    Unsupported(String),
}

#[derive(Clone, Debug)]
pub struct Func {
    pub ty: u32,
    /// Declared locals (after the parameters).
    pub locals: Vec<Ty>,
    pub body: Vec<Ins>,
}

#[derive(Clone, Debug)]
pub struct ImportFn {
    pub module: String,
    pub name: String,
    pub ty: u32,
}

#[derive(Clone, Debug)]
pub struct Global {
    pub ty: Ty,
    pub mutable: bool,
    /// Constant initial value (`None` when initialised from an imported global).
    pub init: Option<u64>,
    pub name: Option<String>,
}

#[derive(Clone, Debug)]
pub struct Memory {
    /// `module.name` of an imported memory.
    pub import: Option<String>,
    pub min_pages: u64,
}

#[derive(Clone, Debug)]
pub struct Data {
    pub mem: u32,
    pub offset: u64,
    pub bytes: Vec<u8>,
}

#[derive(Clone, Debug, Default)]
pub struct Module {
    pub types: Vec<FnTy>,
    pub imports: Vec<ImportFn>,
    pub funcs: Vec<Func>,
    pub globals: Vec<Global>,
    pub memories: Vec<Memory>,
    /// Table contents after active element segments (function indices).
    pub tables: Vec<Vec<Option<u32>>>,
    pub exports: BTreeMap<String, (ExternalKind, u32)>,
    pub data: Vec<Data>,
    pub func_names: BTreeMap<u32, String>,
    /// Local names (function index → local index → name), from the name section.
    pub local_names: BTreeMap<u32, BTreeMap<u32, String>>,
    pub start: Option<u32>,
}

impl Module {
    pub fn load(path: &Path) -> Result<Module> {
        let bytes = if path.extension().is_some_and(|e| e == "wasm") {
            std::fs::read(path)?
        } else {
            let src = std::fs::read_to_string(path)
                .with_context(|| format!("reading {}", path.display()))?;
            wat::parse_str(&src).with_context(|| format!("parsing {}", path.display()))?
        };
        Module::from_bytes(&bytes).with_context(|| format!("loading {}", path.display()))
    }

    #[cfg(test)]
    pub fn from_wat(src: &str) -> Result<Module> {
        Module::from_bytes(&wat::parse_str(src)?)
    }

    pub fn from_bytes(bytes: &[u8]) -> Result<Module> {
        wasmparser::Validator::new()
            .validate_all(bytes)
            .context("validation")?;
        let mut m = Module::default();
        let mut func_tys: Vec<u32> = Vec::new();
        let mut global_names = BTreeMap::new();
        let mut table_sizes = Vec::new();
        for p in Parser::new(0).parse_all(bytes) {
            match p? {
                Payload::TypeSection(r) => {
                    for ft in r.into_iter_err_on_gc_types() {
                        let ft = ft?;
                        // Types with non-integer values are kept (as empty) so that indices
                        // stay right; functions using them fail when executed.
                        let params: Result<Vec<_>> =
                            ft.params().iter().map(|&v| ty_of(v)).collect();
                        let results: Result<Vec<_>> =
                            ft.results().iter().map(|&v| ty_of(v)).collect();
                        m.types.push(match (params, results) {
                            (Ok(params), Ok(results)) => FnTy { params, results },
                            _ => FnTy {
                                params: vec![],
                                results: vec![],
                            },
                        });
                    }
                }
                Payload::ImportSection(r) => {
                    for imp in r.into_imports() {
                        let imp = imp?;
                        match imp.ty {
                            TypeRef::Func(t) | TypeRef::FuncExact(t) => m.imports.push(ImportFn {
                                module: imp.module.into(),
                                name: imp.name.into(),
                                ty: t,
                            }),
                            TypeRef::Global(g) => m.globals.push(Global {
                                ty: ty_of(g.content_type)?,
                                mutable: g.mutable,
                                init: None,
                                name: Some(format!("{}.{}", imp.module, imp.name)),
                            }),
                            TypeRef::Memory(mt) => {
                                if mt.memory64 {
                                    bail!("memory64 is not supported");
                                }
                                m.memories.push(Memory {
                                    import: Some(format!("{}.{}", imp.module, imp.name)),
                                    min_pages: mt.initial,
                                })
                            }
                            other => bail!(
                                "unsupported import {}.{} ({other:?}): only functions, globals and memories",
                                imp.module,
                                imp.name
                            ),
                        }
                    }
                }
                Payload::FunctionSection(r) => {
                    for t in r {
                        func_tys.push(t?);
                    }
                }
                Payload::TableSection(r) => {
                    for t in r {
                        let t = t?;
                        table_sizes.push(t.ty.initial);
                    }
                }
                Payload::MemorySection(r) => {
                    for mt in r {
                        let mt = mt?;
                        if mt.memory64 {
                            bail!("memory64 is not supported");
                        }
                        m.memories.push(Memory {
                            import: None,
                            min_pages: mt.initial,
                        });
                    }
                }
                Payload::GlobalSection(r) => {
                    for g in r {
                        let g = g?;
                        m.globals.push(Global {
                            ty: ty_of(g.ty.content_type)?,
                            mutable: g.ty.mutable,
                            init: const_expr(&g.init_expr),
                            name: None,
                        });
                    }
                }
                Payload::ExportSection(r) => {
                    for e in r {
                        let e = e?;
                        m.exports.insert(e.name.to_string(), (e.kind, e.index));
                    }
                }
                Payload::StartSection { func, .. } => m.start = Some(func),
                Payload::ElementSection(r) => {
                    if m.tables.is_empty() {
                        m.tables = table_sizes
                            .iter()
                            .map(|&n| vec![None; n as usize])
                            .collect();
                    }
                    for e in r {
                        let e = e?;
                        if let ElementKind::Active {
                            table_index,
                            offset_expr,
                        } = e.kind
                        {
                            let t = table_index.unwrap_or(0) as usize;
                            let off = const_expr(&offset_expr).context("element offset")? as usize;
                            let items: Vec<Option<u32>> = match e.items {
                                ElementItems::Functions(fs) => fs
                                    .into_iter()
                                    .map(|f| f.map(Some))
                                    .collect::<Result<_, _>>()?,
                                ElementItems::Expressions(_, es) => es
                                    .into_iter()
                                    .map(|x| x.map(|x| ref_func(&x)))
                                    .collect::<Result<_, _>>()?,
                            };
                            for (k, f) in items.into_iter().enumerate() {
                                if let Some(slot) = m.tables[t].get_mut(off + k) {
                                    *slot = f;
                                }
                            }
                        }
                    }
                }
                Payload::DataSection(r) => {
                    for d in r {
                        let d = d?;
                        if let DataKind::Active {
                            memory_index,
                            offset_expr,
                        } = d.kind
                        {
                            m.data.push(Data {
                                mem: memory_index,
                                offset: const_expr(&offset_expr).context("data offset")?,
                                bytes: d.data.to_vec(),
                            });
                        }
                    }
                }
                Payload::CodeSectionEntry(body) => {
                    let idx = m.funcs.len();
                    let ty = *func_tys.get(idx).context("code without function")?;
                    let mut locals = Vec::new();
                    let mut bad_local = None;
                    for l in body.get_locals_reader()? {
                        let (n, v) = l?;
                        match ty_of(v) {
                            Ok(t) => locals.extend(std::iter::repeat_n(t, n as usize)),
                            Err(e) => bad_local = Some(e.to_string()),
                        }
                    }
                    let mut ops = Vec::new();
                    for op in body.get_operators_reader()? {
                        ops.push(op?);
                    }
                    let mut pos = 0;
                    let mut loops = 0;
                    let mut body = structure(&ops, &mut pos, &m.types, &mut loops)?;
                    if let Some(e) = bad_local {
                        body = vec![Ins::Unsupported(e)];
                    }
                    m.funcs.push(Func { ty, locals, body });
                }
                Payload::CustomSection(c) => {
                    if let KnownCustom::Name(r) = c.as_known() {
                        for n in r.into_iter().flatten() {
                            match n {
                                Name::Function(map) => {
                                    for nm in map.into_iter().flatten() {
                                        m.func_names.insert(nm.index, nm.name.to_string());
                                    }
                                }
                                Name::Local(map) => {
                                    for fl in map.into_iter().flatten() {
                                        let mut names = BTreeMap::new();
                                        for nm in fl.names.flatten() {
                                            names.insert(nm.index, nm.name.to_string());
                                        }
                                        m.local_names.insert(fl.index, names);
                                    }
                                }
                                Name::Global(map) => {
                                    for nm in map.into_iter().flatten() {
                                        global_names.insert(nm.index, nm.name.to_string());
                                    }
                                }
                                _ => {}
                            }
                        }
                    }
                }
                _ => {}
            }
        }
        if m.tables.is_empty() {
            m.tables = table_sizes
                .iter()
                .map(|&n| vec![None; n as usize])
                .collect();
        }
        for (i, g) in m.globals.iter_mut().enumerate() {
            if let Some(n) = global_names.get(&(i as u32)) {
                g.name = Some(n.clone());
            }
        }
        Ok(m)
    }

    pub fn n_imports(&self) -> u32 {
        self.imports.len() as u32
    }

    /// Type of function `f` in the function index space.
    pub fn func_ty(&self, f: u32) -> &FnTy {
        let t = if f < self.n_imports() {
            self.imports[f as usize].ty
        } else {
            self.funcs[(f - self.n_imports()) as usize].ty
        };
        &self.types[t as usize]
    }

    /// A function by export name, `$name` (name section) or index.
    pub fn find_func(&self, name: &str) -> Result<u32> {
        if let Some(n) = name.strip_prefix('$') {
            return self
                .func_names
                .iter()
                .find(|(_, v)| v.as_str() == n)
                .map(|(k, _)| *k)
                .with_context(|| format!("no function ${n}"));
        }
        if let Some((ExternalKind::Func, i)) = self.exports.get(name) {
            return Ok(*i);
        }
        if let Ok(i) = name.parse::<u32>() {
            return Ok(i);
        }
        bail!("no exported function {name}")
    }

    /// A global by name (name section, with or without `$`), export name or index.
    pub fn find_global(&self, name: &str) -> Result<u32> {
        let n = name.strip_prefix('$').unwrap_or(name);
        if let Some(i) = self
            .globals
            .iter()
            .position(|g| g.name.as_deref() == Some(n))
        {
            return Ok(i as u32);
        }
        if let Some((ExternalKind::Global, i)) = self.exports.get(n) {
            return Ok(*i);
        }
        if let Ok(i) = n.parse::<u32>() {
            return Ok(i);
        }
        bail!("no global {name}")
    }

    pub fn func_name(&self, f: u32) -> String {
        if f < self.n_imports() {
            let i = &self.imports[f as usize];
            return format!("{}.{}", i.module, i.name);
        }
        self.func_names
            .get(&f)
            .cloned()
            .unwrap_or_else(|| format!("func{f}"))
    }

    pub fn global_name(&self, g: u32) -> String {
        self.globals[g as usize]
            .name
            .clone()
            .unwrap_or_else(|| format!("g{g}"))
    }
}

fn const_expr(e: &wasmparser::ConstExpr) -> Option<u64> {
    let mut r = e.get_operators_reader();
    match r.read().ok()? {
        Operator::I32Const { value } => Some(value as u32 as u64),
        Operator::I64Const { value } => Some(value as u64),
        _ => None,
    }
}

fn ref_func(e: &wasmparser::ConstExpr) -> Option<u32> {
    let mut r = e.get_operators_reader();
    match r.read().ok()? {
        Operator::RefFunc { function_index } => Some(function_index),
        _ => None,
    }
}

fn block_arity(bt: BlockType, types: &[FnTy]) -> (usize, usize) {
    match bt {
        BlockType::Empty => (0, 0),
        BlockType::Type(_) => (0, 1),
        BlockType::FuncType(t) => {
            let ft = &types[t as usize];
            (ft.params.len(), ft.results.len())
        }
    }
}

/// Structure a flat operator list from `pos` up to the matching `end`/`else`.
fn structure(
    ops: &[Operator],
    pos: &mut usize,
    types: &[FnTy],
    loops: &mut u32,
) -> Result<Vec<Ins>> {
    use Operator as O;
    let mut out = Vec::new();
    while *pos < ops.len() {
        let op = &ops[*pos];
        *pos += 1;
        let i32b = |o| Ins::Bin(Ty::I32, o);
        let i64b = |o| Ins::Bin(Ty::I64, o);
        let ld = |ty, bytes, signed, m: &wasmparser::MemArg| Ins::Load {
            ty,
            bytes,
            signed,
            mem: match m.target {
                wasmparser::MemArgTarget::Memory(k) => k,
                wasmparser::MemArgTarget::Array(_) => u32::MAX,
            },
            offset: m.offset,
        };
        let st = |bytes, m: &wasmparser::MemArg| Ins::Store {
            bytes,
            mem: match m.target {
                wasmparser::MemArgTarget::Memory(k) => k,
                wasmparser::MemArgTarget::Array(_) => u32::MAX,
            },
            offset: m.offset,
        };
        let ins = match op {
            O::End | O::Else => return Ok(out),
            O::Unreachable => Ins::Unreachable,
            O::Nop => Ins::Nop,
            O::Block { blockty } => {
                let (p, r) = block_arity(*blockty, types);
                Ins::Block {
                    params: p,
                    results: r,
                    body: structure(ops, pos, types, loops)?,
                }
            }
            O::Loop { blockty } => {
                let (p, r) = block_arity(*blockty, types);
                let id = *loops;
                *loops += 1;
                Ins::Loop {
                    params: p,
                    results: r,
                    body: structure(ops, pos, types, loops)?,
                    id,
                }
            }
            O::If { blockty } => {
                let (p, r) = block_arity(*blockty, types);
                let then = structure(ops, pos, types, loops)?;
                let els = if matches!(ops.get(*pos - 1), Some(O::Else)) {
                    structure(ops, pos, types, loops)?
                } else {
                    Vec::new()
                };
                Ins::If {
                    params: p,
                    results: r,
                    then,
                    els,
                }
            }
            O::Br { relative_depth } => Ins::Br(*relative_depth),
            O::BrIf { relative_depth } => Ins::BrIf(*relative_depth),
            O::BrTable { targets } => {
                let ts: Vec<u32> = targets.targets().collect::<Result<_, _>>()?;
                Ins::BrTable(ts, targets.default())
            }
            O::Return => Ins::Return,
            O::Call { function_index } => Ins::Call(*function_index),
            O::CallIndirect {
                type_index,
                table_index,
            } => Ins::CallIndirect {
                ty: *type_index,
                table: *table_index,
            },
            O::Drop => Ins::Drop,
            O::Select | O::TypedSelect { .. } => Ins::Select,
            O::LocalGet { local_index } => Ins::LocalGet(*local_index),
            O::LocalSet { local_index } => Ins::LocalSet(*local_index),
            O::LocalTee { local_index } => Ins::LocalTee(*local_index),
            O::GlobalGet { global_index } => Ins::GlobalGet(*global_index),
            O::GlobalSet { global_index } => Ins::GlobalSet(*global_index),
            O::I32Load { memarg } => ld(Ty::I32, 4, false, memarg),
            O::I64Load { memarg } => ld(Ty::I64, 8, false, memarg),
            O::I32Load8S { memarg } => ld(Ty::I32, 1, true, memarg),
            O::I32Load8U { memarg } => ld(Ty::I32, 1, false, memarg),
            O::I32Load16S { memarg } => ld(Ty::I32, 2, true, memarg),
            O::I32Load16U { memarg } => ld(Ty::I32, 2, false, memarg),
            O::I64Load8S { memarg } => ld(Ty::I64, 1, true, memarg),
            O::I64Load8U { memarg } => ld(Ty::I64, 1, false, memarg),
            O::I64Load16S { memarg } => ld(Ty::I64, 2, true, memarg),
            O::I64Load16U { memarg } => ld(Ty::I64, 2, false, memarg),
            O::I64Load32S { memarg } => ld(Ty::I64, 4, true, memarg),
            O::I64Load32U { memarg } => ld(Ty::I64, 4, false, memarg),
            O::I32Store { memarg } => st(4, memarg),
            O::I64Store { memarg } => st(8, memarg),
            O::I32Store8 { memarg } | O::I64Store8 { memarg } => st(1, memarg),
            O::I32Store16 { memarg } | O::I64Store16 { memarg } => st(2, memarg),
            O::I64Store32 { memarg } => st(4, memarg),
            O::MemorySize { mem } => Ins::MemorySize(*mem),
            O::MemoryGrow { mem } => Ins::MemoryGrow(*mem),
            O::MemoryCopy { dst_mem, src_mem } => Ins::MemoryCopy {
                dst: *dst_mem,
                src: *src_mem,
            },
            O::MemoryFill { mem } => Ins::MemoryFill(*mem),
            O::I32Const { value } => Ins::Const32(*value as u32),
            O::I64Const { value } => Ins::Const64(*value as u64),
            O::I32Eqz => Ins::Un(Ty::I32, UnOp::Eqz),
            O::I64Eqz => Ins::Un(Ty::I64, UnOp::Eqz),
            O::I32Clz => Ins::Un(Ty::I32, UnOp::Clz),
            O::I32Ctz => Ins::Un(Ty::I32, UnOp::Ctz),
            O::I32Popcnt => Ins::Un(Ty::I32, UnOp::Popcnt),
            O::I64Clz => Ins::Un(Ty::I64, UnOp::Clz),
            O::I64Ctz => Ins::Un(Ty::I64, UnOp::Ctz),
            O::I64Popcnt => Ins::Un(Ty::I64, UnOp::Popcnt),
            O::I32Extend8S => Ins::Un(Ty::I32, UnOp::Ext8S),
            O::I32Extend16S => Ins::Un(Ty::I32, UnOp::Ext16S),
            O::I64Extend8S => Ins::Un(Ty::I64, UnOp::Ext8S),
            O::I64Extend16S => Ins::Un(Ty::I64, UnOp::Ext16S),
            O::I64Extend32S => Ins::Un(Ty::I64, UnOp::Ext32S),
            O::I32Eq => Ins::Cmp(CmpOp::Eq),
            O::I32Ne => Ins::Cmp(CmpOp::Ne),
            O::I32LtS => Ins::Cmp(CmpOp::LtS),
            O::I32LtU => Ins::Cmp(CmpOp::LtU),
            O::I32GtS => Ins::Cmp(CmpOp::GtS),
            O::I32GtU => Ins::Cmp(CmpOp::GtU),
            O::I32LeS => Ins::Cmp(CmpOp::LeS),
            O::I32LeU => Ins::Cmp(CmpOp::LeU),
            O::I32GeS => Ins::Cmp(CmpOp::GeS),
            O::I32GeU => Ins::Cmp(CmpOp::GeU),
            O::I64Eq => Ins::Cmp(CmpOp::Eq),
            O::I64Ne => Ins::Cmp(CmpOp::Ne),
            O::I64LtS => Ins::Cmp(CmpOp::LtS),
            O::I64LtU => Ins::Cmp(CmpOp::LtU),
            O::I64GtS => Ins::Cmp(CmpOp::GtS),
            O::I64GtU => Ins::Cmp(CmpOp::GtU),
            O::I64LeS => Ins::Cmp(CmpOp::LeS),
            O::I64LeU => Ins::Cmp(CmpOp::LeU),
            O::I64GeS => Ins::Cmp(CmpOp::GeS),
            O::I64GeU => Ins::Cmp(CmpOp::GeU),
            O::I32Add => i32b(BinOp::Add),
            O::I32Sub => i32b(BinOp::Sub),
            O::I32Mul => i32b(BinOp::Mul),
            O::I32DivS => i32b(BinOp::DivS),
            O::I32DivU => i32b(BinOp::DivU),
            O::I32RemS => i32b(BinOp::RemS),
            O::I32RemU => i32b(BinOp::RemU),
            O::I32And => i32b(BinOp::And),
            O::I32Or => i32b(BinOp::Or),
            O::I32Xor => i32b(BinOp::Xor),
            O::I32Shl => i32b(BinOp::Shl),
            O::I32ShrS => i32b(BinOp::ShrS),
            O::I32ShrU => i32b(BinOp::ShrU),
            O::I32Rotl => i32b(BinOp::Rotl),
            O::I32Rotr => i32b(BinOp::Rotr),
            O::I64Add => i64b(BinOp::Add),
            O::I64Sub => i64b(BinOp::Sub),
            O::I64Mul => i64b(BinOp::Mul),
            O::I64DivS => i64b(BinOp::DivS),
            O::I64DivU => i64b(BinOp::DivU),
            O::I64RemS => i64b(BinOp::RemS),
            O::I64RemU => i64b(BinOp::RemU),
            O::I64And => i64b(BinOp::And),
            O::I64Or => i64b(BinOp::Or),
            O::I64Xor => i64b(BinOp::Xor),
            O::I64Shl => i64b(BinOp::Shl),
            O::I64ShrS => i64b(BinOp::ShrS),
            O::I64ShrU => i64b(BinOp::ShrU),
            O::I64Rotl => i64b(BinOp::Rotl),
            O::I64Rotr => i64b(BinOp::Rotr),
            O::I32WrapI64 => Ins::Wrap,
            O::I64ExtendI32S => Ins::ExtendS,
            O::I64ExtendI32U => Ins::ExtendU,
            other => Ins::Unsupported(format!("{other:?}")),
        };
        out.push(ins);
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn structures_blocks_and_names() {
        let m = Module::from_wat(
            r#"(module (global $g (mut i64) (i64.const 5))
                 (func $f (export "f") (param i32) (result i32)
                   (block $b (br_table $b $b (local.get 0)))
                   (if (result i32) (local.get 0) (then (i32.const 1)) (else (i32.const 2)))))"#,
        )
        .unwrap();
        assert_eq!(m.find_func("f").unwrap(), 0);
        assert_eq!(m.find_func("$f").unwrap(), 0);
        assert_eq!(m.find_global("g").unwrap(), 0);
        assert_eq!(m.globals[0].init, Some(5));
        let b = &m.funcs[0].body;
        assert!(matches!(&b[0], Ins::Block { body, .. } if matches!(body[1], Ins::BrTable(..))));
        assert!(matches!(&b[2], Ins::If { results: 1, els, .. } if els.len() == 1));
    }
}
