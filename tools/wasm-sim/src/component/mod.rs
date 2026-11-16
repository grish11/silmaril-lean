//! Linking/packaging variants: preparing the core modules for the component model.
//!
//! `componentize_names` rewrites a core module's import and export *names* (and nothing
//! else) to the canonical-ABI names of `examples/wasm-sim/wit/sim.wit`
//! (`wsim:sim/mem@0.1.0` / `load8`, `wsim:sim/state@0.1.0#get`, `_` -> `-`), so
//! `wasm-tools component embed/new` can wrap the very same code. A memory imported from `io`
//! (shared WASI memory of the core-module variants) becomes a defined memory: components do
//! not share memories.

use wasm_encoder::{
    ExportKind, ExportSection, ImportSection, MemorySection, MemoryType, Module, RawSection,
    SectionId,
};
use wasmparser::{Parser, Payload, TypeRef};
use wasmtime::{Result, bail};

pub const PKG: &str = "wsim:sim";
pub const VER: &str = "0.1.0";

fn iface(i: &str) -> String {
    format!("{PKG}/{i}@{VER}")
}

/// Interface of an imported (module, field).
fn import_iface(module: &str, field: &str) -> Option<&'static str> {
    Some(match (module, field) {
        ("mem", _) => "mem",
        ("sys", _) => "sys",
        ("nd", _) => "nd",
        ("ext", _) => "ext",
        ("ffi", _) => "ffi",
        ("sim" | "core", "get" | "set" | "modelled") => "state",
        ("sim" | "core", "step" | "run") => "isa",
        ("sim" | "core", "set_ext") => "ext-range",
        _ => return None,
    })
}

/// Interface of an exported function (`nparams` disambiguates `call`).
fn export_iface(name: &str, nparams: usize) -> Option<&'static str> {
    Some(match name {
        "get" | "set" | "modelled" => "state",
        "step" | "run" => "isa",
        "set_ext" => "ext-range",
        "cond" | "ea" => "isa-x86",
        n if n.starts_with("i_") => "isa-x86",
        "load8" | "load16" | "load32" | "load64" | "store8" | "store16" | "store32" | "store64"
        | "map" | "mapped" => "mem",
        "syscall" | "set_brk" => "sys",
        "undef" => "nd",
        "call" if nparams == 1 => "ext",
        "call" | "ret" => "ffi",
        _ => return None,
    })
}

fn kebab(s: &str) -> String {
    s.replace('_', "-")
}

/// Rewrite names; keep only exports of the interfaces in `keep` (plus `memory`, `_start`).
pub fn componentize_names(wasm: &[u8], keep: &[&str]) -> Result<Vec<u8>> {
    let mut out = Module::new();
    let mut func_types: Vec<usize> = vec![]; // params per type
    let mut funcs: Vec<usize> = vec![]; // type index per function (imports first)
    let mut io_memory: Option<MemoryType> = None;
    let mut had_memory_section = false;
    let mut pending_memory = false;
    for payload in Parser::new(0).parse_all(wasm) {
        let payload = payload?;
        if let Some((id, range)) = payload.as_section() {
            let range = range.start as usize..range.end as usize;
            // insert a defined memory replacing `io.memory`, at its section position
            if pending_memory
                && id > SectionId::Memory as u8
                && id != SectionId::Custom as u8
                && id != 13
            {
                if !had_memory_section {
                    let mut ms = MemorySection::new();
                    ms.memory(io_memory.unwrap());
                    out.section(&ms);
                }
                pending_memory = false;
            }
            match payload {
                Payload::TypeSection(r) => {
                    for rg in r {
                        for t in rg?.into_types() {
                            func_types.push(t.unwrap_func().params().len());
                        }
                    }
                    out.section(&RawSection {
                        id,
                        data: &wasm[range],
                    });
                }
                Payload::ImportSection(r) => {
                    let mut is = ImportSection::new();
                    for imp in r.into_imports() {
                        let imp = imp?;
                        if imp.module == "io" {
                            let TypeRef::Memory(m) = imp.ty else {
                                bail!("io import must be a memory")
                            };
                            io_memory = Some(MemoryType {
                                minimum: m.initial,
                                maximum: m.maximum,
                                memory64: m.memory64,
                                shared: m.shared,
                                page_size_log2: m.page_size_log2,
                            });
                            pending_memory = true;
                            continue;
                        }
                        let (module, name) = match import_iface(imp.module, imp.name) {
                            Some(i) => (iface(i), kebab(imp.name)),
                            None => (imp.module.to_string(), imp.name.to_string()),
                        };
                        let ty: wasm_encoder::EntityType = match imp.ty {
                            TypeRef::Func(t) => {
                                funcs.push(t as usize);
                                wasm_encoder::EntityType::Function(t)
                            }
                            other => bail!(
                                "unsupported import kind {other:?} of {}.{}",
                                imp.module,
                                imp.name
                            ),
                        };
                        is.import(&module, &name, ty);
                    }
                    out.section(&is);
                }
                Payload::FunctionSection(r) => {
                    for t in r {
                        funcs.push(t? as usize);
                    }
                    out.section(&RawSection {
                        id,
                        data: &wasm[range],
                    });
                }
                Payload::MemorySection(r) => {
                    had_memory_section = true;
                    let mut ms = MemorySection::new();
                    if let Some(m) = io_memory {
                        ms.memory(m);
                    }
                    for m in r {
                        let m = m?;
                        ms.memory(MemoryType {
                            minimum: m.initial,
                            maximum: m.maximum,
                            memory64: m.memory64,
                            shared: m.shared,
                            page_size_log2: m.page_size_log2,
                        });
                    }
                    out.section(&ms);
                    pending_memory = false;
                }
                Payload::ExportSection(r) => {
                    let mut es = ExportSection::new();
                    for e in r {
                        let e = e?;
                        match e.kind {
                            wasmparser::ExternalKind::Func => {
                                let np = func_types[funcs[e.index as usize]];
                                if e.name == "_start" {
                                    es.export("_start", ExportKind::Func, e.index);
                                } else if let Some(i) =
                                    export_iface(e.name, np).filter(|i| keep.contains(i))
                                {
                                    es.export(
                                        &format!("{}#{}", iface(i), kebab(e.name)),
                                        ExportKind::Func,
                                        e.index,
                                    );
                                }
                            }
                            wasmparser::ExternalKind::Memory if e.name == "memory" => {
                                es.export("memory", ExportKind::Memory, e.index);
                            }
                            _ => {}
                        }
                    }
                    out.section(&es);
                }
                Payload::CustomSection(_) => {} // drop names etc.
                _ => {
                    out.section(&RawSection {
                        id,
                        data: &wasm[range],
                    });
                }
            }
        }
    }
    Ok(out.finish())
}
