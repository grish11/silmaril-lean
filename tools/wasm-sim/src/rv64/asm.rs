//! Assembles an RV64 simulator module from the hand-written WAT parts in
//! `examples/wasm-sim/rv64/parts/`. A simulator is a point in a lattice:
//! (state representation) x (fetch) x (set of instruction groups). Groups that
//! are left out are replaced by stubs whose decode handlers return status 2,
//! and their `i_*` methods are not exported, so the export signature of a
//! smaller simulator is a subset of that of a larger one.

use std::path::{Path, PathBuf};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum State {
    G,
    M,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Fetch {
    /// code fetched through the `mem.load32` import (P-mem)
    Import,
    /// code in the simulator's own memory (P-data); needs a data segment
    Data,
}

/// Instruction groups and the decode handlers each one defines.
pub const GROUPS: &[(&str, &[&str])] = &[
    ("base", &["d_opimm", "d_op", "d_lui", "d_auipc"]),
    ("word", &["d_opimm32", "d_op32"]),
    ("mul", &["d_mul", "d_mul32"]),
    ("mem", &["d_load", "d_store"]),
    ("ctrl", &["d_branch", "d_jal", "d_jalr", "d_ebreak"]),
    ("sys", &["d_ecall"]),
];

/// Named lattice points: `base` = Silmaril.RiscV.Instr (21 instructions),
/// `alu` = Ext.Compute (register-only RV64IM), `nosys` = Ext.Instr,
/// `full` = Ext.Instr + ECALL.
pub fn named(name: &str) -> Option<Vec<&'static str>> {
    Some(match name {
        "base" => vec!["base"],
        "alu" => vec!["base", "word", "mul"],
        "nosys" => vec!["base", "word", "mul", "mem", "ctrl"],
        "full" => vec!["base", "word", "mul", "mem", "ctrl", "sys"],
        _ => return None,
    })
}

#[derive(Clone, Debug)]
pub struct Config {
    pub state: State,
    pub fetch: Fetch,
    pub groups: Vec<&'static str>,
}

impl Config {
    pub fn new(state: State, level: &str) -> Config {
        Config {
            state,
            fetch: Fetch::Import,
            groups: named(level).unwrap_or_else(|| panic!("unknown level {level}")),
        }
    }
}

pub fn parts_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/wasm-sim/rv64/parts")
}

fn read(name: &str) -> String {
    let p = parts_dir().join(name);
    std::fs::read_to_string(&p).unwrap_or_else(|e| panic!("{}: {e}", p.display()))
}

/// Split a part into (imports, body) at the `;;@body` marker.
fn split(src: &str) -> (String, String) {
    match src.find(";;@body") {
        Some(i) => (src[..i].to_string(), src[i + 7..].to_string()),
        None => (String::new(), src.to_string()),
    }
}

/// WAT text of the simulator. `extra` is appended inside the module (e.g. the
/// P-data globals and data segment).
pub fn build(cfg: &Config, extra: &str) -> String {
    let mut imports = String::new();
    let mut body = String::new();
    let mut add = |name: &str| {
        let (i, b) = split(&read(name));
        imports.push_str(&format!(";; ---- {name} (imports)\n{i}\n"));
        body.push_str(&format!(";; ---- {name}\n{b}\n"));
    };
    add(match cfg.fetch {
        Fetch::Import => "fetch-import.wat",
        Fetch::Data => "fetch-data.wat",
    });
    add(match cfg.state {
        State::G => "state-g.wat",
        State::M => "state-m.wat",
    });
    add("core.wat");
    let mut stubs = String::new();
    for (g, handlers) in GROUPS {
        if cfg.groups.contains(g) {
            add(&format!("grp-{g}.wat"));
        } else {
            for h in *handlers {
                stubs.push_str(&format!(
                    "(func ${h} (param i32) (result i32) (i32.const 2)) ;; group `{g}` absent\n"
                ));
            }
        }
    }
    format!(
        ";; RV64 simulator: state {:?}, fetch {:?}, groups {:?}\n;; assembled by tools/wasm-sim (rv64) from examples/wasm-sim/rv64/parts\n(module\n{imports}{body};; ---- stubs\n{stubs}{extra})\n",
        cfg.state, cfg.fetch, cfg.groups
    )
}
