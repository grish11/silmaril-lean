//! Program-as-calls (P-calls) translator and P-data segment generator.
//!
//! P-calls: the executable section of a static RV64 ELF is decoded in Rust
//! (`decode.rs`, mirror of the WAT decoder) and becomes one Wasm function
//! `prog_run(fuel) -> status` importing the simulator's `get` and the `i_*`
//! methods it needs (so its import list is its *signature*: it links against
//! any simulator in the lattice that exports those methods). Control flow is a
//! `loop` + `br_table` dispatcher over basic blocks. Each method performs the
//! full instruction semantics including the pc update, so the simulator state
//! after each block is exactly the state `step` would produce; the dispatcher
//! only chooses which block to run next (statically for direct branches/JAL,
//! via the exported pc->block table `prog_blk` for JALR).
//!
//! Leaders: entry, ELF symbols in the text, branch/JAL targets, instructions
//! after a branch/JAL/JALR/EBREAK, and addresses materialised by `auipc rd,hi;
//! addi rd,rd,lo` pairs (`la`). A JALR to a non-leader returns status 2 with
//! pc set; the embedder may continue with `step` (mixed mode, see main.rs).

use super::decode::{Inst, Kind, decode};
use super::elf::Elf;
use std::collections::BTreeSet;
use std::fmt::Write;

pub struct Text {
    pub base: u64,
    pub words: Vec<u32>,
}

pub fn text(elf: &Elf) -> Text {
    // the (single) executable PT_LOAD segment, truncated to whole words
    let s = elf
        .segments
        .iter()
        .find(|s| s.exec)
        .expect("no executable segment");
    let words = s
        .data
        .as_chunks::<4>()
        .0
        .iter()
        .map(|c| u32::from_le_bytes(*c))
        .collect();
    Text {
        base: s.vaddr,
        words,
    }
}

fn sig(k: Kind) -> &'static str {
    match k {
        Kind::R => "(param i32 i32 i32)",
        Kind::I => "(param i32 i32 i64)",
        Kind::U => "(param i32 i64)",
        Kind::L | Kind::S | Kind::B => "(param i32 i32 i64) (result i32)",
        Kind::J => "(param i32 i64) (result i32)",
        Kind::Jr => "(param i32 i32 i64) (result i32)",
        Kind::Z => "(result i32)",
    }
}

pub fn leaders(elf: &Elf, t: &Text) -> BTreeSet<usize> {
    let n = t.words.len();
    let end = t.base + 4 * n as u64;
    let idx = |a: u64| {
        if a >= t.base && a < end && (a - t.base).is_multiple_of(4) {
            Some(((a - t.base) / 4) as usize)
        } else {
            None
        }
    };
    let mut l = BTreeSet::new();
    l.extend(idx(elf.entry));
    for (_, a) in &elf.symbols {
        l.extend(idx(*a));
    }
    for (i, &w) in t.words.iter().enumerate() {
        let pc = t.base + 4 * i as u64;
        let Some(d) = decode(w) else { continue };
        match d.kind {
            Kind::B | Kind::J => {
                l.extend(idx(pc.wrapping_add(d.imm as u64)));
                l.insert(i + 1);
            }
            Kind::Jr | Kind::Z if d.m != "ecall" => {
                l.insert(i + 1);
            }
            Kind::U if d.m == "auipc" => {
                if let Some(Some(e)) = t.words.get(i + 1).map(|&w2| decode(w2))
                    && e.m == "addi"
                    && e.rs1 == d.rd
                    && e.rd == d.rd
                {
                    l.extend(idx(pc
                        .wrapping_add(d.imm as u64)
                        .wrapping_add(e.imm as u64)));
                }
            }
            _ => {}
        }
    }
    l.retain(|&i| i < n);
    l.insert(0);
    l
}

/// The P-calls program module (WAT).
pub fn pcalls(elf: &Elf) -> String {
    let t = text(elf);
    let n = t.words.len();
    let lead = leaders(elf, &t);
    let starts: Vec<usize> = lead.iter().copied().collect();
    let blk_of = |i: usize| starts.binary_search(&i).ok();
    let dec: Vec<Option<Inst>> = t.words.iter().map(|&w| decode(w)).collect();
    let mut used: BTreeSet<(&str, Kind)> = BTreeSet::new();
    for d in dec.iter().flatten() {
        used.insert((d.m, d.kind));
    }
    let mut o = String::new();
    writeln!(
        o,
        ";; P-calls translation: text {:#x}+{:#x}, {} words, {} blocks",
        t.base,
        4 * n,
        n,
        starts.len()
    )
    .unwrap();
    writeln!(o, "(module").unwrap();
    writeln!(
        o,
        "  (import \"sim\" \"get\" (func $get (param i32) (result i64)))"
    )
    .unwrap();
    for (m, k) in &used {
        writeln!(o, "  (import \"sim\" \"i_{m}\" (func $i_{m} {}))", sig(*k)).unwrap();
    }
    // pc -> block table, one i32 per text word
    writeln!(o, "  (memory {})", (4 * n).div_ceil(65536).max(1)).unwrap();
    let mut tbl = String::new();
    for i in 0..n {
        let v: i32 = blk_of(i).map(|b| b as i32).unwrap_or(-1);
        for byte in v.to_le_bytes() {
            write!(tbl, "\\{byte:02x}").unwrap();
        }
    }
    writeln!(o, "  (data (i32.const 0) \"{tbl}\")").unwrap();
    writeln!(
        o,
        "  (global $fuel (export \"prog_fuel_left\") (mut i64) (i64.const 0))"
    )
    .unwrap();
    writeln!(o, "  (func $blk (export \"prog_blk\") (param $pc i64) (result i32) (local $o i64)
    (local.set $o (i64.sub (local.get $pc) (i64.const {})))
    (if (i32.or (i64.ge_u (local.get $o) (i64.const {})) (i32.wrap_i64 (i64.and (local.get $o) (i64.const 3))))
      (then (return (i32.const -1))))
    (i32.load (i32.wrap_i64 (local.get $o))))", t.base, 4 * n).unwrap();
    writeln!(
        o,
        "  (func (export \"prog_run\") (param $f i64) (result i32) (local $b i32) (local $t i32)"
    )
    .unwrap();
    writeln!(o, "    (global.set $fuel (local.get $f))").unwrap();
    writeln!(
        o,
        "    (local.set $b (call $blk (call $get (i32.const 32))))"
    )
    .unwrap();
    writeln!(o, "    (loop $L").unwrap();
    write!(o, "    (block $exit ").unwrap();
    for b in (0..starts.len()).rev() {
        write!(o, "(block $B{b} ").unwrap();
    }
    write!(o, "\n      (br_table").unwrap();
    for b in 0..starts.len() {
        write!(o, " $B{b}").unwrap();
    }
    writeln!(o, " $exit (local.get $b)))").unwrap();
    for (b, &s) in starts.iter().enumerate() {
        let e = starts.get(b + 1).copied().unwrap_or(n);
        let len = (e - s) as u64;
        writeln!(
            o,
            "      ;; block {b} @ {:#x}, {len} instrs",
            t.base + 4 * s as u64
        )
        .unwrap();
        writeln!(o, "      (if (i64.lt_u (global.get $fuel) (i64.const {len})) (then (return (i32.const 4))))").unwrap();
        writeln!(
            o,
            "      (global.set $fuel (i64.sub (global.get $fuel) (i64.const {len})))"
        )
        .unwrap();
        for (i, di) in dec.iter().enumerate().take(e).skip(s) {
            let pc = t.base + 4 * i as u64;
            // refund the instructions of this block that did not retire
            let refund =
                |k: u64| format!("(global.set $fuel (i64.add (global.get $fuel) (i64.const {k})))");
            let early = format!(
                "(if (local.get $t) (then {} (return (local.get $t))))",
                refund(e as u64 - i as u64)
            );
            let Some(d) = *di else {
                writeln!(
                    o,
                    "      {} (return (i32.const 2))",
                    refund(e as u64 - i as u64)
                )
                .unwrap();
                break;
            };
            let (rd, rs1, rs2, imm, m) = (d.rd, d.rs1, d.rs2, d.imm, d.m);
            let target = |off: i64| {
                let a = pc.wrapping_add(off as u64);
                if a >= t.base && (a - t.base).is_multiple_of(4) {
                    blk_of(((a - t.base) / 4) as usize)
                } else {
                    None
                }
            };
            let goto = |tb: Option<usize>| match tb {
                Some(tb) => format!("(local.set $b (i32.const {tb})) (br $L)"),
                None => "(local.set $b (call $blk (call $get (i32.const 32)))) (br $L)".to_string(),
            };
            let line = match d.kind {
                Kind::R => {
                    format!("(call $i_{m} (i32.const {rd}) (i32.const {rs1}) (i32.const {rs2}))")
                }
                Kind::I => {
                    format!("(call $i_{m} (i32.const {rd}) (i32.const {rs1}) (i64.const {imm}))")
                }
                Kind::U => format!("(call $i_{m} (i32.const {rd}) (i64.const {imm}))"),
                Kind::L => format!(
                    "(local.set $t (call $i_{m} (i32.const {rd}) (i32.const {rs1}) (i64.const {imm}))) {early}"
                ),
                Kind::S => format!(
                    "(local.set $t (call $i_{m} (i32.const {rs1}) (i32.const {rs2}) (i64.const {imm}))) {early}"
                ),
                Kind::B => format!(
                    "(local.set $t (call $i_{m} (i32.const {rs1}) (i32.const {rs2}) (i64.const {imm})))\n      (if (i32.eq (local.get $t) (i32.const 1)) (then {}))\n      {early}",
                    goto(target(imm))
                ),
                Kind::J => format!(
                    "(local.set $t (call $i_{m} (i32.const {rd}) (i64.const {imm}))) {early} {}",
                    goto(target(imm))
                ),
                Kind::Jr => format!(
                    "(local.set $t (call $i_{m} (i32.const {rd}) (i32.const {rs1}) (i64.const {imm}))) {early} {}",
                    goto(None)
                ),
                Kind::Z => format!("(local.set $t (call $i_{m})) {early}"),
            };
            writeln!(o, "      {line}").unwrap();
        }
        // fall through into the next block (its code follows the end of `$B{b+1}`)
        writeln!(o, "    )").unwrap();
    }
    writeln!(
        o,
        "    ;; pc is not a block leader: sentinel -> halted, otherwise unsupported"
    )
    .unwrap();
    writeln!(o, "    (return (select (i32.const 1) (i32.const 2) (i64.eq (call $get (i32.const 32)) (i64.const {})))))", super::host::SENTINEL as i64).unwrap();
    writeln!(o, "    (unreachable)))").unwrap();
    o
}

/// P-data: globals and data segment for `parts/fetch-data.wat`.
pub fn pdata(elf: &Elf) -> String {
    let t = text(elf);
    let mut s = String::new();
    for w in &t.words {
        for b in w.to_le_bytes() {
            write!(s, "\\{b:02x}").unwrap();
        }
    }
    format!(
        ";; ---- P-data code segment\n(global $code_base i64 (i64.const {}))\n(global $code_len i64 (i64.const {}))\n(data (memory $code) (i32.const 0) \"{s}\")\n",
        t.base as i64,
        4 * t.words.len()
    )
}
