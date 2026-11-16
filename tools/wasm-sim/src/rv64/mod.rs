//! RV64 simulators: assembler of the WAT parts in
//! `examples/wasm-sim/rv64/parts`, wasmtime harness, P-calls / P-data
//! translators, reduction of RV64 functions to Wasm problems, difftests
//! (qemu-riscv64, G/M lockstep, lattice, executable Lean model), benchmarks.
//! CLI: `src/bin/wasm-sim-rv.rs`.

pub mod asm;
pub mod bench;
pub mod check;
pub mod consistency;
pub mod decode;
pub mod elf;
pub mod host;
pub mod lean;
pub mod randprog;
pub mod reduce;
pub mod translate;
