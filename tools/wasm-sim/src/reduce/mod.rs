//! The problem-level reduction (`docs/projects/wasm-sim-reduction.md`), ISA-independent parts.
//!
//! * `dag`: the problem-DAG schema `silmaril.wasm-sim.dag.v0` shared by the x86 and RV64 reductions
//!   and the solvers driver: nodes (problems, pieces, side conditions) and composition edges
//!   naming the Lean theorem that assembles them; a validator (`wasm-sim dag check`) and the
//!   derived status (which goals follow from solved pieces through proved edges).
//! * `plan`: the reduction-plan manifest `silmaril.wasm-sim.reduce.v0` (x86 fields; the RV64
//!   reduction reads the same file with its own extensions).
//! * `insn`: per-instruction granularity (certified step methods = `emit`).
//! * `elf`: a minimal ELF64 reader (functions and their bytes).

pub mod dag;
pub mod elf;
pub mod insn;
pub mod plan;
