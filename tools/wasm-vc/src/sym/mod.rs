//! Symbolic execution of core Wasm modules to SMT, and the problems solved
//! with it: equivalence, reference relations, bounded call/trap properties.

pub mod annot;
pub mod drive;
pub mod exec;
pub mod infer;
pub mod leangen;
pub mod module;
pub mod problem;
pub mod solve;
pub mod term;
