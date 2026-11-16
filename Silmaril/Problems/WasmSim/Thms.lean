module

public import Silmaril.Problems.WasmSim.Defs
public import Silmaril.Proofs.Problems.WasmSim.Solve

/-!
# Problems: the reduction of ISA problems to Wasm problems, results

PROVED (`Silmaril/Proofs/Problems/WasmSim/Solve.lean`, standard axioms), registered with silmaril's
`@[solves]`: the four transfer principles (`specReductionStmt_sol`,
`fnCorrectDetReductionStmt_sol`, `cexTransferStmt_sol`, `agComposeStmt_sol`) and the toy's
per-instruction pieces (`dblPiece_sol`, `dblIsaOfPiece_sol`); `isaDbl_sol` solves the toy's ISA
statement `isaDbl` through them.
-/

/-- info: 'Silmaril.Problems.WasmSim.specReductionStmt_sol' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Silmaril.Problems.WasmSim.specReductionStmt_sol

