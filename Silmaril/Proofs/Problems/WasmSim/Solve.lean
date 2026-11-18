module

public import Silmaril.Problems.WasmSim.Defs
public import Silmaril.Sim.Reduce.Thms
public import Silmaril.Sim.Reduce.Toy.Dbl.Thms
public import Silmaril.Sim.Reduce.Toy.SumTo.Thms
public import Silmaril.Sim.Reduce.Toy.F.Thms

/-!
# Problems: the reduction of ISA problems to Wasm problems, solutions

The header is `Silmaril/Problems/WasmSim/Thms.lean`.
-/

@[expose] public section

namespace Silmaril.Problems.WasmSim

open Silmaril.Sim.Reduce

@[solves "wasm-sim/reduce/spec-reduction"]
theorem specReductionStmt_sol : specReductionStmt :=
  fun _ _ I S K Init hstep henc h => (specReduction I S K hstep Init henc).sound h

@[solves "wasm-sim/reduce/fncorrectdet-reduction"]
theorem fnCorrectDetReductionStmt_sol : fnCorrectDetReductionStmt :=
  fun _ _ I S K Init hstep henc h e => (specReduction I (S e) K hstep Init (henc e)).sound (h e)

@[solves "wasm-sim/reduce/cex-transfer"]
theorem cexTransferStmt_sol : cexTransferStmt :=
  fun _ _ K _ _ _ _ hc h => isaCex_of_wasmCex K hc h

@[solves "wasm-sim/reduce/ag-compose"]
theorem agComposeStmt_sol : agComposeStmt := fun _ _ _ _ hr h => ag_compose hr h

@[solves "wasm-sim/toy/insn/dbl-piece"]
theorem dblPiece_sol : dblPiece := Silmaril.Sim.Reduce.Toy.Dbl.piece

@[solves "wasm-sim/toy/insn/dbl-isa-of-piece"]
theorem dblIsaOfPiece_sol : dblIsaOfPiece := fun h =>
  Silmaril.Sim.Reduce.Toy.Dbl.isa_of_x86 (Silmaril.Sim.Reduce.Toy.Dbl.x86_of_piece h)

/-- The toy's ISA statement for `dbl`, solved. -/
theorem isaDbl_sol : isaDbl := fun base => Silmaril.Sim.Reduce.Toy.Dbl.isa_dbl base

/-- The toy's ISA statement for `sum_to`, solved (dispatcher route). -/
theorem isaSumTo_sol : isaSumTo := fun base => Silmaril.Sim.Reduce.Toy.SumTo.isa_sumTo base

/-- The toy's ISA statement for `f`, solved by per-function decomposition. -/
theorem isaF_sol : isaF := fun base => Silmaril.Sim.Reduce.Toy.F.isa_f base

end Silmaril.Problems.WasmSim
