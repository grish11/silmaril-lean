module

public import Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Defs

/-! The typed MLIR CF bank opcodes for the signed RTL word profile. -/

@[expose] public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.MLIR.CF

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.Pure (i1)

open Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF (TargetOp opcode)

abbrev i64 : Width := ⟨64, by decide⟩

/-- Flag-free `arith.subi` in the bank emitter. -/
abbrev subi : TargetOp [i64, i64] i64 :=
  opcode (.arithmetic (.binary .subi))

/-- Strict signed `arith.cmpi slt` in the bank emitter. -/
abbrev cmpiSlt : TargetOp [i64, i64] i1 :=
  opcode (.slt i64)

end Silmaril.Machine.SeaOfNodes.Loop.RTL.MLIR.CF
