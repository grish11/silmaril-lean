module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.MLIR.CF.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.MLIR.CF.Example.Defs

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.MLIR.CF

open Diamond.MLIR.CF.Example (input width)
open SeaOfNodes.MLIR (Word)
open SeaOfNodes.MLIR.Lowering (encodeValues)
open SeaOfNodes.Loop.MLIR.CF (evalOp)
open Example (columns outerOverlap plan runCF runSource source trace)

example : (Nested.check source 0).isNone = true := rfl
example : (Shared.check outerOverlap 0).isNone = true := rfl
example : plan.blockOrder.map Fin.val = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] := rfl
example : plan.suffix.blocks.map Fin.val = [5, 6] := rfl
example : (plan.innerEdgeOccurrence true, plan.innerEdgeOccurrence false) = ((3, 0), (4, 0)) := rfl
example : columns = [(7, 15), (12, 25)] := rfl
example : trace = [(.innerTrue, 7, 15, 5), (.innerFalse, 32, 65, 5), (.outerFalse, 130, 130, 2)] := rfl

example : (runSource 19, runCF 20) = (some 130, some 130) := by
  unfold runCF
  rw [lower_run plan input 19]
  rfl

example : (runSource 18, runCF 19) = (none, none) := by
  unfold runCF
  rw [lower_run plan input 18]
  rfl

example : ∃ fuel, (lower plan).run evalOp fuel (encodeValues input) = some (.cons (130 : Word width) .nil) :=
  (returns_iff plan input 130).mpr ⟨19, (130 : Word width), rfl, rfl⟩

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.MLIR.CF
