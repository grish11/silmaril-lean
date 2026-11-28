module

import Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution.Lowering.Backends.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.Petri.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.Thms
meta import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.CF.Defs

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution.Lowering.Backends

open RVSDG (Origin Tuple)
open RVSDG.NestedTheta.Petri (Finishes)
open Silmaril.MLIR.CF.Ordered (Block)

private abbrev args : List ValueSort := [.address, .address, .word]

private def a {past : List (List ValueSort)} : Origin args past .address := .arg .head
private def b {past : List (List ValueSort)} : Origin args past .address := .arg (.tail .head)
private def stop {past : List (List ValueSort)} : Origin args past .word := .arg (.tail (.tail .head))

-- Read a, save it to b, and load that save. Clear a and load b again
-- for the tail test. The last store writes back the saved load.
private def interleaved : Graph args :=
  ⟨.load (.latest 0) a
    (.store (.latest 0) b (.output 0 .head)
      (.load (.latest 1) b
        (.store (.latest 1) a stop
          (.load (.latest 2) b
            (.store (.latest 2) b (.output 1 .head)
              (.ret (.latest 3) (.output 0 .head))))))),
    rfl, .tail (.tail .head)⟩

private def inputs (other : Address 2) : Tuple (Val 2) args :=
  .cons (0 : Address 2) (.cons other (.cons (0 : Word) .nil))

private def initial : Heap 2 := fun addr => if addr = 0 then 7 else 99

private def distinctAfter : Heap 2 := ((initial.write 1 7).write 0 0).write 1 7
private def aliasAfter : Heap 2 := ((initial.write 0 7).write 0 0).write 0 7

private theorem distinctCompletion :
    Finishes (thetaRuntime 2) interleaved.activation (Memory.encodeInput initial (inputs 1))
      (.cons ⟨1⟩ (Memory.encodeInput distinctAfter (inputs 1))) :=
  (interleaved.activation_finishes_iff (inputs 1) initial _).mpr (by cbv)

private theorem aliasCompletion :
    Finishes (thetaRuntime 2) interleaved.activation (Memory.encodeInput initial (inputs 0))
      (.cons ⟨0⟩ (Memory.encodeInput aliasAfter (inputs 0))) :=
  (interleaved.activation_finishes_iff (inputs 0) initial _).mpr (by cbv)

example : Block.eval (MLIR.MemRef.CF.evalBody (inputs 1))
    ((MLIR.MemRef.CF.lower 2 interleaved).block MLIR.MemRef.CF.Label.header) .nil ⟨initial⟩ =
      (.inl ⟨MLIR.MemRef.CF.Label.header, .nil⟩, ⟨distinctAfter⟩) :=
  (petri_activation_iff_memref_header interleaved (inputs 1) initial distinctAfter true).mp distinctCompletion

example : Block.eval (MLIR.MemRef.CF.evalBody (inputs 0))
    ((MLIR.MemRef.CF.lower 2 interleaved).block MLIR.MemRef.CF.Label.header) .nil ⟨initial⟩ =
      (.inl ⟨MLIR.MemRef.CF.Label.exit, .cons 0 .nil⟩, ⟨aliasAfter⟩) :=
  (petri_activation_iff_memref_header interleaved (inputs 0) initial aliasAfter false).mp aliasCompletion

private def headerResult (other : Address 2) : Option (Nat × Word × Word) :=
  let (out, final) := Block.eval (MLIR.MemRef.CF.evalBody (inputs other))
    ((MLIR.MemRef.CF.lower 2 interleaved).block MLIR.MemRef.CF.Label.header) .nil ⟨initial⟩
  match out with
  | .inl frame => some (frame.argsTy.length, final.cell 0, final.cell 1)
  | .inr _ => none

#guard headerResult 1 == some (0, 0, 7)
#guard headerResult 0 == some (1, 7, 99)

private def loopResult (other : Address 2) (budget : Nat) : Option (Word × Word × Word) :=
  (MLIR.MemRef.CF.run interleaved (inputs other) budget ⟨initial⟩).map fun (word, final) =>
    (word, final.cell 0, final.cell 1)

#guard (loopResult 1 0).isNone
#guard loopResult 1 1 == some (0, 0, 0)
#guard loopResult 0 0 == some (0, 7, 99)

private def distinctExit : Heap 2 := ((distinctAfter.write 1 0).write 0 0).write 1 0

example : Finishes (thetaRuntime 2) interleaved.lowerTheta (Memory.encodeInput initial (inputs 1))
    (Memory.encodeResult 0 distinctExit) :=
  (interleaved.lowerTheta_finishes_iff (inputs 1) initial 0 distinctExit).mp
    ⟨1, (interleaved.returnsAfter_iff_evalAfter (inputs 1) initial 1 0 distinctExit).mpr (by cbv)⟩

example : Finishes (thetaRuntime 2) interleaved.lowerTheta (Memory.encodeInput initial (inputs 0))
    (Memory.encodeResult 0 aliasAfter) :=
  (interleaved.lowerTheta_finishes_iff (inputs 0) initial 0 aliasAfter).mp
    ⟨0, (interleaved.returnsAfter_iff_evalAfter (inputs 0) initial 0 0 aliasAfter).mpr (by cbv)⟩

end Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution.Lowering.Backends
