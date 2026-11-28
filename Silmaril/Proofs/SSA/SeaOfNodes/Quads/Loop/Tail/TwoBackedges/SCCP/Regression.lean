module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Example.Defs

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP

open SCCP.Example (Byte program model facts concrete report feedbackBytes firstFeedback nativeReturn)

#guard feedbackBytes = (.constant 99, .constant 7)
#guard report (.constant ⟨false⟩) = (true, false, true, true, .constant 7, .constant 7)
#guard report .overdefined = (true, true, true, true, .overdefined, .overdefined)
#guard firstFeedback false = some (false, 7)
#guard firstFeedback true = some (true, 99)
#guard nativeReturn false 4 = none
#guard nativeReturn false 5 = some 7
#guard nativeReturn true 5 = some 99

example :
    program.Arrives model (concrete false) (.feedback false) 1
      ((program.feedback false).eval model (concrete false)) := .feedback .entry rfl

private theorem inputCovered : Diamond.SCCP.TupleCovers (facts (.constant ⟨false⟩)) (concrete false) := by
  intro _ port
  cases port with
  | head => rfl
  | tail port =>
    cases port with
    | head => rfl
    | tail port =>
      cases port with
      | head => rfl
      | tail port => cases port

example {fuel : Nat} {value : Byte} (returned : program.source.runFrom model fuel 0 (concrete false) = some value) :
    value = 7 := by
  have sound := (solve_source_return model program inputCovered returned).2
  change (7 : Byte) = value at sound
  exact sound.symm

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP
