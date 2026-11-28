module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.Example.Defs

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF

open Example (program looping entry facts observations reachingBank width)
open SeaOfNodes.Diamond.SCCP (TupleCovers)
open SeaOfNodes.MLIR (Word)
open SeaOfNodes.MLIR.Lowering (encodeValues)
open SeaOfNodes.Loop.MLIR.CF (model evalOp)

#guard (compile program (facts .overdefined)).isNone
#guard observations program true false 5 5 = some (some 7, some 7)
#guard observations program true true 5 5 = some (some 99, some 99)
#guard observations program true true 4 4 = some (none, none)
#guard reachingBank false = some (false, false, 7)
#guard reachingBank true = some (false, true, 99)
#guard observations program false true 2 2 = some (some 7, none)
#guard observations program false true 2 3 = some (some 7, some 7)
#guard observations looping true true 29 21 = some (none, none)

example : ReturnsAfter program model 1 (entry true true) (99 : Word width) :=
  .feedback rfl (.exit rfl)

private theorem coveredEntry : TupleCovers (facts (.constant ⟨true⟩)) (entry true true) := by
  intro s port
  cases port with
  | head => trivial
  | tail port =>
    cases port with
    | head => rfl
    | tail port =>
      cases port with
      | head => rfl
      | tail port => nomatch port

private theorem looping_no_trace {n : Nat} {value : SeaOfNodes.Diamond.sortValue model.value Example.word}
    (trace : ReturnsAfter looping model n (entry true true) value) : False := by
  induction n with
  | zero => cases trace with
    | exit taken => cases taken
  | succ n ih =>
    cases trace with
    | feedback taken rest =>
      change Sum.inr (true, entry true true) = _ at taken
      cases taken
      exact ih rest

private def checkedLoop : Checked model looping (facts (.constant ⟨true⟩)) :=
  (check model looping (facts (.constant ⟨true⟩))).get (by rfl)

example : (lower checkedLoop).Diverges evalOp (encodeValues (entry true true)) := by
  intro fuel
  cases obs : (lower checkedLoop).run evalOp fuel (encodeValues (entry true true)) with
  | none => rfl
  | some env =>
    cases env with
    | cons value tail =>
      cases tail
      obtain ⟨_, trace, _⟩ := (run_count_iff checkedLoop coveredEntry fuel value).mp obs
      exact (looping_no_trace trace).elim

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF
