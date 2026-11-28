module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Numbered.Comparison.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Numbered.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Numbered.Example.Defs

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Numbered

open Bypass.MLIR.CF.Example (entry facts program looping word)
open Example (headerWrite observations packet)
open SeaOfNodes.Diamond (sortValue)
open SeaOfNodes.Diamond.SCCP (TupleCovers)
open SeaOfNodes.Loop.MLIR.CF (model)

#guard (compile model program (facts .overdefined)).isNone
#guard observations program true false 1 = some (some 7, some 7, some 7)
#guard observations program true true 1 = some (some 99, some 99, some 99)
#guard observations program true true 0 = some (none, none, none)
#guard packet false = some (0, false, false, 7)
#guard packet true = some (0, false, true, 99)
#guard observations headerWrite false true 0 = some (some 42, some 42, some 42)
#guard observations looping true true 9 = some (none, none, none)

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

private theorem looping_no_trace {n : Nat} {value : sortValue model.value word}
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

example (fuel : Nat) : (lower checkedLoop).run (Join.model model) fuel (entry true true) = none := by
  cases observed : (lower checkedLoop).run (Join.model model) fuel (entry true true) with
  | none => rfl
  | some values =>
    cases values with
    | cons value tail =>
      cases tail
      obtain ⟨_, trace, _⟩ := (run_count_iff checkedLoop coveredEntry fuel value).mp observed
      exact (looping_no_trace trace).elim

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Numbered
