module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.Example.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Thms
meta import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.Example.Defs

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch

open SCCP.Example (model facts concrete program nativeReturn)
open Dispatch.Example (jumpTarget rewrittenReturn looping loopingReturn)

#guard jumpTarget (.constant ⟨false⟩) = some 4
#guard jumpTarget (.constant ⟨true⟩) = some 3
#guard jumpTarget .overdefined = none
#guard rewrittenReturn false 4 = some none
#guard rewrittenReturn false 5 = some (nativeReturn false 5)
#guard rewrittenReturn true 5 = some (nativeReturn true 5)
#guard loopingReturn 12 = some none

private theorem covered (side : Bool) :
    Diamond.SCCP.TupleCovers (facts (.constant ⟨side⟩)) (concrete side) := by
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

example (side : Bool) (checked : Checked model program (facts (.constant ⟨side⟩))) (fuel : Nat) :
    checked.source.runFrom model fuel 0 (concrete side) = program.source.runFrom model fuel 0 (concrete side) :=
  checked.runFrom_eq (covered side) fuel

private theorem looping_header (fuel : Nat) :
    looping.source.runFrom model fuel 1 (concrete false) = none := by
  induction fuel using Nat.strong_induction_on with
  | ind fuel smaller =>
    cases fuel with
    | zero => rfl
    | succ fuel =>
      rw [looping.source_header]
      exact smaller (fuel - 2) (by omega)

example (checked : Checked model looping (facts (.constant ⟨false⟩))) (fuel : Nat) :
    checked.source.runFrom model fuel 0 (concrete false) = none := by
  rw [checked.runFrom_eq (covered false)]
  cases fuel with
  | zero => rfl
  | succ fuel =>
    rw [looping.source_entry]
    exact looping_header fuel

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch
