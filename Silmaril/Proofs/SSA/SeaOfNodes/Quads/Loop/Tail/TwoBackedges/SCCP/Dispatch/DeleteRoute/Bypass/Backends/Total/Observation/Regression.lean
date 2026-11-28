module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Total.Observation.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Total.Observation.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Total.Observation.Example.Defs

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Total.Observation

open Bypass.MLIR.CF.Example (entry facts program width)
open Backends.Example (stoppingFacts)
open Total.Example (bothRoutes)
open Observation.Example (report)
open SeaOfNodes.Diamond.SCCP (TupleCovers)
open SeaOfNodes.MLIR (Word)

private def specialized := compile program (facts (.constant ⟨true⟩))
private def both := compile bothRoutes (facts .overdefined)
private def neither := compile program stoppingFacts

#guard (match specialized with | .specialized _ => true | _ => false)
#guard (match both with | .twoLive _ => true | _ => false)
#guard (match neither with | .neitherMarked _ => true | _ => false)
#guard report specialized (entry true true) 1 = ((5, 5, 1), (some 99, some 99, some 99))
#guard report both (entry true true) 2 = ((8, 9, 2), (some 198, some 198, some 198))
#guard report neither (entry true true) 1 = ((5, 6, 1), (some 99, some 99, some 99))

private theorem covered : TupleCovers (facts (.constant ⟨true⟩)) (entry true true) := by
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

private theorem specialized_correct : Correct specialized (entry true true) :=
  compile_correct rfl (specialized.compatible_of_covers covered)

example : specialized.numberedPart (entry true true) = Part.some (99 : Word width) :=
  specialized_correct.part_eq.2.trans (Part.eq_some_iff.mpr (mem_sourcePart_iff.mpr ⟨⟨5⟩, rfl⟩))

example : ∃ budget, both.runCF (entry true true) budget = some (198 : Word width) :=
  (((compile_correct rfl (by trivial) : Correct both (entry true true)).returns_iff _).1).mpr ⟨⟨8⟩, rfl⟩

-- The original artifacts do not depend on the entry fact that the header stops.
example : neither.Compatible stoppingFacts (entry true true) := trivial

example : neither.cfPart (entry true true) = Part.some (99 : Word width) :=
  (compile_correct rfl (by trivial) : Correct neither (entry true true)).part_eq.1.trans
    (Part.eq_some_iff.mpr (mem_sourcePart_iff.mpr ⟨⟨5⟩, rfl⟩))

-- The same true-route specialization cannot be used as a certified result on false input.
example : ¬ specialized.Compatible (facts (.constant ⟨true⟩)) (entry true false) := by
  intro compatible
  change TupleCovers (facts (.constant ⟨true⟩)) (entry true false) at compatible
  have wrong := compatible (.tail .head)
  change (⟨true⟩ : ULift Bool) = ⟨false⟩ at wrong
  cases wrong

#guard report specialized (entry true false) 1 = ((5, 5, 1), (some 7, some 99, some 99))

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Total.Observation
