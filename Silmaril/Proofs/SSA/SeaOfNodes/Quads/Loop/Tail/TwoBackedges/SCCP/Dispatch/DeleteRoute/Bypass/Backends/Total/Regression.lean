module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Total.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Total.Example.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Thms
meta import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Total.Example.Defs

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Total

open Bypass.MLIR.CF.Example (entry facts program looping width regs)
open Backends.Example (stoppingFacts)
open Backends.Total.Example (bothRoutes observations)
open SeaOfNodes.Loop.MLIR.CF (model evalOp)
open SeaOfNodes.MLIR (Word)
open SeaOfNodes.MLIR.Lowering (encodeValues)
open Blocks (Bank)

private def afterTrue : Bank (regs := regs) model :=
  .cons ⟨true⟩ (.cons ⟨false⟩ (.cons (99 : Word width) .nil))

private def afterFalse : Bank (regs := regs) model :=
  .cons ⟨false⟩ (.cons ⟨false⟩ (.cons (198 : Word width) .nil))

example : bothRoutes.step model (entry true true) = .inr (true, afterTrue) := rfl
example : bothRoutes.step model afterTrue = .inr (false, afterFalse) := rfl
example : bothRoutes.step model afterFalse = .inl (198 : Word width) := rfl

#guard observations bothRoutes (facts .overdefined) (entry true true) 1 =
  ("twoLive", none, none, none)
#guard observations bothRoutes (facts .overdefined) (entry true true) 2 =
  ("twoLive", some 198, some 198, some 198)
#guard observations bothRoutes (facts .overdefined) (entry true false) 1 =
  ("twoLive", some 14, some 14, some 14)
#guard observations bothRoutes (facts .overdefined) (entry false true) 0 =
  ("twoLive", some 7, some 7, some 7)
#guard observations looping (facts .overdefined) (entry true true) 8 =
  ("twoLive", none, none, none)
#guard observations program (facts (.constant ⟨true⟩)) (entry true true) 1 =
  ("specialized", some 99, some 99, some 99)
#guard observations program stoppingFacts (entry false true) 0 =
  ("neitherMarked", some 7, some 7, some 7)
#guard (Backends.compile bothRoutes (facts .overdefined)).map Targets.retained = .error .bothMarked
#guard (Backends.Worklist.compile program stoppingFacts).map Targets.retained = .error .neitherMarked

private theorem looping_header_none (fuel : Nat) :
    looping.source.runFrom model fuel 1 (entry true true) = none := by
  induction fuel using Nat.strong_induction_on with
  | ind fuel ih =>
    cases fuel with
    | zero => rfl
    | succ fuel =>
      rw [looping.source_header]
      exact ih (fuel - 2) (by omega)

example :
    (emitOriginal looping).cf.Diverges evalOp (encodeValues (entry true true)) ∧
      ∀ fuel, (emitOriginal looping).numbered.run (Join.model model) fuel (entry true true) = none := by
  have success : compile looping (facts .overdefined) = .twoLive (emitOriginal looping) := rfl
  have absent : ¬ ∃ value fuel, looping.source.runFrom model fuel 0 (entry true true) = some value := by
    rintro ⟨value, fuel, returned⟩
    cases fuel with
    | zero => cases returned
    | succ fuel =>
      have reached : looping.source.runFrom model fuel 1 (entry true true) = some value := returned
      rw [looping_header_none] at reached
      cases reached
  have laws := twoLive_noReturn_iff (entry true true) success
  exact ⟨laws.1.mpr absent, laws.2.mpr absent⟩

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Total
