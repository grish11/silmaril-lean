module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.Example.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Thms
meta import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution.Defs
meta import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.Example.Defs

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution

open CategoryTheory (Discrete)
open Bypass.MLIR.CF.Example (entry facts looping program regs width)
open SeaOfNodes.Loop.MLIR.CF (model evalOp)
open SeaOfNodes.MLIR (Word)
open SeaOfNodes.MLIR.Lowering (encodeValues)

private def assumptions := facts (.constant ⟨true⟩)
private def guarded : Admitted regs width := (admit program assumptions).toOption.get (by rfl)
private def otherRoute : Admitted regs width :=
  (admit program (facts (.constant ⟨false⟩))).toOption.get (by rfl)
private def noExit : Admitted regs width := (admit looping assumptions).toOption.get (by rfl)

private def report (artifacts : Artifacts regs width) (input : Entry regs) (cfFuel thetaFuel : Nat) :
    Option Nat × Option Nat :=
  ((artifacts.cf.run evalOp cfFuel (encodeValues input)).map
      (fun env => (env.get .here).toNat),
    (artifacts.numbered.2.run (Join.model model) thetaFuel input).map
      (fun packet => (packet.get .head : Word width).toNat))

#guard
  let artifacts := guarded.emit
  (report artifacts (entry true true) 6 1, report artifacts (entry true false) 7 1) =
    ((some 99, some 99), (some 7, some 7))

-- The checked graphs agree on exhaustion at these bounds.
#guard report guarded.emit (entry true true) 1 0 = (none, none)
#guard report noExit.emit (entry true true) 1 0 = (none, none)

example (backend : Backend) : backend.observe guarded.emit (entry true true) = Part.some (99 : Word width) :=
  Part.eq_some_iff.mpr ((backend.mem_observe_iff _ _ _).mpr
    ((backend.returns_iff_source guarded _ _).mpr ⟨5, rfl⟩))

example (backend : Backend) : backend.Returns guarded.emit (entry true false) (7 : Word width) :=
  (backend.returns_iff_source guarded _ _).mpr ⟨5, rfl⟩

private theorem noExit_at_header (fuel : Nat) :
    looping.source.runFrom model fuel 1 (entry true true) = none := by
  induction fuel using Nat.strong_induction_on with
  | ind fuel ih =>
    cases fuel with
    | zero => rfl
    | succ n =>
      rw [Program.source_header]
      have step : looping.step model (entry true true) = .inr (true, entry true true) := rfl
      rw [step]
      exact ih (n - 2) (by omega)

private theorem noExit_none : noExit.observe (entry true true) = Part.none := by
  apply Part.eq_none_iff'.mpr
  intro defined
  obtain ⟨value, returned⟩ := Part.dom_iff_mem.mp defined
  obtain ⟨fuel, ran⟩ := (noExit.mem_observe_iff (entry true true) value).mp returned
  change looping.source.runFrom model fuel 0 (entry true true) = some value at ran
  cases fuel with
  | zero => cases ran
  | succ n =>
    rw [Program.source_entry] at ran
    change looping.source.runFrom model n 1 (entry true true) = some value at ran
    rw [noExit_at_header] at ran
    cases ran

example (backend : Backend) :
    (targetRoom regs width backend).Sat (Discrete.mk (entry true true))
      ((comparison backend).sen (.equation guarded otherRoute)) :=
  ((comparison backend).sat _ _).mpr rfl

example (backend : Backend) :
    (targetRoom regs width backend).Sat (Discrete.mk (entry true false))
      ((comparison backend).sen (.terminates guarded)) :=
  ((comparison backend).sat _ _).mpr (Part.dom_iff_mem.mpr
    ⟨(7 : Word width), (guarded.mem_observe_iff _ _).mpr ⟨5, rfl⟩⟩)

example (backend : Backend) :
    ¬ (targetRoom regs width backend).Sat (Discrete.mk (entry true true))
      ((comparison backend).sen (.equation guarded noExit)) := by
  intro satisfied
  have native := ((comparison backend).sat _ _).mp satisfied
  have returned := (guarded.mem_observe_iff (entry true true) (99 : Word width)).mpr ⟨5, rfl⟩
  change guarded.observe (entry true true) = noExit.observe (entry true true) at native
  rw [native, noExit_none] at returned
  exact Part.notMem_none _ returned

example (backend : Backend) :
    ¬ (targetRoom regs width backend).Sat (Discrete.mk (entry true true))
      ((comparison backend).sen (.terminates noExit)) := by
  intro satisfied
  have defined := ((comparison backend).sat _ _).mp satisfied
  exact (Part.eq_none_iff'.mp noExit_none) defined

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution
