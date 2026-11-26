module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Weakening.Guarded.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Weakening.Guarded.Example.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Thms
meta import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Weakening.Guarded.Example.Defs

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Weakening.Guarded

open CategoryTheory
open SeaOfNodes.Loop.MLIR.CF (model)
open SeaOfNodes.MLIR (Word)
open SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.Example (bankEq entry looping regs width)
open SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution (Admitted Backend Sentence admit)
open Reindex.Guarded.Institution (AdmittedAt Generated generatedRoom)
open Reindex.Guarded.Institution.Example (initialSignature original)
open Example (capture captureWidth checkedSide input run widened)

#guard checkedSide == some true
#guard (run 0 true, run 65535 true) == (some (some 99, some 99, some 99), some (some 99, some 99, some 99))
#guard (run 0 false, run 65535 false) == (some (some 7, some 7, some 7), some (some 7, some 7, some 7))

example (value : Word captureWidth) (side : Bool) : project (input value side) = entry true side := rfl

example : compile capture original = .ok (Generated.lower (lift capture original)) :=
  compile_eq capture original

example (backend : Backend) (value : Word captureWidth) :
    backend.Returns (liftGenerated capture (Generated.lower original)).artifacts
      (input value false) (7 : Word width) :=
  (compile_returns_iff capture backend original (compile_eq capture original) _ _).mpr ⟨5, rfl⟩

private def nonreturning : AdmittedAt initialSignature width :=
  (@admit regs width bankEq looping
    (SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.Example.facts (.constant ⟨true⟩))).toOption.get (by rfl)

private theorem header_never_returns (fuel : Nat) :
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

example (backend : Backend) (value : Word captureWidth) :
    ¬ ∃ word, backend.Returns (liftGenerated capture (Generated.lower nonreturning)).artifacts
      (input value true) word := by
  apply (backend_noReturn capture backend (Generated.lower nonreturning) _).mpr
  rintro ⟨word, returned⟩
  obtain ⟨fuel, h⟩ := (@Backend.returns_iff_source _ _ initialSignature.bankEq backend nonreturning _ _).mp returned
  change looping.source.runFrom model fuel 0 (entry true true) = some word at h
  cases fuel with
  | zero => cases h
  | succ n =>
    rw [Program.source_entry] at h
    change looping.source.runFrom model n 1 (entry true true) = some word at h
    rw [header_never_returns] at h
    cases h

example (backend : Backend) (value : Word captureWidth) (side : Bool)
    (sentence : Sentence (Generated initialSignature width)) :
    (generatedRoom width backend widened).Sat (Discrete.mk (input value side))
      ((generatedCorridor capture backend).sen sentence) ↔
      (generatedRoom width backend initialSignature).Sat (Discrete.mk (entry true side)) sentence :=
  (generatedCorridor capture backend).sat _ _

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Weakening.Guarded
