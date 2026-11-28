module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Reindex.Guarded.Institution.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Reindex.Guarded.Institution.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Reindex.Guarded.Institution.Example.Defs

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Reindex.Guarded.Institution

open CategoryTheory
open SeaOfNodes.MLIR (Word)
open SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.Example (entry width)
open SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution (Backend Sentence)
open Example (initialSignature middleSignature finalSignature first second original finalInput staged direct run)

#guard (run staged true, run direct true, run staged false, run direct false) ==
  ((some 99, some 99, some 99), (some 99, some 99, some 99),
    (some 7, some 7, some 7), (some 7, some 7, some 7))

example (side : Bool) : reduct (first ≫ second) (finalInput side) = entry true side := rfl

example : direct = staged := Generated.map_comp first second (Generated.lower original)

example (backend : Backend) :
    backend.Returns staged.artifacts (finalInput true) (99 : Word width) := by
  rw [← show direct = staged from Generated.map_comp first second (Generated.lower original)]
  exact (Generated.returns_map backend (first ≫ second) (Generated.lower original) _ _).mpr
    ((@Backend.returns_iff_source _ _ initialSignature.bankEq backend original _ _).mpr ⟨5, rfl⟩)

example : Backend.petri.Returns direct.artifacts (finalInput false) (7 : Word width) :=
  (Generated.returns_map .petri (first ≫ second) (Generated.lower original) _ _).mpr
    ((@Backend.returns_iff_source _ _ initialSignature.bankEq .petri original _ _).mpr ⟨5, rfl⟩)

example (backend : Backend) (side : Bool) :
    backend.observe direct.artifacts (finalInput side) =
      backend.observe (Generated.lower original).artifacts (reduct first (reduct second (finalInput side))) := by
  change backend.observe ((Generated.lower original).map (first ≫ second)).artifacts _ = _
  rw [Generated.observe_map, reduct_comp]

/-- Apply the staged and composite comparison to both sentence forms and
either runtime guard outcome. -/
example (backend : Backend) (side : Bool) (sentence : Sentence (AdmittedAt initialSignature width)) :
    (generatedRoom width backend finalSignature).Sat (Discrete.mk (finalInput side))
      ((nativeCorridor (first ≫ second) ≫ emitCorridor backend finalSignature).sen sentence) ↔
    (generatedRoom width backend finalSignature).Sat (Discrete.mk (finalInput side))
      ((emitCorridor backend initialSignature ≫ generatedCorridor backend first ≫ generatedCorridor backend second).sen sentence) := by
  rw [emit_comp]

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Reindex.Guarded.Institution
