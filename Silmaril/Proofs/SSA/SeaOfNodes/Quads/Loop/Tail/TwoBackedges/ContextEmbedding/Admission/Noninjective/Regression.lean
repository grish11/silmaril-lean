module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Admission.Noninjective.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Identification.Thms
meta import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Admission.Noninjective.Defs

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Admission.Noninjective

open SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.Example (width)
open SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution (Backend)
open Reindex.Guarded.Institution (AdmittedAt Generated)

#guard writeChecks == (true, true, true)
#guard outcomes == some ⟨.ok true, .error (.second (.checker .neitherMarked)), .error (.checker .neitherMarked)⟩
#guard runIntermediate 7 true == some (some 7, some 7)
#guard runIntermediate 8 true == some (some 0, some 0)
#guard runIntermediate 8 false == some (some 0, some 0)

example (backend : Backend) (source : AdmittedAt old width) (target : Generated middle width)
    (accepted : original = .ok source) (compiled : Identification.compile first source = .ok target) :
    backend.Returns target.artifacts (input 7 true) 7 ∧
      backend.Returns target.artifacts (input 8 true) 0 ∧
      backend.Returns target.artifacts (input 8 false) 0 := by
  have code := (Identification.admit_fields body oldFacts source accepted).1
  refine ⟨(Identification.compile_returns_iff first source compiled backend _ _).mpr ?_,
    (Identification.compile_returns_iff first source compiled backend _ _).mpr ?_,
    (Identification.compile_returns_iff first source compiled backend _ _).mpr ?_⟩
  · rw [code]
    exact ⟨2, rfl⟩
  · rw [code]
    exact ⟨5, rfl⟩
  · rw [code]
    exact ⟨5, rfl⟩

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Admission.Noninjective
