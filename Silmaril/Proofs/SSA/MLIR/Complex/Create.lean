module

public import Silmaril.SSA.MLIR.Complex.Defs

public section

namespace Silmaril.Proofs.MLIR.Complex

open Silmaril.MLIR.Complex Silmaril.MLIR.MathCollection

theorem create_realizes (decode : MLIR.Math.Binary64 → Option ℝ) :
    (denote .create).RealizesOn (createObservation decode)
      (fun bits => ∃ parts, decodeParts decode bits = some parts) (denote .create).Executes := by
  intro bits h
  obtain ⟨parts, decoded⟩ := h
  refine ⟨⟨bits, rfl⟩, ?_⟩
  intro output returned
  change some bits = some output at returned
  cases returned
  refine ⟨parts, ⟨parts.1, parts.2⟩, decoded, ⟨trivial, rfl⟩, ?_⟩
  change (decodeParts decode bits).map _ = some _
  rw [decoded]
  rfl

end Silmaril.Proofs.MLIR.Complex
