module

public import Silmaril.Wasm.SSA.MLIRMath.Defs

public section

namespace Silmaril.Proofs.Wasm.SSA.MLIRMath

open Silmaril.Wasm.SSA.MLIRMath Silmaril.MLIR
open Silmaril.Numeric.Ieee754 Silmaril.Numeric.Libm

theorem log_exact_iff (bits : Math.Binary64) (result : ℝ) :
    Double.log.exact (toF64 bits) = some result ↔
      ∃ x, decodeFinite bits = some x ∧ (Math.denote .log).reference.Holds x result := by
  classical
  change B64.onFinite (0 < ·) Real.log (toF64 bits) = some result ↔ _
  cases h : (toF64 bits).toRat? with
  | none => simp [B64.onFinite, decodeFinite, h]
  | some q =>
    by_cases pos : (0 : ℝ) < (q : ℝ) <;>
      simp [B64.onFinite, decodeFinite, h, pos, Math.denote, MathCollection.Reference.Holds]

theorem log_in_catalogue : Double.log.entry ∈ Double.catalogue := by
  have h : Double.log ∈ Double.batch2Unary := by simp [Double.batch2Unary]
  exact List.mem_append_right _ (List.mem_append_left _ (List.mem_map_of_mem h))

theorem log_node_of_cr {impl : F64 → Outcome F64} (hcr : Double.log.CorrectlyRounded impl) :
    LogNode impl := by
  intro bits h
  obtain ⟨x, decoded, positive⟩ := h
  have ideal : (Math.denote .log).reference.Holds x (Real.log x) := ⟨positive, rfl⟩
  have spec := (log_exact_iff bits (Real.log x)).2 ⟨x, decoded, ideal⟩
  refine ⟨⟨_, rfl⟩, ?_⟩
  rintro output rfl
  exact ⟨x, Real.log x, decoded, ideal, hcr _ _ spec⟩

theorem log_node_of_catalogue {impl : LibmImpl}
    (h : Double.ValidLibmDouble .correctlyRounded impl) : LogNode (impl Double.log.entry) := by
  have valid := h Double.log.entry log_in_catalogue
  change Double.log.Valid (impl Double.log.entry) .correctlyRounded at valid
  exact log_node_of_cr valid.2

theorem log_one_exact : Double.log.exact (toF64 0x3ff0000000000000) = some 0 := by
  have decoded : (toF64 0x3ff0000000000000).toRat? = some (1 : ℚ) := by decide +kernel
  refine (log_exact_iff _ _).2 ⟨1, ?_, ⟨zero_lt_one, Real.log_one⟩⟩
  rw [decodeFinite, decoded]
  change some ((1 : ℚ) : ℝ) = some 1
  rw [Rat.cast_one]

end Silmaril.Proofs.Wasm.SSA.MLIRMath
