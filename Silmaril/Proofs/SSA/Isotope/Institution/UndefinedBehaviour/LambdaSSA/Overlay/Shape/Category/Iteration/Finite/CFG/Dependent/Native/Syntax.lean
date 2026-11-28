module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Native.Defs

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native

open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native

universe u

variable {Φ : Type u} [DecidableEq Φ]

theorem sameRegion_eq {r t : Isotope.LambdaSSA.Region Φ} (same : sameRegion r t = true) : r = t := by
  induction r generalizing t with
  | br i a =>
    cases t <;> simp [sameRegion] at same
    case br j b =>
      obtain ⟨rfl, rfl⟩ := same
      rfl
  | case a left right hl hr =>
    cases t <;> simp [sameRegion] at same
    case case b l r =>
      obtain ⟨⟨rfl, lEq⟩, rEq⟩ := same
      rw [hl lEq, hr rEq]
  | let₁ a body ih =>
    cases t <;> simp [sameRegion] at same
    case let₁ b body' =>
      obtain ⟨rfl, bodyEq⟩ := same
      rw [ih bodyEq]
  | let₂ => cases t <;> simp [sameRegion] at same
  | cfg entry n blocks he hb =>
    cases t <;> try (solve | simp [sameRegion] at same)
    case cfg e m bs =>
      by_cases arity : n = m
      · subst m
        simp [sameRegion] at same
        obtain ⟨entryEq, blockEq⟩ := same
        rw [he entryEq, show blocks = bs from funext (fun i => hb i (blockEq i))]
      · simp [sameRegion, arity] at same

variable [HasTy Φ (Silmaril.Ty Empty)] {X : Silmaril.Ty Empty}
variable {R L : List (Silmaril.Ty Empty)}

theorem recognized_eq {raw : Typed Φ [X] L} {w : Readback Φ X R L}
    (accepted : recognize R raw = some w) : raw = w.typed := by
  obtain ⟨candidate, _, checked⟩ := Option.bind_eq_some_iff.mp accepted
  split at checked
  · rename_i same
    obtain rfl := Option.some.inj checked
    exact Subtype.ext (sameRegion_eq same)
  · cases checked

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native
