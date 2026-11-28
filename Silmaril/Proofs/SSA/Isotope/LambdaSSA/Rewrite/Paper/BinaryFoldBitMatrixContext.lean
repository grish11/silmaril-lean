module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.StructuralValues.ThreeCycle.MatrixBoundary.Binary.Context.Defs

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BinaryFoldBitMatrixContext

open Silmaril.Calco2019.CounterSemiring.ThreeCycle
open Binary

theorem eliminate_contextual {C I X E : Type} [DecidableEq C]
    (f : C → (I ⊕ X) → (E ⊕ X) → Scalar) (c : C) (x : X) :
    eliminate (c, x) (contextual f) =
      contextual (Function.update f c (eliminate x (f c))) := by
  funext i j
  let source := Equiv.prodSumDistrib C I X
  let target := Equiv.prodSumDistrib C E X
  obtain ⟨⟨si, ri⟩, rfl⟩ := source.surjective i
  obtain ⟨⟨tj, rj⟩, rfl⟩ := target.surjective j
  change contextual f (source (si, ri)) (target (tj, rj)) +
    contextual f (source (si, ri)) (target (c, .inr x)) *
      Scalar.star (contextual f (source (c, .inr x)) (target (c, .inr x))) *
      contextual f (source (c, .inr x)) (target (tj, rj)) = _
  simp only [contextual, source, target, Equiv.symm_apply_apply, ↓reduceIte]
  by_cases h : si = c
  · subst si
    by_cases k : c = tj <;> simp [k, eliminate]
  · by_cases k : si = tj
    · subst tj
      simp [h, Ne.symm h]
    · simp [h, k]

theorem contextual_schedule {C I X E : Type} [DecidableEq C]
    (f : C → (I ⊕ X) → (E ⊕ X) → Scalar) (states : List (C × X)) :
    states.foldr eliminate (contextual f) =
      contextual (fun c =>
        (states.filterMap (fun s => if s.1 = c then some s.2 else none)).foldr eliminate (f c)) := by
  induction states with
  | nil => rfl
  | cons head tail ih =>
    obtain ⟨c, x⟩ := head
    rw [List.foldr_cons, ih, eliminate_contextual]
    congr 1
    funext d
    by_cases h : c = d
    · subst d
      simp
    · simp [h, Ne.symm h]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BinaryFoldBitMatrixContext
