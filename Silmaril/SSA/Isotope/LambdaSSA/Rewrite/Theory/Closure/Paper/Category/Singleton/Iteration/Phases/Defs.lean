module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Defs

/-! # Phases of a state type and the map forgetting the phase -/

@[expose] public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory

open CategoryTheory CategoryTheory.Limits

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- `k + 1` phases of the state `A`: the right-nested sum `A + (A + (… + A))`. -/
def phaseType (A : τ) : Nat → τ
  | 0 => A
  | k + 1 => Silmaril.coprod A (phaseType A k)

/-- Forget the phase. On one phase it is the identity. On more it is case
analysis on the exact sum with the identity on the first summand. -/
noncomputable def phaseFold (A : τ) : (k : Nat) → (ofType (Φ := Φ) (phaseType A k) ⟶ ofType A)
  | 0 => 𝟙 _
  | k + 1 => (sumIso A (phaseType A k)).hom ≫ coprod.desc (𝟙 _) (phaseFold A k)

/-- The state as the first of `k + 2` phases. -/
noncomputable def phaseInl (A : τ) (k : Nat) : ofType (Φ := Φ) A ⟶ ofType (phaseType A (k + 1)) :=
  coprod.inl ≫ (sumIso A (phaseType A k)).inv

/-- The later phases. -/
noncomputable def phaseInr (A : τ) (k : Nat) :
    ofType (Φ := Φ) (phaseType A k) ⟶ ofType (phaseType A (k + 1)) :=
  coprod.inr ≫ (sumIso A (phaseType A k)).inv

/-- A state row joined with a block of `k + 1` phases. The row exits or
enters the block. The block exits, returns to the state, or stays in the
block. -/
noncomputable def joinedStep (A : τ) (k : Nat) {Y : τ}
    (a : ofType (Φ := Φ) A ⟶ ofType Y ⨿ ofType (phaseType A k))
    (c : ofType (Φ := Φ) (phaseType A k) ⟶ (ofType Y ⨿ ofType A) ⨿ ofType (phaseType A k)) :
    ofType (Φ := Φ) (phaseType A (k + 1)) ⟶ ofType Y ⨿ ofType (phaseType A (k + 1)) :=
  (sumIso A (phaseType A k)).hom ≫ coprod.desc (a ≫ coprod.map (𝟙 _) (phaseInr A k))
    (c ≫ coprod.desc (coprod.map (𝟙 _) (phaseInl A k)) (phaseInr A k ≫ coprod.inr))

/-- Keep the state and fold the block: `id + phaseFold`. -/
noncomputable def partialFold (A : τ) (k : Nat) :
    ofType (Φ := Φ) (phaseType A (k + 1)) ⟶ ofType (phaseType A 1) :=
  (sumIso A (phaseType A k)).hom ≫ coprod.desc (phaseInl A 0) (phaseFold A k ≫ phaseInr A 0)

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
