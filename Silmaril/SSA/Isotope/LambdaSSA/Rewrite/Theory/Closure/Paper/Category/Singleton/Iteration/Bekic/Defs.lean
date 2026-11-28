module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Defs

/-! # Two blocks at an exact sum type -/

@[expose] public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory

open CategoryTheory CategoryTheory.Limits

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- The left constructor injection of an exact sum. -/
noncomputable def sumInl (R P : τ) : ofType (Φ := Φ) R ⟶ ofType (Silmaril.coprod R P) :=
  coprod.inl ≫ (sumIso R P).inv

/-- The right constructor injection of an exact sum. -/
noncomputable def sumInr (R P : τ) : ofType (Φ := Φ) P ⟶ ofType (Silmaril.coprod R P) :=
  coprod.inr ≫ (sumIso R P).inv

/-- A row exits, repeats into the left block, or enters the right block. -/
noncomputable def blockRoute (R P Y : τ) :
    (ofType (Φ := Φ) Y ⨿ ofType R) ⨿ ofType P ⟶ ofType Y ⨿ ofType (Silmaril.coprod R P) :=
  coprod.desc (coprod.map (𝟙 _) (sumInl R P)) (sumInr R P ≫ coprod.inr)

/-- The joined step of a left row `r` and a right row `c` at the exact sum
`R + P`. Each row may exit, go to `R`, or go to `P`. -/
noncomputable def blockStep (R P : τ) {Y : τ}
    (r : ofType (Φ := Φ) R ⟶ (ofType Y ⨿ ofType R) ⨿ ofType P)
    (c : ofType (Φ := Φ) P ⟶ (ofType Y ⨿ ofType R) ⨿ ofType P) :
    ofType (Φ := Φ) (Silmaril.coprod R P) ⟶ ofType Y ⨿ ofType (Silmaril.coprod R P) :=
  (sumIso R P).hom ≫ coprod.desc (r ≫ blockRoute R P Y) (c ≫ blockRoute R P Y)

/-- Keep the left summand and map the right one: `id_R + h`. -/
noncomputable def sumMap (R : τ) {D E : τ} (h : ofType (Φ := Φ) D ⟶ ofType E) :
    ofType (Φ := Φ) (Silmaril.coprod R D) ⟶ ofType (Silmaril.coprod R E) :=
  (sumIso R D).hom ≫ coprod.desc (sumInl R E) (h ≫ sumInr R E)

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
