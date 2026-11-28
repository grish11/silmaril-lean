module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Phases.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Bekic.Defs

/-! # Two classes of states, duplicated together -/

@[expose] public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory

open CategoryTheory CategoryTheory.Limits

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- `n + 1` interleaved pairs of an `A` state and a `B` state:
`A + (B + (A + (B + …)))`. Each class is duplicated `n + 1` times. -/
def pairPhases (A B : τ) : Nat → τ
  | 0 => Silmaril.coprod A B
  | n + 1 => Silmaril.coprod A (Silmaril.coprod B (pairPhases A B n))

/-- Forget which duplicate: every `A` state goes to `A` and every `B`
state to `B`. This is the sum of the two class folds. -/
noncomputable def pairFold (A B : τ) :
    (n : Nat) → (ofType (Φ := Φ) (pairPhases A B n) ⟶ ofType (Silmaril.coprod A B))
  | 0 => 𝟙 _
  | n + 1 => (sumIso A _).hom ≫ coprod.desc (sumInl A B)
      ((sumIso B _).hom ≫ coprod.desc (sumInr A B) (pairFold A B n))

/-- Reassociate an exact sum. -/
noncomputable def sumAssoc (X Y W : τ) :
    ofType (Φ := Φ) (Silmaril.coprod X (Silmaril.coprod Y W)) ≅
      ofType (Silmaril.coprod (Silmaril.coprod X Y) W) :=
  sumIso X (Silmaril.coprod Y W) ≪≫ coprod.mapIso (Iso.refl _) (sumIso Y W) ≪≫
    (coprod.associator _ _ _).symm ≪≫ coprod.mapIso (sumIso X Y).symm (Iso.refl _) ≪≫
      (sumIso (Silmaril.coprod X Y) W).symm

/-- An iso on the right summand of an exact sum. -/
noncomputable def sumMapIso (R : τ) {D E : τ} (i : ofType (Φ := Φ) D ≅ ofType E) :
    ofType (Φ := Φ) (Silmaril.coprod R D) ≅ ofType (Silmaril.coprod R E) :=
  sumIso R D ≪≫ coprod.mapIso (Iso.refl _) i ≪≫ (sumIso R E).symm

/-- Pairs of duplicates are phases of the pair `A + B`. -/
noncomputable def pairIso (A B : τ) :
    (n : Nat) → (ofType (Φ := Φ) (pairPhases A B n) ≅ ofType (phaseType (Silmaril.coprod A B) n))
  | 0 => Iso.refl _
  | n + 1 => sumAssoc A B (pairPhases A B n) ≪≫ sumMapIso (Silmaril.coprod A B) (pairIso A B n)

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
