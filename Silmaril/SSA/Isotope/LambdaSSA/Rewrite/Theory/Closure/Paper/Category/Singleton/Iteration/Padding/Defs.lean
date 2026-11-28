module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Classes.Defs

/-! # Padding a table with unreachable states -/

@[expose] public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory

open CategoryTheory CategoryTheory.Limits

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- Case analysis on an exact sum. -/
noncomputable def sumDesc {U X T : τ} (a : ofType (Φ := Φ) U ⟶ ofType T) (b : ofType (Φ := Φ) X ⟶ ofType T) :
    ofType (Φ := Φ) (Silmaril.coprod U X) ⟶ ofType T :=
  (sumIso U X).hom ≫ coprod.desc a b

/-- Add the states `U` in front of a table `J` on `X`. The old states
keep their rows. A new state takes its class by `u`, runs the folded
table `T` there, and repeats into the old states through `s`. No old
state jumps to a new one. -/
noncomputable def padStep (U : τ) {X Z Y : τ} (u : ofType (Φ := Φ) U ⟶ ofType Z)
    (s : ofType (Φ := Φ) Z ⟶ ofType X) (J : ofType (Φ := Φ) X ⟶ ofType Y ⨿ ofType X)
    (T : ofType (Φ := Φ) Z ⟶ ofType Y ⨿ ofType Z) :
    ofType (Φ := Φ) (Silmaril.coprod U X) ⟶ ofType Y ⨿ ofType (Silmaril.coprod U X) :=
  sumDesc (u ≫ T ≫ coprod.map (𝟙 _) (s ≫ sumInr U X)) (J ≫ coprod.map (𝟙 _) (sumInr U X))

/-- The first `A` duplicate. -/
noncomputable def pairFirst (A B : τ) : (n : Nat) → (ofType (Φ := Φ) A ⟶ ofType (pairPhases A B n))
  | 0 => sumInl A B
  | _ + 1 => sumInl A _

/-- The class fold on `n + 2` duplicates of `B` and `n + 1` of `A`:
the pairs with the first `A` duplicate removed. -/
noncomputable def shortFold (A B : τ) (n : Nat) :
    ofType (Φ := Φ) (Silmaril.coprod B (pairPhases A B n)) ⟶ ofType (Silmaril.coprod A B) :=
  sumInr A _ ≫ pairFold A B (n + 1)

/-- A representative of each class among those states. -/
noncomputable def shortSection (A B : τ) (n : Nat) :
    ofType (Φ := Φ) (Silmaril.coprod A B) ⟶ ofType (Silmaril.coprod B (pairPhases A B n)) :=
  sumDesc (pairFirst A B n ≫ sumInr B _) (sumInl B _)

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
