module

public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.CfgSlotBoundary

/-! # Coordinates of the finite state map on an ordered boundary -/

public section

universe u u₁ v₁

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel)

variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
  {κ : Type u} (M : TypeModel (Ty κ) V) {n : Nat} {P Q : Fin n → Ty κ}

/-- Splitting after the boundary map gives the indexed state map and the same exits. -/
theorem mapSlotBoundary_split (slot : ∀ i, M.obj (P i) ⟶ M.obj (Q i)) (L : LCtx (Ty κ)) :
    mapSlotBoundary M slot L ≫ labelAppendSplit M (List.ofFn Q) L =
      labelAppendSplit M (List.ofFn P) L ≫ coprod.map (𝟙 _) (mapSlotLabels M slot) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.CfgSlotBoundary.split M slot L

theorem mapSlotBoundary_local (slot : ∀ i, M.obj (P i) ⟶ M.obj (Q i)) (L : LCtx (Ty κ)) (i : Fin n)
    (hi : At (List.ofFn P ++ L) i (P i)) (hj : At (List.ofFn Q ++ L) i (Q i)) :
    labelInject M i hi ≫ mapSlotBoundary M slot L = slot i ≫ labelInject M i hj :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.CfgSlotBoundary.local_coord M slot L i hi hj

theorem mapSlotBoundary_exit (slot : ∀ i, M.obj (P i) ⟶ M.obj (Q i)) (L : LCtx (Ty κ)) {i : Nat} {A : Ty κ}
    (hi : At L i A) (hp : At (List.ofFn P ++ L) (n + i) A) (hq : At (List.ofFn Q ++ L) (n + i) A) :
    labelInject M (n + i) hp ≫ mapSlotBoundary M slot L = labelInject M (n + i) hq :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.CfgSlotBoundary.exit_coord M slot L hi hp hq

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical
