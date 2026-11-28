module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.CfgReadback.SlotMaps.Defs

/-! # State-slot maps on an appended label interface -/

@[expose] public section

universe u u₁ v₁

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel)

variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
  {κ : Type u} (M : TypeModel (Ty κ) V) {n : Nat} {P Q : Fin n → Ty κ}

theorem appendLocal (P : Fin n → Ty κ) (L : LCtx (Ty κ)) : Ren (List.ofFn P) (List.ofFn P ++ L) id :=
  fun {i} {_} h => by
    have lt := (List.getElem?_eq_some_iff.mp h).1
    exact (List.getElem?_append_left lt).trans h

theorem appendExit (P : Fin n → Ty κ) (L : LCtx (Ty κ)) : Ren L (List.ofFn P ++ L) (n + ·) :=
  fun {_} {_} h => by simpa [At, List.getElem?_append_right] using h

/-- Reassemble the local and outward summands in their original label order. -/
noncomputable def mergeLabels (P : Fin n → Ty κ) (L : LCtx (Ty κ)) :
    labelObj M L ⨿ labelObj M (List.ofFn P) ⟶ labelObj M (List.ofFn P ++ L) :=
  coprod.desc (labelMap M (appendExit P L)) (labelMap M (appendLocal P L))

/-- Apply indexed maps to the local prefix and keep the entire exit suffix. -/
noncomputable def mapSlotBoundary (slot : ∀ i, M.obj (P i) ⟶ M.obj (Q i)) (L : LCtx (Ty κ)) :
    labelObj M (List.ofFn P ++ L) ⟶ labelObj M (List.ofFn Q ++ L) :=
  labelAppendSplit M (List.ofFn P) L ≫ coprod.map (𝟙 _) (mapSlotLabels M slot) ≫ mergeLabels M Q L

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical
