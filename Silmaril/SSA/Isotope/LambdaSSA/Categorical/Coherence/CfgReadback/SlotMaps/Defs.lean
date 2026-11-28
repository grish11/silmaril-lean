module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.CfgReadback.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.LabelRenaming.Defs

/-! # Componentwise maps of finite CFG state coproducts -/

@[expose] public section

universe u u₁ v₁

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel)

variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
  {κ : Type u} (M : TypeModel (Ty κ) V) {n : Nat} {P Q : Fin n → Ty κ}

/-- Act on each state payload without changing its finite label index. -/
noncomputable def mapSlotLabels (slot : ∀ i, M.obj (P i) ⟶ M.obj (Q i)) :
    labelObj M (List.ofFn P) ⟶ labelObj M (List.ofFn Q) :=
  labelObjToFinite M P ≫ Sigma.desc fun i =>
    slot i ≫ labelInject M i (L := List.ofFn Q) (by simp [At])

/-- The component of a head map at an ordinal of the full interface. -/
noncomputable def mapLabelHeadComponent {A B : Ty κ} (L : LCtx (Ty κ)) (h : M.obj A ⟶ M.obj B)
    (i : Fin (A :: L).length) : M.obj ((A :: L).get i) ⟶ labelObj M (B :: L) :=
  Fin.cases (h ≫ labelInject M 0 (rfl : At (B :: L) 0 B))
    (fun j => labelInject M (j.val + 1) (show At (B :: L) (j.val + 1) (L.get j) from labelAt_get L j)) i

/-- Map the first label and preserve the entire ordered suffix. -/
noncomputable def mapLabelHead {A B : Ty κ} (L : LCtx (Ty κ)) (h : M.obj A ⟶ M.obj B) :
    labelObj M (A :: L) ⟶ labelObj M (B :: L) :=
  Sigma.desc (mapLabelHeadComponent M L h)

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical
