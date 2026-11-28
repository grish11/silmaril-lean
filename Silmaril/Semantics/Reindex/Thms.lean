module

public import Silmaril.Semantics.Reindex.Defs

public section

namespace Silmaril.Reindex

universe u

open CategoryTheory

@[simp] theorem indexHom_refl (I : Type u) :
    indexHom I I (Equiv.refl I) = 𝟙 (⟨I⟩ : IndexGroupoid) := rfl

@[simp] theorem indexHom_trans {I J K : Type u} (e : Index I J) (f : Index J K) :
    indexHom I K (e.trans f) = indexHom I J e ≫ indexHom J K f := rfl

@[simp] theorem indexHom_symm {I J : Type u} (e : Index I J) :
    indexHom J I e.symm = Groupoid.inv (indexHom I J e) := rfl

variable {A B C D F G : Type*}

@[simp] theorem function_apply (a : A ≃ C) (b : B ≃ D) (f : A → B) (x : A) :
    function a b f (a x) = b (f x) := by
  change b (f (a.symm (a x))) = _
  rw [Equiv.symm_apply_apply]

@[simp] theorem relation_apply (a : A ≃ C) (b : B ≃ D) (r : A → B → Prop)
    (x : A) (y : B) : relation a b r (a x) (b y) ↔ r x y := by
  simp [relation]

@[simp] theorem relation_trans (a : A ≃ C) (b : B ≃ D) (a' : C ≃ F) (b' : D ≃ G)
    (r : A → B → Prop) :
    relation a' b' (relation a b r) = relation (a.trans a') (b.trans b') r := rfl

@[simp] theorem relation_refl (r : A → B → Prop) :
    relation (Equiv.refl A) (Equiv.refl B) r = r := rfl

@[simp] theorem language_apply (e : A ≃ B) (L : List A → Prop) (xs : List A) :
    language e L (Equiv.listEquivOfEquiv e xs) ↔ L xs := by
  unfold language
  rw [Equiv.symm_apply_apply]

@[simp] theorem language_refl (L : List A → Prop) :
    language (Equiv.refl A) L = L := by
  funext xs
  exact congrArg L (List.map_id xs)

@[simp] theorem language_trans (e : A ≃ B) (f : B ≃ C) (L : List A → Prop) :
    language f (language e L) = language (e.trans f) L := by
  funext xs
  change L (List.map e.symm (List.map f.symm xs)) = L (List.map (e.trans f).symm xs)
  rw [List.map_map]
  rfl

end Silmaril.Reindex
