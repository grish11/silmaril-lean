module

public import Silmaril.SSA.Isotope.LetIter.Heap.Institution.Defs

public section

namespace Silmaril.Isotope.LetIter.Heap.InstitutionProofs

open CategoryTheory Silmaril.Elgot Silmaril.Elgot.ITree
open Silmaril.Logic.ITree (Model)

variable {I J K : Type}

theorem valueEquiv_refl : valueEquiv (Equiv.refl I) = Equiv.refl (Value I) := by
  ext x
  cases x <;> rfl

theorem valueEquiv_trans (e : I ≃ J) (d : J ≃ K) :
    valueEquiv (e.trans d) = (valueEquiv e).trans (valueEquiv d) := by
  ext x
  cases x <;> rfl

theorem heapRename_id : heapRename (Equiv.refl I) = 𝟙 (heapSignature I) := by
  apply ITree.Signature.Hom.ext
  rintro ⟨_, ⟨f, x⟩⟩
  cases f with
  | alloc =>
    change (⟨⟨I, allocEvent (valueEquiv (Equiv.refl I) x)⟩, id⟩ :
      (p : Request (Event I)) × (p.1 → I)) = ⟨⟨I, allocEvent x⟩, id⟩
    rw [valueEquiv_refl]
    rfl
  | get =>
    change (⟨⟨Value I, getEvent x⟩, (valueEquiv (Equiv.refl I)).symm⟩ :
      (p : Request (Event I)) × (p.1 → Value I)) = ⟨⟨Value I, getEvent x⟩, id⟩
    rw [valueEquiv_refl]
    rfl
  | set =>
    change (⟨⟨PUnit, setEvent x.1 (valueEquiv (Equiv.refl I) x.2)⟩, id⟩ :
      (p : Request (Event I)) × (p.1 → PUnit)) = ⟨⟨PUnit, setEvent x.1 x.2⟩, id⟩
    rw [valueEquiv_refl]
    rfl
  | free => rfl

theorem heapRename_comp (e : I ≃ J) (d : J ≃ K) :
    heapRename (e.trans d) = heapRename e ≫ heapRename d := by
  apply ITree.Signature.Hom.ext
  rintro ⟨_, ⟨f, x⟩⟩
  cases f with
  | alloc =>
    change (⟨⟨K, allocEvent (valueEquiv (e.trans d) x)⟩, (e.trans d).symm⟩ :
      (p : Request (Event K)) × (p.1 → I)) =
        ⟨⟨K, allocEvent (valueEquiv d (valueEquiv e x))⟩, e.symm ∘ d.symm⟩
    rw [valueEquiv_trans]
    rfl
  | get =>
    change (⟨⟨Value K, getEvent (d (e x))⟩, (valueEquiv (e.trans d)).symm⟩ :
      (p : Request (Event K)) × (p.1 → Value I)) =
        ⟨⟨Value K, getEvent (d (e x))⟩, (valueEquiv e).symm ∘ (valueEquiv d).symm⟩
    rw [valueEquiv_trans]
    rfl
  | set =>
    change (⟨⟨PUnit, setEvent (d (e x.1)) (valueEquiv (e.trans d) x.2)⟩, id⟩ :
      (p : Request (Event K)) × (p.1 → PUnit)) =
        ⟨⟨PUnit, setEvent (d (e x.1)) (valueEquiv d (valueEquiv e x.2))⟩, id⟩
    rw [valueEquiv_trans]
    rfl
  | free => rfl

theorem readRename_id : readRename (Equiv.refl I) = 𝟙 (readSignature I) := by
  apply ITree.Signature.Hom.ext
  rintro ⟨_, ⟨i⟩⟩
  simp only [readRename, valueEquiv_refl]
  rfl

theorem readRename_comp (e : I ≃ J) (d : J ≃ K) :
    readRename (e.trans d) = readRename e ≫ readRename d := by
  apply ITree.Signature.Hom.ext
  rintro ⟨_, ⟨i⟩⟩
  simp only [readRename, valueEquiv_trans]
  rfl

theorem readInclusion_natural (e : I ≃ J) :
    readInclusion I ≫ heapRename e = readRename e ≫ readInclusion J := by
  apply ITree.Signature.Hom.ext
  rintro ⟨_, ⟨i⟩⟩
  rfl

theorem heapModel_reduct (e : I ≃ J) :
    (heapModel J).reduct (heapRename e) = (heapModel I).renameState (storeEquiv e) := by
  change Model.mk (Store J) (fun _ => True) _ = Model.mk (Store J) (fun _ => True) _
  apply congrArg (Model.mk (Store J) (fun _ => True))
  funext q x r y
  obtain ⟨x, rfl⟩ := (storeEquiv e).surjective x
  obtain ⟨y, rfl⟩ := (storeEquiv e).surjective y
  let a := (signatureEquiv e).reply q
  change (∃ r', a.symm r' = r ∧
    step ((signatureEquiv e).request q) (storeEquiv e x) r' (storeEquiv e y)) =
    step q ((storeEquiv e).symm (storeEquiv e x)) r ((storeEquiv e).symm (storeEquiv e y))
  rw [(storeEquiv e).symm_apply_apply, (storeEquiv e).symm_apply_apply]
  apply propext
  constructor
  · rintro ⟨r', hr, hs⟩
    have eq : r' = a r := by rw [← hr, Equiv.apply_symm_apply]
    exact (step_equivariant e q x r y).mp (eq ▸ hs)
  · intro h
    exact ⟨a r, a.symm_apply_apply r, (step_equivariant e q x r y).mpr h⟩

end Silmaril.Isotope.LetIter.Heap.InstitutionProofs
