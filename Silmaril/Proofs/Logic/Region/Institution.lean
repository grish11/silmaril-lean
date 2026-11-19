module

public import Silmaril.Logic.Region.Defs

@[expose] public section
namespace Silmaril.Logic.Region.Proofs
open CategoryTheory
open Silmaril.Semantics.Region

theorem satisfaction {A B : Signature} (f : A ⟶ B) (M : Model B) (p : Sentence A) :
    Sat M (p.map f) ↔ Sat (reduct f M) p := by
  induction p with
  | neg p ih => exact not_congr ih
  | conj p q ih jh => exact and_congr ih jh
  | _ => rfl

theorem map_id {A : Signature} (p : Sentence A) : p.map (𝟙 A) = p := by
  classical
  induction p <;> simp_all [Sentence.map, CategoryStruct.id, Finset.image_id]

theorem map_comp {A B C : Signature} (f : A ⟶ B) (g : B ⟶ C) (p : Sentence A) :
    p.map (f ≫ g) = (p.map f).map g := by
  classical
  induction p <;> simp_all [Sentence.map, CategoryStruct.comp, Finset.image_image, Option.map_map]

theorem reduct_id {A : Signature} (M : Model A) : reduct (𝟙 A) M = M := by
  classical
  cases M
  simp [reduct, CategoryStruct.id, Finset.image_id]

theorem reduct_comp {A B C : Signature} (f : A ⟶ B) (g : B ⟶ C) (M : Model C) :
    reduct (f ≫ g) M = reduct f (reduct g M) := by
  classical
  simp [reduct, CategoryStruct.comp, Finset.image_image, Option.map_map]

theorem reduct_laws {A B : Signature} (f : A ⟶ B) (M : Model B) (h : SegmentRegionLaws M) :
    SegmentRegionLaws (reduct f M) := by
  classical
  constructor
  · intro i a s e xs hb
    exact h.bb_seg _ _ _ _ _ hb
  · intro i a s e xs hb
    simpa [reduct, finiteBoundaryOps] using h.bb_reg _ _ _ _ _ hb
  · intro i a ss e x
    simpa [reduct, finiteBoundaryOps] using h.sr_iff (f.image i) (f.iface a) (ss.image f.segment) (f.label e) (f.label x)
  · intro i a ss e x
    have opt : (optionExits x).image f.label = optionExits (x.map f.label) := by
      cases x <;> simp [optionExits]
    simpa [reduct, finiteBoundaryOps, opt] using h.optional_iff (f.image i) (f.iface a) (ss.image f.segment) (f.label e) (x.map f.label)
end Silmaril.Logic.Region.Proofs
