module

public import Silmaril.SSA.Isotope.LetIter.Heap.Institution.Defs
import Silmaril.Proofs.SSA.Isotope.LetIter.Heap.Institution.Equivariance

@[expose] public section

namespace Silmaril.Isotope.LetIter.Heap

open CategoryTheory Silmaril.Elgot Silmaril.Elgot.ITree
open Silmaril.Logic.ITree (Model Sentence Sat satisfaction sat_renameState)

universe v

variable {I J K : Type}

@[simp] theorem heapRename_id : heapRename (Equiv.refl I) = 𝟙 (heapSignature I) :=
  InstitutionProofs.heapRename_id

theorem heapRename_comp (e : I ≃ J) (d : J ≃ K) :
    heapRename (e.trans d) = heapRename e ≫ heapRename d :=
  InstitutionProofs.heapRename_comp e d

@[simp] theorem readRename_id : readRename (Equiv.refl I) = 𝟙 (readSignature I) :=
  InstitutionProofs.readRename_id

theorem readRename_comp (e : I ≃ J) (d : J ≃ K) :
    readRename (e.trans d) = readRename e ≫ readRename d :=
  InstitutionProofs.readRename_comp e d

theorem readInclusion_natural (e : I ≃ J) :
    readInclusion I ≫ heapRename e = readRename e ≫ readInclusion J :=
  InstitutionProofs.readInclusion_natural e

/-- The heap signature acts on the existing groupoid of types and isomorphisms. -/
def heapSignatures : Reindex.IndexGroupoid.{0} ⥤ ITree.Signature where
  obj I := heapSignature I.of
  map f := heapRename f.iso.toEquiv
  map_id _ := heapRename_id
  map_comp f g := heapRename_comp f.iso.toEquiv g.iso.toEquiv

/-- The read-only signature acts on the same groupoid. -/
def readSignatures : Reindex.IndexGroupoid.{0} ⥤ ITree.Signature where
  obj I := readSignature I.of
  map f := readRename f.iso.toEquiv
  map_id _ := readRename_id
  map_comp f g := readRename_comp f.iso.toEquiv g.iso.toEquiv

def readInclusions : readSignatures ⟶ heapSignatures where
  app I := readInclusion I.of
  naturality _ _ f := (readInclusion_natural f.iso.toEquiv).symm

/-- Reduce the target heap back to source requests, keeping its target store
type. The result is the source heap with its stores relabelled forward. -/
theorem heapModel_reduct (e : I ≃ J) :
    (heapModel J).reduct (heapRename e) = (heapModel I).renameState (storeEquiv e) :=
  InstitutionProofs.heapModel_reduct e

theorem readModel_reduct (e : I ≃ J) :
    ((heapModel J).reduct (readInclusion J)).reduct (readRename e) =
      ((heapModel I).reduct (readInclusion I)).renameState (storeEquiv e) := by
  rw [← Model.reduct_comp, ← readInclusion_natural, Model.reduct_comp, heapModel_reduct]
  exact Model.reduct_renameState (readInclusion I) (heapModel I) (storeEquiv e)

/-- Translation into the heap commutes with signature renaming. -/
theorem translate_readInclusion (e : I ≃ J) (φ : Sentence.{0,v} (readSignature I)) :
    (φ.translate (readInclusion I)).translate (heapRename e) =
      (φ.translate (readRename e)).translate (readInclusion J) := by
  rw [← Sentence.translate_comp, readInclusion_natural, Sentence.translate_comp]

theorem heap_sat_rename (e : I ≃ J) (φ : Sentence.{0,v} (heapSignature I)) :
    Sat (heapModel J) (φ.translate (heapRename e)) ↔ Sat (heapModel I) φ := by
  rw [satisfaction, heapModel_reduct]
  exact sat_renameState (heapModel I) (storeEquiv e) φ

theorem read_sat_rename (e : I ≃ J) (φ : Sentence.{0,v} (readSignature I)) :
    Sat ((heapModel J).reduct (readInclusion J)) (φ.translate (readRename e)) ↔
      Sat ((heapModel I).reduct (readInclusion I)) φ := by
  rw [satisfaction, readModel_reduct]
  exact sat_renameState ((heapModel I).reduct (readInclusion I)) (storeEquiv e) φ

end Silmaril.Isotope.LetIter.Heap
