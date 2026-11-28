module

public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingWithUnaryReturns.LiveTable.Routes

@[expose] public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingWithUnaryReturns.LiveTable

open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical.SingletonDispatcher (labelHom_ext)
open Silmaril.Isotope.LambdaSSA.Region (packedExitType)
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel)
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open CartesianMonoidalCategory (fst snd)

universe u u₁ v₁
variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
  {τ : Type u} [TypeFormers τ] (M : TypeModel τ V)

set_option backward.isDefEq.respectTransparency false

noncomputable def finiteLabelToList {n : Nat} (R : Fin n → τ) :
    finiteLabelObj M R ⟶ labelObj M (List.ofFn R) :=
  Sigma.desc (fun i => labelInject M i (A := R i) (by simp [At, i.isLt]))

@[reassoc] theorem finiteLabelToList_leg {n : Nat} (R : Fin n → τ) (i : Fin n)
    (hi : At (List.ofFn R) i (R i)) :
    finiteLabelInject M R i ≫ finiteLabelToList M R = labelInject M i hi :=
  Sigma.ι_comp_desc _ _

noncomputable def finiteLabelListIso {n : Nat} (R : Fin n → τ) :
    finiteLabelObj M R ≅ labelObj M (List.ofFn R) where
  hom := finiteLabelToList M R
  inv := labelObjToFinite M R
  hom_inv_id := by
    apply Sigma.hom_ext
    intro i
    change finiteLabelInject M R i ≫ _ = finiteLabelInject M R i ≫ _
    rw [finiteLabelToList_leg_assoc M R i (by simp [At, i.isLt]),
      labelObjToFinite_local M R i, Category.comp_id]
  inv_hom_id := by
    apply labelHom_ext M
    intro i A hi
    obtain ⟨j, hj, hA⟩ : ∃ j : Fin n, i = j ∧ A = R j := by
      have h := List.getElem?_eq_some_iff.mp hi
      let j : Fin n := ⟨i, by simpa using h.1⟩
      have q : (List.ofFn R)[i]? = some (R j) := by simp [j, show i < n from j.isLt]
      exact ⟨j, rfl, Option.some.inj (hi.symm.trans q)⟩
    subst i
    subst A
    rw [← Category.assoc, labelObjToFinite_local M R j, finiteLabelToList_leg M R j hi,
      Category.comp_id]

variable [DistributiveTensor V]

/-- Pure comparison of the ordered coproduct of captured row packets with
the exact state type of the singleton dispatcher. -/
noncomputable def packetStateIso {n : Nat} (X : τ) (R : Fin (n + 1) → τ) :
    (∐ fun i => ctxObj M [X] ⊗ M.obj (R i)) ≅
      M.obj (Silmaril.product X (packedExitType (List.ofFn R))) :=
  ((colimit.isColimit (Discrete.functor (fun i => ctxObj M [X] ⊗ M.obj (R i)))).coconePointUniqueUpToIso
    (finitePacketCofanIsColimit M n [X] R)) ≪≫
      (MonoidalCategory.tensorLeft (ctxObj M [X])).mapIso (finiteLabelListIso M R) ≪≫
        capturedStateIso M X (List.ofFn R)

omit [DistributiveTensor V] in
theorem stateIso_hom (X : τ) (L : LCtx τ) :
    (capturedStateIso M X L).hom = packCapture M (lookup M 0 (rfl : At [X] 0 X)) L := by
  simp only [capturedStateIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, packLabelIso, packCapture]
  have h : lookup M 0 (rfl : At [X] 0 X) = (λ_ (M.obj X)).hom := by
    simp [lookup, CartesianMonoidalCategory.leftUnitor_hom]
    rfl
  simp only [h, MonoidalCategory.tensorHom_def', Category.assoc]
  rfl

omit [DistributiveTensor V] in
theorem stateIso_split (X : τ) (L : LCtx τ) :
    (capturedStateIso M X L).hom =
      (ctxObj M [X] ◁ packLabel M L) ≫ (rowInputIso M X (packedExitType L)).hom := by
  simp only [capturedStateIso, rowInputIso, Iso.trans_hom, Functor.mapIso_hom, packLabelIso]
  rfl

theorem packetStateIso_leg {n : Nat} (X : τ) (R : Fin (n + 1) → τ) (i : Fin (n + 1))
    (hi : At (List.ofFn R) i (R i)) :
    Sigma.ι (fun j => ctxObj M [X] ⊗ M.obj (R j)) i ≫ (packetStateIso M X R).hom =
      (ctxObj M [X] ◁ packedLabelInject M i hi) ≫
        (rowInputIso M X (packedExitType (List.ofFn R))).hom := by
  let E := ctxObj M [X]
  let c := colimit.isColimit (Discrete.functor (fun j => E ⊗ M.obj (R j)))
  let d := finitePacketCofanIsColimit M n [X] R
  have leg : Sigma.ι (fun j => E ⊗ M.obj (R j)) i ≫ (c.coconePointUniqueUpToIso d).hom =
      E ◁ finiteLabelInject M R i := by
    have h := c.comp_coconePointUniqueUpToIso_hom d ⟨i⟩
    change Sigma.ι (fun j => E ⊗ M.obj (R j)) i ≫ (c.coconePointUniqueUpToIso d).hom =
      (𝟙 E) ⊗ₘ finiteLabelInject M R i at h
    simpa only [MonoidalCategory.id_tensorHom] using h
  simp only [packetStateIso, Iso.trans_hom]
  rw [← Category.assoc, leg, stateIso_split]
  change (E ◁ finiteLabelInject M R i) ≫
    (E ◁ finiteLabelToList M R) ≫ (E ◁ packLabel M (List.ofFn R)) ≫ _ = _
  rw [← Category.assoc _ (E ◁ finiteLabelToList M R), ← MonoidalCategory.whiskerLeft_comp,
    finiteLabelToList_leg M R i hi, ← Category.assoc, ← MonoidalCategory.whiskerLeft_comp,
    labelInject_packLabel]

omit [DistributiveTensor V] in
@[reassoc] theorem row_capture (X A : τ) (L : LCtx τ) :
    (fst (ctxObj M [X]) (M.obj A) ▷ labelObj M L) ≫ (capturedStateIso M X L).hom =
      packCapture M (lookup M 1 (rfl : At [A, X] 1 X)) L := by
  rw [stateIso_hom]
  unfold packCapture
  rw [← Category.assoc,
    ← MonoidalCategory.tensorHom_id, MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp]
  rfl

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingWithUnaryReturns.LiveTable
