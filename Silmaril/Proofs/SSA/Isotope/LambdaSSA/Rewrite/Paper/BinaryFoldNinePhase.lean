module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.NinePhase.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.StructuralValues.Coproducts.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Tripling.Components.Structural.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BinaryFoldNinePhase

open Silmaril.Isotope.LambdaSSA.Region
open Paper.WithCaseReturns.BinaryFold.WithTripling (Step triple_step)
open Paper.WithCaseReturns.BinaryFold.WithTripling.NinePhase
open Paper.Extension.Singleton.ThreeCycle (square fold_iff_triple uniformity_of_cycleRows transportStep)
open Paper.Extension.Singleton
  (sumCofan sumCofanIsColimit sumCofan_inl_sumIso_hom sumCofan_inr_sumIso_hom
    uniformity_of_composed_squares uniformity_of_iso)
open Paper.Extension.Singleton.StructuralValues (HomProperty copair_mem)
open CategoryTheory CategoryTheory.Limits
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton
  (ofType iterateChosen sumIso)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.ThreeCycle
  (fold step triple cycleRows batchRows)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.ValueCoproducts (exactCopair)

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

set_option hygiene false in
local notation "T" => Step (τ := τ) (Φ := Φ) pe
set_option hygiene false in
local notation "Q" => Paper.Extension.Singleton.TypeCategory T
local notation "Copies" A:max => (A ⨿ (A ⨿ A))
set_option hygiene false in
local notation "Obj" => ofType T
set_option hygiene false in
local notation "I" => iterateChosen T

set_option backward.isDefEq.respectTransparency false

private theorem stay_square {A B : Q} (g : A ⟶ B ⨿ A) :
    stay pe g ≫ coprod.map (𝟙 B) (fold A) = fold A ≫ g := by
  apply coprod.hom_ext
  · simp [stay]
  · apply coprod.hom_ext <;> simp [stay]

private theorem stay_then_step {A B : Q} (f g : A ⟶ B ⨿ A) :
    stay pe f ≫ coprod.desc coprod.inl (step g) =
      step (f ≫ coprod.desc coprod.inl g) := by
  have leg (i j : A ⟶ Copies A) (row : i ≫ step g = g ≫ coprod.map (𝟙 B) j) :
      (f ≫ coprod.map (𝟙 B) i) ≫ coprod.desc coprod.inl (step g) =
        (f ≫ coprod.desc coprod.inl g) ≫ coprod.map (𝟙 B) j := by
    rw [Category.assoc, coprod.map_desc, Category.id_comp, row]
    simp only [Category.assoc, coprod.desc_comp, coprod.inl_map, Category.id_comp]
  apply coprod.hom_ext
  · simpa only [stay, step, coprod.inl_desc_assoc, coprod.inl_desc, Category.assoc] using
      leg coprod.inl (coprod.inl ≫ coprod.inr) (by simp [step])
  · apply coprod.hom_ext
    · simpa only [stay, step, coprod.inr_desc_assoc, coprod.inl_desc_assoc, coprod.inl_desc,
        coprod.inr_desc, Category.assoc] using
        leg (coprod.inl ≫ coprod.inr) (coprod.inr ≫ coprod.inr) (by simp [step])
    · simpa only [stay, step, coprod.inr_desc_assoc, coprod.inr_desc, Category.assoc] using
        leg (coprod.inr ≫ coprod.inr) coprod.inl (by simp [step])

theorem batch_eq {A B : Q} (g : A ⟶ B ⨿ A) :
    batchRows (stay pe g) (stay pe g) (step g) = step (triple g) := by
  rw [batchRows, stay_then_step, stay_then_step]

private theorem cycle_uniformity {A B : Q} (g : A ⟶ B ⨿ A) :
    I (step g) = fold A ≫ I g := by
  obtain ⟨a⟩ := A
  obtain ⟨b⟩ := B
  exact (fold_iff_triple T g).mpr (triple_step (τ := τ) (Φ := Φ) pe (A := a) (B := b) g)

private theorem nine_square {A B : Q} (g : A ⟶ B ⨿ A) :
    nineStep pe g ≫ coprod.map (𝟙 B) (foldInner pe A) = foldInner pe A ≫ step g := by
  have route (i : A ⟶ Copies A) (j : Copies A ⟶ Copies (Copies A))
      (align : j ≫ foldInner pe A = fold A ≫ i) (f : Copies A ⟶ B ⨿ Copies A)
      (comm : f ≫ coprod.map (𝟙 B) (fold A) = fold A ≫ g) :
      f ≫ coprod.map (𝟙 B) j ≫ coprod.map (𝟙 B) (foldInner pe A) =
        fold A ≫ g ≫ coprod.map (𝟙 B) i := by
    calc
      _ = (f ≫ coprod.map (𝟙 B) (fold A)) ≫ coprod.map (𝟙 B) i := by
        simp only [Category.assoc, coprod.map_map, Category.id_comp, align]
      _ = _ := by rw [comm, Category.assoc]
  apply coprod.hom_ext
  · simpa only [nineStep, cycleRows, step, foldInner, coprod.inl_desc_assoc, coprod.inl_desc,
      coprod.inl_map_assoc, Category.assoc] using
      route (coprod.inl ≫ coprod.inr) (coprod.inl ≫ coprod.inr) (by simp) (stay pe g) (stay_square pe g)
  · apply coprod.hom_ext
    · simpa only [nineStep, cycleRows, step, foldInner, coprod.inr_desc_assoc, coprod.inl_desc_assoc,
        coprod.inl_desc, coprod.inr_desc, coprod.inr_map_assoc, coprod.inl_map_assoc, Category.assoc] using
        route (coprod.inr ≫ coprod.inr) (coprod.inr ≫ coprod.inr) (by simp) (stay pe g) (stay_square pe g)
    · simpa only [nineStep, cycleRows, step, foldInner, coprod.inr_desc_assoc, coprod.inr_desc,
        coprod.inr_map_assoc, Category.assoc] using
        route coprod.inl coprod.inl (by simp) (step g) (square T g)

theorem uniformity {A B : Q} (g : A ⟶ B ⨿ A) :
    nineStep pe g ≫ coprod.map (𝟙 B) (foldInner pe A ≫ fold A) = (foldInner pe A ≫ fold A) ≫ g ∧
      I (nineStep pe g) = (foldInner pe A ≫ fold A) ≫ I g := by
  have batch : I (batchRows (stay pe g) (stay pe g) (step g)) = fold A ≫ I (triple g) := by
    rw [batch_eq, cycle_uniformity]
  have inner : I (nineStep pe g) = foldInner pe A ≫ I (step g) :=
    uniformity_of_cycleRows T (fold A) (stay pe g) (stay pe g) (step g) g g g
      (stay_square pe g) (square T g) batch
  exact uniformity_of_composed_squares T (foldInner pe A) (fold A) (nineStep pe g) (step g) g
    (nine_square pe g) (square T g) (fun _ => inner) (fun _ => cycle_uniformity pe g)

theorem exactFold_mem (A : τ) : HomProperty T (exactFold pe A) := by
  let h := (HomProperty T).id_mem (Obj A)
  exact copair_mem T h (copair_mem T h h)

private theorem exactFold_eq (A : τ) : exactFold pe A = (phaseIso pe A).hom ≫ fold (Obj A) := by
  have copair {X Y : τ} {D : Q} (l : Obj X ⟶ D) (r : Obj Y ⟶ D) :
      exactCopair T l r = (sumIso T X Y).hom ≫ coprod.desc l r := by
    apply BinaryCofan.IsColimit.hom_ext (sumCofanIsColimit T X Y)
    · rw [← Category.assoc, sumCofan_inl_sumIso_hom, coprod.inl_desc]
      exact (sumCofanIsColimit T X Y).fac (BinaryCofan.mk l r) ⟨WalkingPair.left⟩
    · rw [← Category.assoc, sumCofan_inr_sumIso_hom, coprod.inr_desc]
      exact (sumCofanIsColimit T X Y).fac (BinaryCofan.mk l r) ⟨WalkingPair.right⟩
  rw [exactFold, copair, copair, phaseIso, Iso.trans_hom, Category.assoc, coprod.mapIso_hom,
    Iso.refl_hom, coprod.map_desc, Category.id_comp]

private theorem exact_composite (A : τ) :
    (nineIso pe A).hom ≫ foldInner pe (Obj A) ≫ fold (Obj A) = exactFold pe (phase A) ≫ exactFold pe A := by
  let e := phaseIso (Φ := Φ) pe A
  let h := e.hom ≫ fold (Obj A)
  have natural : coprod.map h (coprod.map h h) ≫ fold (Obj A) = fold (Obj (phase A)) ≫ h := by
    apply coprod.hom_ext
    · simp
    · apply coprod.hom_ext <;> simp
  rw [exactFold_eq, exactFold_eq, Category.assoc]
  change (nineIso pe A).hom ≫ foldInner pe (Obj A) ≫ fold (Obj A) =
    (phaseIso pe (phase A)).hom ≫ fold (Obj (phase A)) ≫ h
  have mapped :
      coprod.map e.hom (coprod.map e.hom e.hom) ≫ foldInner pe (Obj A) =
        coprod.map h (coprod.map h h) := by
    simp only [foldInner, coprod.map_map, h]
  rw [nineIso, Iso.trans_hom, coprod.mapIso_hom, coprod.mapIso_hom, Category.assoc,
    ← Category.assoc (coprod.map e.hom (coprod.map e.hom e.hom)), mapped, natural]

theorem exact_uniformity {A : τ} {B : Q} (g : Obj A ⟶ B ⨿ Obj A) :
    exactStep pe g ≫ coprod.map (𝟙 B) (exactFold pe (phase A) ≫ exactFold pe A) =
        (exactFold pe (phase A) ≫ exactFold pe A) ≫ g ∧
      I (exactStep pe g) = (exactFold pe (phase A) ≫ exactFold pe A) ≫ I g := by
  let e := nineIso (Φ := Φ) pe A
  let h := foldInner pe (Obj A) ≫ fold (Obj A)
  have foldExact : exactFold pe (phase A) ≫ exactFold pe A = e.hom ≫ h := by
    simpa only [e, h] using (exact_composite (Φ := Φ) pe A).symm
  have sectionSquare : exactStep pe g ≫ coprod.map (𝟙 B) e.hom = e.hom ≫ nineStep pe g := by
    simp only [exactStep, transportStep, Category.assoc, coprod.map_map, e,
      Iso.inv_hom_id, coprod.map_id_id, Category.comp_id]
  obtain ⟨comm, iter⟩ := uniformity pe g
  rw [foldExact]
  constructor
  · calc
      _ = (exactStep pe g ≫ coprod.map (𝟙 B) e.hom) ≫ coprod.map (𝟙 B) h := by
        rw [Category.assoc, coprod.map_map, Category.id_comp]
      _ = (e.hom ≫ nineStep pe g) ≫ coprod.map (𝟙 B) h := by rw [sectionSquare]
      _ = _ := by rw [Category.assoc, comm, ← Category.assoc]
  · simp only [uniformity_of_iso T e _ _ sectionSquare, iter, Category.assoc, h]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BinaryFoldNinePhase
