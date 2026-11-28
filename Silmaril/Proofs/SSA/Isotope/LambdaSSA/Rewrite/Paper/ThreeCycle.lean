module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Blocks.ThreeCycle.Defs

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ThreeCycle

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.Extension.Singleton
open Paper.Extension.Singleton.ThreeCycle
open CategoryTheory CategoryTheory.Limits

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

local notation "Q" => TypeCategory Seed
local notation "I" => iterateChosen Seed

theorem square {A B : Q} (g : A ⟶ B ⨿ A) :
    step g ≫ coprod.map (𝟙 B) (fold A) = fold A ≫ g := by
  apply coprod.hom_ext
  · simp [step]
  · apply coprod.hom_ext <;> simp [step]

private noncomputable def cut {A B : Q} (first middle last : A ⟶ B ⨿ A) :
    A ⨿ (A ⨿ A) ⟶ (B ⨿ A) ⨿ (A ⨿ A) :=
  coprod.desc (first ≫ coprod.map coprod.inl coprod.inl)
    (coprod.desc (middle ≫ coprod.map coprod.inl coprod.inr) (last ≫ coprod.inl))

private theorem cut_assoc {A B : Q} (first middle last : A ⟶ B ⨿ A) :
    cut Seed first middle last ≫ (coprod.associator B A (A ⨿ A)).hom = cycleRows first middle last := by
  apply coprod.hom_ext
  · simp only [cut, cycleRows, coprod.inl_desc_assoc, coprod.inl_desc, Category.assoc]
    congr 1
    apply coprod.hom_ext <;> simp [coprod.associator]
  · apply coprod.hom_ext
    · simp only [cut, cycleRows, coprod.inr_desc_assoc, coprod.inr_desc, coprod.inl_desc_assoc,
        coprod.inl_desc, Category.assoc]
      congr 1
      apply coprod.hom_ext <;> simp [coprod.associator]
    · simp only [cut, cycleRows, coprod.inr_desc_assoc, coprod.inr_desc, Category.assoc]
      congr 1
      apply coprod.hom_ext <;> simp [coprod.associator]

theorem iterate_cycleRows {A B : Q} (first middle last : A ⟶ B ⨿ A) :
    let batch := I (batchRows first middle last)
    I (cycleRows first middle last) = coprod.desc batch
      (coprod.desc ((middle ≫ coprod.desc coprod.inl last) ≫ coprod.desc (𝟙 B) batch)
        (last ≫ coprod.desc (𝟙 B) batch)) := by
  let right : A ⨿ A ⟶ (B ⨿ A) ⨿ (A ⨿ A) := coprod.inr ≫ cut Seed first middle last
  have rightLast : (coprod.inr : A ⟶ A ⨿ A) ≫ I right = last := by
    rw [iterateChosen_fixpoint Seed right]
    simp [right, cut]
  have rightMiddle : (coprod.inl : A ⟶ A ⨿ A) ≫ I right =
      middle ≫ coprod.desc coprod.inl last := by
    have row : (coprod.inl : A ⟶ A ⨿ A) ≫ right =
        middle ≫ coprod.map coprod.inl coprod.inr := by simp [right, cut]
    conv_lhs => rw [iterateChosen_fixpoint Seed right]
    rw [← Category.assoc, row]
    simp [rightLast]
  have rightEq : I right = coprod.desc (middle ≫ coprod.desc coprod.inl last) last :=
    coprod.hom_ext (by simpa using rightMiddle) (by simpa using rightLast)
  have entry : (coprod.inl : A ⟶ A ⨿ (A ⨿ A)) ≫ cut Seed first middle last ≫
      coprod.desc (𝟙 (B ⨿ A)) (I right) = batchRows first middle last := by
    simp [cut, rightEq]
  rw [← cut_assoc Seed first middle last, iterateChosen_rows Seed]
  change coprod.desc (I ((coprod.inl ≫ cut Seed first middle last) ≫ coprod.desc (𝟙 _) (I right)))
    (I right ≫ coprod.desc (𝟙 B) (I ((coprod.inl ≫ cut Seed first middle last) ≫ coprod.desc (𝟙 _) (I right)))) = _
  rw [Category.assoc, entry, rightEq, coprod.desc_comp]

theorem iterate_eq {A B : Q} (g : A ⟶ B ⨿ A) :
    I (step g) = coprod.desc (I (triple g))
      (coprod.desc ((g ≫ coprod.desc coprod.inl g) ≫ coprod.desc (𝟙 B) (I (triple g)))
        (g ≫ coprod.desc (𝟙 B) (I (triple g)))) := iterate_cycleRows Seed g g g

theorem uniformity_of_cycleRows {A D B : Q} (h : A ⟶ D)
    (first middle last : A ⟶ B ⨿ A) (first' middle' last' : D ⟶ B ⨿ D)
    (middleSquare : middle ≫ coprod.map (𝟙 B) h = h ≫ middle')
    (lastSquare : last ≫ coprod.map (𝟙 B) h = h ≫ last')
    (batch : I (batchRows first middle last) =
      h ≫ I (batchRows first' middle' last')) :
    I (cycleRows first middle last) =
      coprod.map h (coprod.map h h) ≫ I (cycleRows first' middle' last') := by
  let leftBatch := I (batchRows first middle last)
  let rightBatch := I (batchRows first' middle' last')
  have shift : coprod.map (𝟙 B) h ≫ coprod.desc coprod.inl last' =
      coprod.desc coprod.inl last ≫ coprod.map (𝟙 B) h := by
    apply coprod.hom_ext
    · simp
    · simpa using lastSquare.symm
  have suffix : (middle ≫ coprod.desc coprod.inl last) ≫ coprod.map (𝟙 B) h =
      h ≫ (middle' ≫ coprod.desc coprod.inl last') := by
    rw [Category.assoc, ← shift, ← Category.assoc middle, middleSquare, Category.assoc]
  have next : coprod.desc (𝟙 B) leftBatch = coprod.map (𝟙 B) h ≫ coprod.desc (𝟙 B) rightBatch := by
    rw [coprod.map_desc, Category.id_comp]
    exact congrArg (coprod.desc (𝟙 B)) batch
  have middleResult : (middle ≫ coprod.desc coprod.inl last) ≫ coprod.desc (𝟙 B) leftBatch =
      h ≫ ((middle' ≫ coprod.desc coprod.inl last') ≫ coprod.desc (𝟙 B) rightBatch) := by
    rw [next, ← Category.assoc, suffix, Category.assoc]
  have lastResult : last ≫ coprod.desc (𝟙 B) leftBatch = h ≫ (last' ≫ coprod.desc (𝟙 B) rightBatch) := by
    rw [next, ← Category.assoc, lastSquare, Category.assoc]
  rw [iterate_cycleRows, iterate_cycleRows, coprod.map_desc, coprod.map_desc]
  change coprod.desc leftBatch (coprod.desc
    ((middle ≫ coprod.desc coprod.inl last) ≫ coprod.desc (𝟙 B) leftBatch)
    (last ≫ coprod.desc (𝟙 B) leftBatch)) = _
  rw [middleResult, lastResult, show leftBatch = _ from batch]

theorem fold_iff_triple {A B : Q} (g : A ⟶ B ⨿ A) :
    I (step g) = fold A ≫ I g ↔ I (triple g) = I g := by
  rw [iterate_eq Seed g]
  constructor
  · intro h
    simpa using congrArg ((coprod.inl : A ⟶ A ⨿ (A ⨿ A)) ≫ ·) h
  · intro h
    rw [h]
    have unfold : g ≫ coprod.desc (𝟙 B) (I g) = I g := (iterateChosen_fixpoint Seed g).symm
    apply coprod.hom_ext
    · simp
    · apply coprod.hom_ext
      · simp only [coprod.inr_desc, coprod.inl_desc, Category.id_comp, Category.assoc, coprod.desc_comp,
          unfold]
      · simp [unfold]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ThreeCycle
