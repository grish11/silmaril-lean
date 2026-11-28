module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Replay.Square.Native.Retained.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Replay.Square.Native.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Thms

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.RetainedNativeFrame

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.Paper
open WithBoundEntryEta.NativeFrame WithBoundEntryEta.NativeFrame.Retained
open CategoryTheory CategoryTheory.Limits
open Paper.TypeCategory (ofType ofRegion sumCofan sumIso)
open Paper.WithCaseReturns.BinaryFold (alternatingStep)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {D B : τ}

local notation "Obj" => ofType (Φ := Φ)
local notation "Tagged" => Silmaril.coprod D D

set_option backward.isDefEq.respectTransparency false

theorem foldInl : (sumCofan (Φ := Φ) D D).inl ≫ fold D = 𝟙 (Obj D) := by
  unfold fold
  rw [← Category.assoc, Paper.TypeCategory.sumCofan_inl_sumIso_hom, coprod.inl_desc]

theorem foldInr : (sumCofan (Φ := Φ) D D).inr ≫ fold D = 𝟙 (Obj D) := by
  unfold fold
  rw [← Category.assoc, Paper.TypeCategory.sumCofan_inr_sumIso_hom, coprod.inr_desc]

theorem fold_eq_case (D : τ) : fold (Φ := Φ) D = ofRegion (foldRegion_guarded (Φ := Φ) D) := by
  let idBranch : ValueBranches [D] (.br 0 (.var 0) : Region Φ) [D] := .br rfl (.var rfl)
  have idEq : ofRegion idBranch = 𝟙 (Obj D) := Paper.TypeCategory.ofRegion_id D
  unfold fold
  rw [← idEq]
  exact Paper.TypeCategory.coprod_desc_ofRegion idBranch idBranch

theorem switched_eq {work : Region Φ} (hw : ValueBranches [D] work [D]) :
    switched (B := B) hw = alternatingStep (single (B := B) hw) := by
  unfold switched split alternatingStep single
  simp only [Category.assoc, ← Category.assoc (sumCofan D D).inl (fold D),
    ← Category.assoc (sumCofan D D).inr (fold D), foldInl, foldInr, Category.id_comp, coprod.inr_map]

theorem fold_square {work : Region Φ} (hw : ValueBranches [D] work [D]) :
    alternatingStep (single (B := B) hw) ≫ coprod.map (𝟙 (Obj B)) (fold D) =
      fold D ≫ single (B := B) hw := by
  rw [← switched_eq]
  unfold switched single
  rw [split_post _ _ _ _ _ foldInr foldInl, Category.id_comp]

theorem fold_square_iff_single {work : Region Φ} (hw : ValueBranches [D] work [D])
    (target : Obj D ⟶ Obj B ⨿ Obj D) :
    alternatingStep (single (B := B) hw) ≫ coprod.map (𝟙 (Obj B)) (fold D) =
      fold D ≫ target ↔ single (B := B) hw = target := by
  rw [fold_square hw]
  constructor
  · intro eq
    have observed := congrArg (fun arrow => (sumCofan D D).inl ≫ arrow) eq
    rw [← Category.assoc (sumCofan D D).inl, foldInl, Category.id_comp,
      ← Category.assoc (sumCofan D D).inl, foldInl, Category.id_comp] at observed
    exact observed
  · rintro rfl
    rfl

theorem single_eq {work : Region Φ} (hw : ValueBranches [D] work [D]) :
    ofRegion (repeating_guarded (B := B) hw (.var (i := 0) rfl)) ≫ (sumIso B D).hom =
      single (B := B) hw := by
  rw [repeating_composite (B := B) hw (.var (i := 0) rfl), Paper.TypeCategory.ofRegion_id, Category.id_comp]
  rfl

theorem doubled_eq {work : Region Φ} (hw : ValueBranches [D] work [D]) :
    let g := single (B := B) hw
    ofRegion (repeating_guarded (B := B) (CfgEta.TypeCategory.seqValueBranches hw hw)
      (.var (i := 0) rfl)) ≫ (sumIso B D).hom = g ≫ coprod.desc coprod.inl g := by
  dsimp only
  rw [single_eq (B := B) (CfgEta.TypeCategory.seqValueBranches hw hw)]
  unfold single
  rw [← Paper.TypeCategory.ofRegion_comp hw hw (CfgEta.TypeCategory.seqValueBranches hw hw)]
  simp only [Category.assoc, coprod.inr_desc]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.RetainedNativeFrame
