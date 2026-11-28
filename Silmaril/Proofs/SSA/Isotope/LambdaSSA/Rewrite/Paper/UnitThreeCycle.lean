module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Blocks.ThreeCycle.Unit.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Tensor.Premonoidal.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Uniformity.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.UnitThreeCycle

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Paper.TypeCategory.UnitThreeCycle
open Paper.Extension.Singleton

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

local notation "P" => Paper.TypeCategory (τ := τ) Φ
local notation "U" => One (τ := τ) (Φ := Φ)
local notation "T" => Three (τ := τ) (Φ := Φ)
local notation "e" => split (τ := τ) (Φ := Φ)

open Paper.TypeCategory
  (ConstructorReturn discard_comp_branchValue sumIso sumCofan sumCofan_inl sumCofan_inr)

set_option backward.isDefEq.respectTransparency false

private theorem tagged_zero : (coprod.inl : U ⟶ U ⨿ (U ⨿ U)) ≫ (e).inv =
    (sumCofan unitTy twoTy).inl := by
  apply (cancel_mono (e).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  simp only [split, Iso.trans_hom, coprod.mapIso_hom, Iso.refl_hom]
  rw [← Category.assoc (sumCofan unitTy twoTy).inl, Paper.TypeCategory.sumCofan_inl_sumIso_hom]
  simp

private theorem tagged_one : (coprod.inl : U ⟶ U ⨿ U) ≫ coprod.inr ≫ (e).inv =
    (sumCofan unitTy unitTy).inl ≫ (sumCofan unitTy twoTy).inr := by
  apply (cancel_mono (e).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  simp only [split, Iso.trans_hom, coprod.mapIso_hom, Iso.refl_hom]
  rw [← Category.assoc (sumCofan unitTy twoTy).inr, Paper.TypeCategory.sumCofan_inr_sumIso_hom, coprod.inr_map,
    ← Category.assoc (sumCofan unitTy unitTy).inl, Paper.TypeCategory.sumCofan_inl_sumIso_hom]

private theorem tagged_two : (coprod.inr : U ⟶ U ⨿ U) ≫ coprod.inr ≫ (e).inv =
    (sumCofan unitTy unitTy).inr ≫ (sumCofan unitTy twoTy).inr := by
  apply (cancel_mono (e).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  simp only [split, Iso.trans_hom, coprod.mapIso_hom, Iso.refl_hom]
  rw [← Category.assoc (sumCofan unitTy twoTy).inr, Paper.TypeCategory.sumCofan_inr_sumIso_hom, coprod.inr_map,
    ← Category.assoc (sumCofan unitTy unitTy).inr, Paper.TypeCategory.sumCofan_inr_sumIso_hom]

theorem zero_forget : ((coprod.inl : U ⟶ U ⨿ (U ⨿ U)) ≫ (e).inv) ≫ forget = reset := by
  rw [tagged_zero, sumCofan_inl]
  exact discard_comp_branchValue (.inl (.var rfl))

private theorem inner_forget :
    (sumCofan (Φ := Φ) (unitTy (τ := τ)) twoTy).inr ≫ forget = Paper.TypeCategory.discardArrow twoTy := by
  rw [sumCofan_inr]
  exact discard_comp_branchValue (.inr (.var rfl))

theorem one_forget : ((coprod.inl : U ⟶ U ⨿ U) ≫ coprod.inr ≫ (e).inv) ≫ forget = reset := by
  rw [tagged_one, Category.assoc, inner_forget, sumCofan_inl]
  exact discard_comp_branchValue (.inl (.var rfl))

theorem two_forget : ((coprod.inr : U ⟶ U ⨿ U) ≫ coprod.inr ≫ (e).inv) ≫ forget = reset := by
  rw [tagged_two, Category.assoc, inner_forget, sumCofan_inr]
  exact discard_comp_branchValue (.inr (.var rfl))

theorem native_square {B : P} (g : U ⟶ B ⨿ U)
    (input : reset ≫ g = g) (output : g ≫ coprod.map (𝟙 B) reset = g) :
    step g ≫ coprod.map (𝟙 B) forget = forget ≫ g := by
  apply (cancel_epi (e).inv).mp
  rw [step, ← Category.assoc (e).inv, Iso.inv_hom_id_assoc]
  have branch {j k : U ⟶ T} (hj : j ≫ forget = reset) (hk : k ≫ forget = reset) :
      (g ≫ coprod.map (𝟙 B) k) ≫ coprod.map (𝟙 B) forget = j ≫ forget ≫ g := by
    rw [Category.assoc, coprod.map_map, Category.id_comp, hk, output, ← Category.assoc j, hj, input]
  apply coprod.hom_ext
  · simpa only [Category.assoc, coprod.inl_desc_assoc] using
      branch (zero_forget (Φ := Φ) (τ := τ)) (one_forget (Φ := Φ) (τ := τ))
  · apply coprod.hom_ext
    · simpa only [Category.assoc, coprod.inr_desc_assoc, coprod.inl_desc_assoc] using
        branch (one_forget (Φ := Φ) (τ := τ)) (two_forget (Φ := Φ) (τ := τ))
    · simpa only [Category.assoc, coprod.inr_desc_assoc] using
        branch (two_forget (Φ := Φ) (τ := τ)) (zero_forget (Φ := Φ) (τ := τ))

theorem native_iterate {B : P} (g : U ⟶ B ⨿ U)
    (input : reset ≫ g = g) (output : g ≫ coprod.map (𝟙 B) reset = g) :
    Paper.TypeCategory.iterate (step g) = forget ≫ Paper.TypeCategory.iterate g :=
  Paper.TypeCategory.iterate_uniformity_ofConstructorReturn
    (show ConstructorReturn (forget (Φ := Φ) (τ := τ)) from ⟨.unit, .unit, rfl⟩) _ _ (native_square g input output)

variable (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)
local notation "J" => projection Seed
local notation "Q" => TypeCategory Seed

private theorem projected_row {D Y B : P} (f : D ⟶ B ⨿ D) (g : Y ⟶ B ⨿ Y)
    (j k : Y ⟶ D) (row : j ≫ f = g ≫ coprod.map (𝟙 B) k) :
    (J).map j ≫ projectStep Seed f =
      projectStep Seed g ≫ coprod.map (𝟙 ((J).obj B)) ((J).map k) := by
  let c := PreservesColimitPair.iso (J)
  change (J).map j ≫ (J).map f ≫ (c B D).inv =
    ((J).map g ≫ (c B Y).inv) ≫ coprod.map (𝟙 ((J).obj B)) ((J).map k)
  rw [← (J).map_comp_assoc, row, (J).map_comp, Category.assoc, Category.assoc,
    ← (J).map_id B, coprodComparison_inv_map]

private noncomputable def splitProjected : (J).obj U ⨿ ((J).obj U ⨿ (J).obj U) ≅ (J).obj T :=
  coprod.mapIso (Iso.refl _) (PreservesColimitPair.iso (J) U U) ≪≫
    PreservesColimitPair.iso (J) U (U ⨿ U) ≪≫ (J).mapIso (e).symm

@[reassoc] private theorem splitProjected_zero :
    coprod.inl ≫ (splitProjected Seed).hom = (J).map (coprod.inl ≫ (e).inv) := by
  simp [splitProjected, PreservesColimitPair.iso_hom, ← Functor.map_comp]

@[reassoc] private theorem splitProjected_one :
    coprod.inl ≫ coprod.inr ≫ (splitProjected Seed).hom = (J).map (coprod.inl ≫ coprod.inr ≫ (e).inv) := by
  simp [splitProjected, PreservesColimitPair.iso_hom, ← Functor.map_comp]

@[reassoc] private theorem splitProjected_two :
    coprod.inr ≫ coprod.inr ≫ (splitProjected Seed).hom = (J).map (coprod.inr ≫ coprod.inr ≫ (e).inv) := by
  simp [splitProjected, PreservesColimitPair.iso_hom, ← Functor.map_comp]

private theorem projected_cycle {B : P} (g : U ⟶ B ⨿ U) :
    ThreeCycle.step (projectStep Seed g) ≫ coprod.map (𝟙 ((J).obj B)) (splitProjected Seed).hom =
      (splitProjected Seed).hom ≫ projectStep Seed (step g) := by
  let j₀ : U ⟶ T := coprod.inl ≫ (e).inv
  let j₁ : U ⟶ T := coprod.inl ≫ coprod.inr ≫ (e).inv
  let j₂ : U ⟶ T := coprod.inr ≫ coprod.inr ≫ (e).inv
  have l := projected_row Seed (step g) g j₀ j₁ (by simp [j₀, j₁, step])
  have m := projected_row Seed (step g) g j₁ j₂ (by simp [j₁, j₂, step])
  have r := projected_row Seed (step g) g j₂ j₀ (by simp [j₂, j₀, step])
  apply coprod.hom_ext
  · simpa only [ThreeCycle.step, coprod.inl_desc_assoc, Category.assoc, coprod.map_map,
      Category.id_comp, splitProjected_zero_assoc, splitProjected_one, j₀, j₁] using l.symm
  · apply coprod.hom_ext
    · simpa only [ThreeCycle.step, coprod.inl_desc_assoc, coprod.inr_desc_assoc, Category.assoc,
        coprod.map_map, Category.id_comp, splitProjected_one_assoc, splitProjected_two, j₁, j₂] using m.symm
    · simpa only [ThreeCycle.step, coprod.inr_desc_assoc, Category.assoc, coprod.map_map,
        Category.id_comp, splitProjected_two_assoc, splitProjected_zero, j₂, j₀] using r.symm

theorem triple_step_of_native_reset
    (includeUnit : ∀ {Γ L r s}, Paper.WithUnitEta.Step Γ r s L → Seed Γ r s L)
    {B : P} (g : U ⟶ B ⨿ U) (input : reset ≫ g = g) (output : g ≫ coprod.map (𝟙 B) reset = g) :
    iterateChosen Seed (ThreeCycle.triple (projectStep Seed g)) = iterateChosen Seed (projectStep Seed g) := by
  have resetId : (J).map (reset (τ := τ) (Φ := Φ)) = 𝟙 _ := unit_eta_of_include Seed includeUnit
  have foldEq : (splitProjected Seed).hom ≫ (J).map forget = ThreeCycle.fold ((J).obj U) := by
    have image {i : (J).obj U ⟶ (J).obj U ⨿ ((J).obj U ⨿ (J).obj U)} {j : U ⟶ T}
        (inj : i ≫ (splitProjected Seed).hom = (J).map j) (eq : j ≫ forget = reset) :
        i ≫ (splitProjected Seed).hom ≫ (J).map forget = 𝟙 _ := by
      rw [← Category.assoc i, inj, ← Functor.map_comp, eq, resetId]
    apply coprod.hom_ext
    · simpa using image (splitProjected_zero Seed) zero_forget
    · apply coprod.hom_ext
      · simpa [Category.assoc] using image (i := (coprod.inl : (J).obj U ⟶ (J).obj U ⨿ (J).obj U) ≫ coprod.inr)
          (by simpa only [Category.assoc] using splitProjected_one Seed) one_forget
      · simpa [Category.assoc] using image (i := (coprod.inr : (J).obj U ⟶ (J).obj U ⨿ (J).obj U) ≫ coprod.inr)
          (by simpa only [Category.assoc] using splitProjected_two Seed) two_forget
  apply (ThreeCycle.fold_iff_triple Seed (projectStep Seed g)).mp
  rw [uniformity_of_iso Seed (splitProjected Seed) _ _ (projected_cycle Seed g),
    iterateChosen_projectStep, native_iterate g input output, Functor.map_comp, ← Category.assoc, foldEq,
    iterateChosen_projectStep]

theorem triple_step
    (includeUnit : ∀ {Γ L r s}, Paper.WithUnitEta.Step Γ r s L → Seed Γ r s L)
    {B : Q} (g : ofType Seed (unitTy (τ := τ)) ⟶ B ⨿ ofType Seed (unitTy (τ := τ))) :
    iterateChosen Seed (ThreeCycle.triple g) = iterateChosen Seed g := by
  have resetId : (J).map (reset (τ := τ) (Φ := Φ)) = 𝟙 _ := unit_eta_of_include Seed includeUnit
  obtain ⟨q, hq⟩ := exists_projectStep Seed g
  let q' := reset ≫ q ≫ coprod.map (𝟙 _) reset
  have idem : (reset (τ := τ) (Φ := Φ)) ≫ reset = reset :=
    discard_comp_branchValue (.unit (Γ := [unitTy]))
  have input : reset ≫ q' = q' := by simp only [q', ← Category.assoc reset reset, idem]
  have output : q' ≫ coprod.map (𝟙 _) reset = q' := by
    simp only [q', Category.assoc, coprod.map_map, Category.id_comp, idem]
  have pr : projectStep Seed q' = g := by
    change (J).map (reset ≫ q ≫ coprod.map (𝟙 _) reset) ≫ _ = _
    rw [Functor.map_comp, Functor.map_comp, resetId, Category.id_comp, Category.assoc, ← hq]
    rw [← coprodComparison_inv_map Seed (𝟙 _) reset]
    simp [(J).map_id, resetId, projectStep]
    rfl
  rw [← pr]
  exact triple_step_of_native_reset Seed includeUnit q' input output

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.UnitThreeCycle
