module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Blocks.ThreeCycle.PhaseProduct.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.PhaseProductThreeCycle

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.PhaseProductUniformity

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Paper.TypeCategory.PhaseProduct
open Paper.TypeCategory (rightUnitProjection rightUnitSection rightUnit_section_projection)
open Paper.Extension.Singleton

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
    (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

local notation "P" => Paper.TypeCategory (τ := τ) Φ
local notation "J" => projection Seed
local notation "I" => iterateChosen Seed

set_option backward.isDefEq.respectTransparency false

private theorem project_row {X Y B : P} (f : X ⟶ B ⨿ X) (g : Y ⟶ B ⨿ Y)
    (j k : X ⟶ Y) (row : j ≫ g = f ≫ coprod.map (𝟙 B) k) :
    (J).map j ≫ projectStep Seed g =
      projectStep Seed f ≫ coprod.map (𝟙 ((J).obj B)) ((J).map k) := by
  let c := PreservesColimitPair.iso (J)
  change (J).map j ≫ (J).map g ≫ (c B Y).inv =
    ((J).map f ≫ (c B X).inv) ≫ coprod.map (𝟙 ((J).obj B)) ((J).map k)
  rw [← (J).map_comp_assoc, row, (J).map_comp, Category.assoc, Category.assoc,
    ← (J).map_id B, coprodComparison_inv_map]

theorem phase_uniformity_iff_triple
    (includeUnit : ∀ {Γ L r s}, Paper.WithUnitEta.Step Γ r s L → Seed Γ r s L)
    {A : τ} {B : P} (f : Paper.TypeCategory.ofType A ⟶ B ⨿ Paper.TypeCategory.ofType A) :
    I (projectStep Seed (step f)) = (J).map (payload A) ≫ I (projectStep Seed f) ↔
      I (ThreeCycle.triple (projectStep Seed f)) = I (projectStep Seed f) := by
  let X := Paper.TypeCategory.ofType (Φ := Φ) A
  let W := Packet (Φ := Φ) A
  let s := split (Φ := Φ) A
  let c := PreservesColimitPair.iso (J)
  let u : (J).obj X ≅ (J).obj W := (rightUnitIsoOfEta Seed (unit_eta_of_include Seed includeUnit) ((J).obj X)).symm
  let cover := coprod.mapIso u (coprod.mapIso u u) ≪≫
    coprod.mapIso (Iso.refl ((J).obj W)) (c W W) ≪≫ c W (W ⨿ W) ≪≫ (J).mapIso s
  let j₀ : X ⟶ Packed A := rightUnitSection A ≫ coprod.inl ≫ s.hom
  let j₁ : X ⟶ Packed A := rightUnitSection A ≫ coprod.inl ≫ coprod.inr ≫ s.hom
  let j₂ : X ⟶ Packed A := rightUnitSection A ≫ coprod.inr ≫ coprod.inr ≫ s.hom
  have unitInsert : u.hom = (J).map (rightUnitSection A) := rfl
  have leg₀ : coprod.inl ≫ cover.hom = (J).map j₀ := by
    simp [cover, unitInsert, c, j₀, PreservesColimitPair.iso_hom, ← Functor.map_comp]
    rfl
  have leg₁ : coprod.inl ≫ coprod.inr ≫ cover.hom = (J).map j₁ := by
    simp [cover, unitInsert, c, j₁, PreservesColimitPair.iso_hom, ← Functor.map_comp]
    rfl
  have leg₂ : coprod.inr ≫ coprod.inr ≫ cover.hom = (J).map j₂ := by
    simp [cover, unitInsert, c, j₂, PreservesColimitPair.iso_hom, ← Functor.map_comp]
    rfl
  have row₀ := project_row Seed f (step f) j₀ j₁ (by
    simp [j₀, j₁, step, s, packetStep]
    rw [← Category.assoc (rightUnitSection A), rightUnit_section_projection, Category.id_comp])
  have row₁ := project_row Seed f (step f) j₁ j₂ (by
    simp [j₁, j₂, step, s, packetStep]
    rw [← Category.assoc (rightUnitSection A), rightUnit_section_projection, Category.id_comp])
  have row₂ := project_row Seed f (step f) j₂ j₀ (by
    simp [j₂, j₀, step, s, packetStep]
    rw [← Category.assoc (rightUnitSection A), rightUnit_section_projection, Category.id_comp])
  have cycle : ThreeCycle.step (projectStep Seed f) ≫ coprod.map (𝟙 ((J).obj B)) cover.hom =
      cover.hom ≫ projectStep Seed (step f) := by
    apply coprod.hom_ext
    · simp only [ThreeCycle.step, coprod.inl_desc_assoc, Category.assoc, coprod.map_map, Category.id_comp]
      rw [leg₁, ← Category.assoc coprod.inl cover.hom, leg₀]
      simpa only [projectStep, Category.assoc] using row₀.symm
    · apply coprod.hom_ext
      · simp only [ThreeCycle.step, coprod.inl_desc_assoc, coprod.inr_desc_assoc, Category.assoc,
          coprod.map_map, Category.id_comp]
        rw [leg₂, ← Category.assoc coprod.inl, ← Category.assoc (coprod.inl ≫ coprod.inr),
          Category.assoc coprod.inl coprod.inr cover.hom, leg₁]
        simpa only [projectStep, Category.assoc] using row₁.symm
      · simp only [ThreeCycle.step, coprod.inr_desc_assoc, Category.assoc, coprod.map_map, Category.id_comp]
        rw [leg₀, ← Category.assoc coprod.inr, ← Category.assoc (coprod.inr ≫ coprod.inr),
          Category.assoc coprod.inr coprod.inr cover.hom, leg₂]
        simpa only [projectStep, Category.assoc] using row₂.symm
  have fold : cover.hom ≫ (J).map (payload A) = ThreeCycle.fold ((J).obj X) := by
    apply coprod.hom_ext
    · rw [← Category.assoc, leg₀, ← Functor.map_comp]
      simp [j₀, s, PhaseProductThreeCycle.split_payload, rightUnit_section_projection]
      exact (J).map_id X
    · apply coprod.hom_ext
      · simp only [coprod.inr_desc, coprod.inl_desc]
        rw [← Category.assoc coprod.inr cover.hom, ← Category.assoc coprod.inl, leg₁, ← Functor.map_comp]
        simp [j₁, s, PhaseProductThreeCycle.split_payload, rightUnit_section_projection]
        exact (J).map_id X
      · simp only [coprod.inr_desc]
        rw [← Category.assoc coprod.inr cover.hom, ← Category.assoc coprod.inr, leg₂, ← Functor.map_comp]
        simp [j₂, s, PhaseProductThreeCycle.split_payload, rightUnit_section_projection]
        exact (J).map_id X
  rw [← ThreeCycle.fold_iff_triple Seed (projectStep Seed f),
    uniformity_of_iso Seed cover _ _ cycle, ← fold, Category.assoc, cancel_epi]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.PhaseProductUniformity
