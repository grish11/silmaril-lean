module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Tripling.Components.Structural.Payload.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Blocks.ThreeCycle.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Tensor.Premonoidal.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.RetainedCase.Distributor.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.StructuralTriplingPayload

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.Extension.Singleton
open Paper.TypeCategory.ComponentTripling (phaseInterleave phaseInterleave_hom)
open Paper.Extension.Singleton.ThreeCycle (fold step square)
open Paper.Extension.Singleton.ThreeCycle.Payload
open CategoryTheory CategoryTheory.Limits

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

local notation "Q" => TypeCategory Seed
local notation "Obj" => ofType (Φ := Φ) Seed
local notation "U" => (Silmaril.unit : τ)
local notation "Phases" A:max => (A ⨿ (A ⨿ A))

set_option backward.isDefEq.respectTransparency false

noncomputable def bitPayloadIso
    (includeUnit : ∀ {Γ L r s}, Paper.WithUnitEta.Step Γ r s L → Seed Γ r s L) (A : τ) :
    Obj (Silmaril.product (Silmaril.coprod U U) A) ≅ Obj A ⨿ Obj A :=
  braidIso Seed (Obj (Silmaril.coprod U U)) (Obj A) ≪≫
    ((projection Seed).mapIso (Paper.RetainedCase.distributorIso A U U)) ≪≫
    sumIso Seed (Silmaril.product A U) (Silmaril.product A U) ≪≫
    coprod.mapIso (rightUnitIsoOfEta Seed (unit_eta_of_include Seed includeUnit) (Obj A))
      (rightUnitIsoOfEta Seed (unit_eta_of_include Seed includeUnit) (Obj A))

theorem regroup_fold (A D : Q) :
    (phaseInterleave A D).hom ≫ coprod.map (fold A) (fold D) = fold (A ⨿ D) := by
  apply coprod.hom_ext
  · apply coprod.hom_ext <;> simp [phaseInterleave_hom]
  · apply coprod.hom_ext <;> (apply coprod.hom_ext <;> simp [phaseInterleave_hom])

private theorem group_square {A D B : Q} (g : A ⨿ D ⟶ B ⨿ (A ⨿ D)) :
    (phaseInterleave A D).inv ≫ step g ≫
      coprod.map (𝟙 B) (phaseInterleave A D).hom ≫ coprod.map (𝟙 B) (coprod.map (fold A) (fold D)) =
      coprod.map (fold A) (fold D) ≫ g := by
  rw [coprod.map_map, Category.id_comp, regroup_fold, square Seed g,
    ← regroup_fold Seed A D, Category.assoc, Iso.inv_hom_id_assoc]

theorem rows_square {A D B : Q} (g : A ⨿ D ⟶ B ⨿ (A ⨿ D)) :
    groupedRows Seed g ≫ coprod.map (coprod.map (𝟙 B) (fold A)) (fold D) =
      coprod.map (fold A) (fold D) ≫ g ≫ (coprod.associator B A D).inv := by
  have ports : (coprod.associator B (Phases A) (Phases D)).inv ≫
      coprod.map (coprod.map (𝟙 B) (fold A)) (fold D) =
      coprod.map (𝟙 B) (coprod.map (fold A) (fold D)) ≫ (coprod.associator B A D).inv := by
    apply coprod.hom_ext
    · simp [coprod.associator]
    · apply coprod.hom_ext <;> simp [coprod.associator]
  simp only [groupedRows, Category.assoc]
  rw [ports, ← Category.assoc (coprod.map (𝟙 B) (phaseInterleave A D).hom),
    ← Category.assoc (step g), ← Category.assoc (phaseInterleave A D).inv, group_square, Category.assoc]

theorem right_square {A D B : Q} (g : A ⨿ D ⟶ B ⨿ (A ⨿ D)) :
    rightRow Seed g ≫ coprod.map (𝟙 (B ⨿ A)) (fold D) = fold D ≫ targetRightRow Seed g := by
  simpa only [rightRow, groupedRightRow, targetRightRow, Category.assoc, coprod.map_map,
    Category.comp_id, Category.id_comp, coprod.inr_map_assoc] using
    congrArg ((coprod.inr : Phases D ⟶ Phases A ⨿ Phases D) ≫ ·) (rows_square Seed g)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.StructuralTriplingPayload
