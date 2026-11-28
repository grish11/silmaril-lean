module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Tripling.Components.Structural.Payload.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Tripling.Components.Structural.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.StructuralTriplingPayload

/-! # The local phase-discard square for arbitrary retained payload -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.ThreeCycle.Payload

open CategoryTheory CategoryTheory.Limits
open Paper.TypeCategory.ComponentTripling (phaseInterleave)

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

local notation "Q" => TypeCategory Seed
local notation "Obj" => ofType (Φ := Φ) Seed
local notation "U" => (Silmaril.unit : τ)

/-- Native braid and distribution, followed by the existing Unit-η unitors,
put the two Bit tags in separate summands with their full retained payload. -/
noncomputable def bitPayloadIso
    (includeUnit : ∀ {Γ L r s}, Paper.WithUnitEta.Step Γ r s L → Seed Γ r s L) (A : τ) :
    Obj (Silmaril.product (Silmaril.coprod U U) A) ≅ Obj A ⨿ Obj A :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.StructuralTriplingPayload.bitPayloadIso Seed includeUnit A

/-- Phase regrouping commutes with forgetting the phase of either tag. -/
theorem regroup_fold (A D : Q) :
    (phaseInterleave A D).hom ≫ coprod.map (fold A) (fold D) = fold (A ⨿ D) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.StructuralTriplingPayload.regroup_fold Seed A D

/-- Both rows commute with phase discard, keeping the exit and both tag ports. -/
theorem rows_square {A D B : Q} (g : A ⨿ D ⟶ B ⨿ (A ⨿ D)) :
    groupedRows Seed g ≫ coprod.map (coprod.map (𝟙 B) (fold A)) (fold D) =
      coprod.map (fold A) (fold D) ≫ g ≫ (coprod.associator B A D).inv :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.StructuralTriplingPayload.rows_square Seed g

/-- The local right-row iteration is the Bekić right cut with the opposite
tag's phase erased at its outward port. -/
theorem iterate_rightRow {A D B : Q} (g : A ⨿ D ⟶ B ⨿ (A ⨿ D)) :
    iterateChosen Seed (rightRow Seed g) =
      iterateChosen Seed (groupedRightRow Seed g) ≫ coprod.map (𝟙 B) (fold A) :=
  (iterateChosen_naturality Seed _ _).symm

/-- The actual right-row square after regrouping the three-phase schedule.
Its outward object retains the original exit followed by the opposite tag.
Uniformity here would compare `iterateChosen Seed (rightRow Seed g)` with
`fold D ≫ iterateChosen Seed (targetRightRow Seed g)`. -/
theorem right_square {A D B : Q} (g : A ⨿ D ⟶ B ⨿ (A ⨿ D)) :
    rightRow Seed g ≫ coprod.map (𝟙 (B ⨿ A)) (fold D) = fold D ≫ targetRightRow Seed g :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.StructuralTriplingPayload.right_square Seed g

/-- The same square for an arbitrary written round at the literal Bit × A
boundary. The outward object of the round is still B. -/
theorem bitPayload_right_square
    (includeUnit : ∀ {Γ L r s}, Paper.WithUnitEta.Step Γ r s L → Seed Γ r s L) {A : τ} {B : Q}
    (g : Obj (Silmaril.product (Silmaril.coprod U U) A) ⟶
      B ⨿ Obj (Silmaril.product (Silmaril.coprod U U) A)) :
    let split := transportStep Seed (bitPayloadIso Seed includeUnit A).symm g
    rightRow Seed split ≫ coprod.map (𝟙 (B ⨿ Obj A)) (fold (Obj A)) =
      fold (Obj A) ≫ targetRightRow Seed split :=
  right_square Seed _

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.ThreeCycle.Payload
