module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Tripling.Components.Structural.Payload.Cuts.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Tripling.Components.Structural.Payload.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.StructuralTriplingPayloadCuts

/-! # Exact right and left comparisons for the written three-phase loop -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.ThreeCycle.Payload

open CategoryTheory CategoryTheory.Limits

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

local notation "Q" => TypeCategory Seed
local notation "Obj" => ofType (Φ := Φ) Seed
local notation "Bit" => Silmaril.coprod (Silmaril.unit : τ) Silmaril.unit
local notation "I" => iterateChosen Seed

/-- Once the opposite tag's phase is erased on its outward port, this is
the ordinary three-cycle on the exact retained right row. -/
theorem rightRow_eq_step {A D B : Q} (g : A ⨿ D ⟶ B ⨿ (A ⨿ D)) :
    rightRow Seed g = step (targetRightRow Seed g) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.StructuralTriplingPayloadCuts.rightRow_eq_step Seed g

/-- An arbitrary retained step with the opposite tag in its outward object
is already a right row of an exact two-tag step. -/
theorem targetRightRow_of_rows {A D B : Q} (left : A ⟶ B ⨿ (A ⨿ D)) (right : D ⟶ (B ⨿ A) ⨿ D) :
    targetRightRow Seed (coprod.desc left (right ≫ (coprod.associator B A D).hom)) = right := by
  simp only [targetRightRow, coprod.inr_desc_assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The first Bekić comparison at the enlarged outward object. -/
theorem right_uniformity_iff_triple {A D B : Q} (g : A ⨿ D ⟶ B ⨿ (A ⨿ D)) :
    I (rightRow Seed g) = fold D ≫ I (targetRightRow Seed g) ↔
      I (triple (targetRightRow Seed g)) = I (targetRightRow Seed g) := by
  rw [rightRow_eq_step, fold_iff_triple]

/-- If right elimination respects phase discard, the actual left cuts
commute before iteration. -/
theorem left_square {A D B : Q} (g : A ⨿ D ⟶ B ⨿ (A ⨿ D))
    (right : I (rightRow Seed g) = fold D ≫ I (targetRightRow Seed g)) :
    leftCut Seed g ≫ coprod.map (𝟙 B) (fold A) = fold A ≫ targetLeftCut Seed g :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.StructuralTriplingPayloadCuts.left_square Seed g right

/-- With the first comparison, the original tripling equation is exactly
uniformity of the remaining left square. -/
theorem triple_iff_left_uniformity {A D B : Q} (g : A ⨿ D ⟶ B ⨿ (A ⨿ D))
    (right : I (rightRow Seed g) = fold D ≫ I (targetRightRow Seed g)) :
    I (triple g) = I g ↔ I (leftCut Seed g) = fold A ≫ I (targetLeftCut Seed g) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.StructuralTriplingPayloadCuts.triple_iff_left_uniformity Seed g right

/-- The left-cut comparison is equivalent to tripling at the literal
product boundary once the right cut respects phase discard. -/
theorem bitPayload_triple_iff_left_uniformity
    (includeUnit : ∀ {Γ L r s}, Paper.WithUnitEta.Step Γ r s L → Seed Γ r s L) {A : τ} {B : Q}
    (g : Obj (Silmaril.product Bit A) ⟶ B ⨿ Obj (Silmaril.product Bit A))
    (right : let split := transportStep Seed (bitPayloadIso Seed includeUnit A).symm g
      I (rightRow Seed split) = fold (Obj A) ≫ I (targetRightRow Seed split)) :
    let split := transportStep Seed (bitPayloadIso Seed includeUnit A).symm g
    I (triple g) = I g ↔ I (leftCut Seed split) = fold (Obj A) ≫ I (targetLeftCut Seed split) :=
  (triple_transport_iff Seed (bitPayloadIso Seed includeUnit A).symm g).symm.trans
    (triple_iff_left_uniformity Seed _ right)

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.ThreeCycle.Payload
