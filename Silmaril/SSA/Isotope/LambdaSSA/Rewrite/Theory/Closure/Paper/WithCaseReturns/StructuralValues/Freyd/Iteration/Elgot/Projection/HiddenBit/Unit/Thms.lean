module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.StructuralValues.Freyd.Iteration.Elgot.Projection.HiddenBit.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.UnitFoldUniformity

/-! # Alternating feedback at unit -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.StructuralValues.HiddenBit

open CategoryTheory CategoryTheory.Limits
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

local notation "Seed" => Paper.WithCaseReturns.JoinedStep (τ := τ) (Φ := Φ) pe
local notation "Comp" => Paper.WithCaseReturns.TypeCategory (τ := τ) (Φ := Φ) pe
local notation "U" => ofType Seed (Silmaril.unit : τ)

/-- Unit η identifies recursive tag erasure after projection with native
constructor discard before projection. -/
theorem project_unit_row_comp_fold
    (S : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)
    (includeUnit : ∀ {Γ : VCtx τ} {r s : Region Φ} {L : LCtx τ},
      Paper.WithUnitEta.Step Γ r s L → S Γ r s L)
    {B : Paper.TypeCategory (τ := τ) Φ}
    (row : Paper.TypeCategory.ofType (Silmaril.unit : τ) ⟶
      B ⨿ Paper.TypeCategory.ofType (Silmaril.coprod (Silmaril.unit : τ) Silmaril.unit)) :
    let X := ofType S (Silmaril.unit : τ)
    let P := Extension.Singleton.projection S
    let bit := Paper.TypeCategory.ofType (Silmaril.coprod (Silmaril.unit : τ) Silmaril.unit)
    (P.map row ≫ (PreservesColimitPair.iso P B bit).inv ≫
        coprod.map (𝟙 (P.obj B)) (Extension.Singleton.sumIso S Silmaril.unit Silmaril.unit).hom) ≫
      coprod.map (𝟙 (P.obj B)) (coprod.desc (𝟙 X) (𝟙 X)) =
        projectStep S (row ≫ coprod.map (𝟙 B) (Paper.TypeCategory.discardArrow _)) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.UnitFoldUniformity.project_unit_row_comp_fold
    S includeUnit row

/-- Independently written native rows can be replayed when constructor
discard gives the same erased row. Unit η identifies the projected discard
with the fold, including when both rows have mixed recursive routing. -/
theorem unit_fold_of_native_rows
    (S : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)
    (includeUnit : ∀ {Γ : VCtx τ} {r s : Region Φ} {L : LCtx τ},
      Paper.WithUnitEta.Step Γ r s L → S Γ r s L)
    {B : Paper.TypeCategory (τ := τ) Φ}
    (left right : Paper.TypeCategory.ofType (Silmaril.unit : τ) ⟶
      B ⨿ Paper.TypeCategory.ofType (Silmaril.coprod (Silmaril.unit : τ) Silmaril.unit))
    (g : Paper.TypeCategory.ofType (Silmaril.unit : τ) ⟶ B ⨿ Paper.TypeCategory.ofType (Silmaril.unit : τ))
    (leftErase : left ≫ coprod.map (𝟙 B) (Paper.TypeCategory.discardArrow _) = g)
    (rightErase : right ≫ coprod.map (𝟙 B) (Paper.TypeCategory.discardArrow _) = g) :
    let X := ofType S (Silmaril.unit : τ)
    let P := Extension.Singleton.projection S
    let bit := Paper.TypeCategory.ofType (Silmaril.coprod (Silmaril.unit : τ) Silmaril.unit)
    let projectRow := fun a : Paper.TypeCategory.ofType (Silmaril.unit : τ) ⟶ B ⨿ bit =>
      P.map a ≫ (PreservesColimitPair.iso P B bit).inv ≫
        coprod.map (𝟙 (P.obj B)) (Extension.Singleton.sumIso S Silmaril.unit Silmaril.unit).hom
    iterateChosen S (coprod.desc (projectRow left) (projectRow right)) =
      coprod.desc (𝟙 X) (𝟙 X) ≫ iterateChosen S (projectStep S g) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.UnitFoldUniformity.unit_fold_of_native_rows
    S includeUnit left right g leftErase rightErase

/-- Unit η proves the double-step equation in any contextual quotient containing it. -/
theorem unit_alternate_power_of_seed
    (S : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)
    (includeUnit : ∀ {Γ : VCtx τ} {r s : Region Φ} {L : LCtx τ},
      Paper.WithUnitEta.Step Γ r s L → S Γ r s L)
    {B : Extension.Singleton.TypeCategory S}
    (g : ofType S (Silmaril.unit : τ) ⟶ B ⨿ ofType S (Silmaril.unit : τ)) :
    iterateChosen S (g ≫ coprod.desc coprod.inl g) = iterateChosen S g :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.UnitFoldUniformity.unit_alternate_power_of_seed
    S includeUnit g

/-- A common decision can choose to stay in the current Unit mode or switch
to the other. Folding the two modes erases the choice of successor copy. -/
theorem unit_fold_of_shared_choice
    (S : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)
    (includeUnit : ∀ {Γ : VCtx τ} {r s : Region Φ} {L : LCtx τ},
      Paper.WithUnitEta.Step Γ r s L → S Γ r s L)
    {B : Extension.Singleton.TypeCategory S}
    (g : ofType S (Silmaril.unit : τ) ⟶
      B ⨿ (ofType S (Silmaril.unit : τ) ⨿ ofType S (Silmaril.unit : τ))) :
    let X := ofType S (Silmaril.unit : τ)
    let fold := coprod.desc (𝟙 X) (𝟙 X)
    iterateChosen S (coprod.desc g (g ≫ coprod.map (𝟙 B) (coprod.desc coprod.inr coprod.inl))) =
      fold ≫ iterateChosen S (g ≫ coprod.map (𝟙 B) fold) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.UnitFoldUniformity.unit_fold_of_shared_choice
    S includeUnit g

/-- Unit η allows literal constructor discard to prove the power equation for every unit-state step. -/
theorem unit_alternate_power {B : Comp} (g : U ⟶ B ⨿ U) :
    iterateChosen Seed (g ≫ coprod.desc coprod.inl g) = iterateChosen Seed g :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.UnitFoldUniformity.unit_alternate_power pe g

local notation "Bit" => Silmaril.coprod (Silmaril.unit : τ) (Silmaril.unit : τ)
local notation "State" => ofType Seed (Silmaril.product (Silmaril.unit : τ) Bit)
local notation "p" => productFst Seed (Silmaril.unit : τ) Bit

/-- With unit as the visible state, resetting the tag is valid when the right
mode switches back on recurrence. The left mode can recur into either mode. -/
theorem unit_reset_of_right_switch {B : Comp} (f : State ⟶ B ⨿ State) (g : U ⟶ B ⨿ U)
    (square : f ≫ coprod.map (𝟙 B) p = p ≫ g)
    (switch : rightMode pe (Silmaril.unit : τ) ≫ f =
      g ≫ coprod.map (𝟙 B) (leftMode pe (Silmaril.unit : τ))) :
    iterateChosen Seed f =
      iterateChosen Seed (f ≫ coprod.map (𝟙 B) (p ≫ leftMode pe (Silmaril.unit : τ))) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.UnitFoldUniformity.unit_reset_of_right_switch
    pe f g square switch

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.StructuralValues.HiddenBit
