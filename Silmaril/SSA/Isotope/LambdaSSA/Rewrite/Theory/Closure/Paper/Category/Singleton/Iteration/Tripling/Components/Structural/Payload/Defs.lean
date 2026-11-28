module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Tripling.Components.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Blocks.ThreeCycle.Defs

/-! # The right block of a three-phase schedule on a sum -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.ThreeCycle.Payload

open CategoryTheory CategoryTheory.Limits

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

local notation "Q" => TypeCategory Seed
local notation "Phases" A:max => (A ⨿ (A ⨿ A))

/-- Group the written three-phase schedule by tag and expose the left tag
beside the exit for right-block elimination. -/
noncomputable def groupedRows {A D B : Q} (g : A ⨿ D ⟶ B ⨿ (A ⨿ D)) :
    Phases A ⨿ Phases D ⟶ (B ⨿ Phases A) ⨿ Phases D :=
  let c := Paper.TypeCategory.ComponentTripling.phaseInterleave A D
  c.inv ≫ step g ≫ coprod.map (𝟙 B) c.hom ≫
    (coprod.associator B (Phases A) (Phases D)).inv

/-- The right row with the opposite tag and its phase exposed. -/
noncomputable def groupedRightRow {A D B : Q} (g : A ⨿ D ⟶ B ⨿ (A ⨿ D)) :
    Phases D ⟶ (B ⨿ Phases A) ⨿ Phases D :=
  coprod.inr ≫ groupedRows Seed g

/-- Forget the phase of the opposite tag on its outward port. -/
noncomputable def rightRow {A D B : Q} (g : A ⨿ D ⟶ B ⨿ (A ⨿ D)) :
    Phases D ⟶ (B ⨿ A) ⨿ Phases D :=
  groupedRightRow Seed g ≫ coprod.map (coprod.map (𝟙 B) (fold A)) (𝟙 (Phases D))

/-- The one-round right row has the same exit and exposed opposite tag. -/
noncomputable def targetRightRow {A D B : Q} (g : A ⨿ D ⟶ B ⨿ (A ⨿ D)) :
    D ⟶ (B ⨿ A) ⨿ D :=
  coprod.inr ≫ g ≫ (coprod.associator B A D).inv

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.ThreeCycle.Payload
