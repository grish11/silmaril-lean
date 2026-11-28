module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.RetainedCase.Distributor.Chosen.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Tensor.Unit.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Blocks.ThreeCycle.Unit.Thms

/-! # Cycling a phase while preserving a separate payload type -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory.PhaseProduct

open Silmaril CategoryTheory CategoryTheory.Limits
open CfgEta.TypeCategory (productFstBranches)
open Paper.RetainedCase.Chosen (paperChosenDistributor)

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

local notation "P" => TypeCategory (τ := τ) Φ
local notation "T" => ofType (Φ := Φ)
local infixr:70 " ×ₜ " => Silmaril.product
local infixr:65 " ⊕ₜ " => Silmaril.coprod
local notation "U" => (Silmaril.unit : τ)

abbrev Phase : τ := U ⊕ₜ (U ⊕ₜ U)
abbrev Packed (A : τ) : P := T (A ×ₜ Phase)
abbrev Packet (A : τ) : P := T (A ×ₜ U)

/-- Forget the phase by the literal guarded first projection. -/
abbrev payload (A : τ) : Packed (Φ := Φ) A ⟶ T A :=
  ofRegion (productFstBranches A Phase)

/-- Distribute the product into three copies of the packet type. -/
noncomputable def splitPair (A X Y : τ) :
    T (A ×ₜ X) ⨿ T (A ×ₜ Y) ≅ T (A ×ₜ (X ⊕ₜ Y)) :=
  paperChosenDistributor A X Y ≪≫ (whiskerLeftFunctor (T A)).mapIso (sumIso X Y).symm

/-- In native Paper the distributed packets have a Unit factor. -/
noncomputable def split (A : τ) :
    Packet (Φ := Φ) A ⨿ (Packet (Φ := Φ) A ⨿ Packet (Φ := Φ) A) ≅ Packed (Φ := Φ) A :=
  coprod.mapIso (Iso.refl _) (splitPair A U U) ≪≫ splitPair A U (U ⊕ₜ U)

/-- Run the payload step, keeping its exit and inserting literal Unit only
on the recursive result. -/
noncomputable def packetStep {A : τ} {B : P} (f : T A ⟶ B ⨿ T A) :
    Packet A ⟶ B ⨿ Packet A :=
  rightUnitProjection A ≫ f ≫ coprod.map (𝟙 B) (rightUnitSection A)

/-- The transported three-cycle changes phase just on recurrence. -/
noncomputable def step {A : τ} {B : P} (f : T A ⟶ B ⨿ T A) : Packed A ⟶ B ⨿ Packed A :=
  let s := (split (Φ := Φ) A)
  let g := packetStep f
  s.inv ≫ coprod.desc
    (g ≫ coprod.map (𝟙 B) (coprod.inl ≫ coprod.inr ≫ s.hom))
    (coprod.desc (g ≫ coprod.map (𝟙 B) (coprod.inr ≫ coprod.inr ≫ s.hom))
      (g ≫ coprod.map (𝟙 B) (coprod.inl ≫ s.hom)))

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory.PhaseProduct
