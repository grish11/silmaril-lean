module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Tripling.Components.Structural.Payload.Cuts.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Blocks.Alternating.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.StructuralTriplingPayloadBinaryCut

/-! # The BinaryFold premise after one phase is eliminated -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.ThreeCycle.Payload

open CategoryTheory CategoryTheory.Limits

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

local notation "Q" => TypeCategory Seed
local notation "I" => iterateChosen Seed

/-- Eliminating the last phase leaves a one-round leg and a two-round leg,
with the same short-circuit exit on both. -/
theorem iterate_binary_cut {D B : Q} (r : D ⟶ B ⨿ D) :
    I (Alternating.step r (r ≫ coprod.desc coprod.inl r)) =
      coprod.inl ≫ (coprod.associator D D D).hom ≫ I (step r) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.StructuralTriplingPayloadBinaryCut.iterate_binary_cut Seed r

/-- The ordinary binary fold after this elimination has a commuting square
exactly when the one- and two-round steps agree as arrows. -/
theorem binary_cut_square_iff {D B : Q} (r target : D ⟶ B ⨿ D) :
    Alternating.step r (r ≫ coprod.desc coprod.inl r) ≫ coprod.map (𝟙 B) (coprod.desc (𝟙 D) (𝟙 D)) =
      coprod.desc (𝟙 D) (𝟙 D) ≫ target ↔
    target = r ∧ r ≫ coprod.desc coprod.inl r = r :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.StructuralTriplingPayloadBinaryCut.binary_cut_square_iff Seed r target

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.ThreeCycle.Payload

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold

open CategoryTheory CategoryTheory.Limits
open Paper.Extension.Singleton
open Paper.Extension.Singleton.ThreeCycle (fold triple)
open Paper.Extension.Singleton.ThreeCycle.Payload

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

local notation "S" => JoinedStep (τ := τ) (Φ := Φ) pe
local notation "Q" => TypeCategory (τ := τ) (Φ := Φ) pe
local notation "I" => iterateChosen S

/-- The existing binary law proves the first Bekić comparison when the
two surviving rounds have the binary fold's actual square. -/
theorem phase_right_uniformity_of_binary_cut_square {A D B : Q}
    (g : A ⨿ D ⟶ B ⨿ (A ⨿ D)) (target : D ⟶ (B ⨿ A) ⨿ D)
    (square : let r := targetRightRow S g
      Alternating.step r (r ≫ coprod.desc coprod.inl r) ≫
        coprod.map (𝟙 (B ⨿ A)) (coprod.desc (𝟙 D) (𝟙 D)) =
      coprod.desc (𝟙 D) (𝟙 D) ≫ target) :
    I (rightRow S g) = fold D ≫ I (targetRightRow S g) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.StructuralTriplingPayloadBinaryCut.phase_right_uniformity_of_binary_cut_square pe g target square

/-- When the right-row binary square is available, the remaining obligation
is iteration of the actual left cuts, with the original outward object. -/
theorem phase_triple_iff_left_of_right_step_idempotence {A D B : Q}
    (g : A ⨿ D ⟶ B ⨿ (A ⨿ D))
    (idempotent : let r := targetRightRow S g
      r ≫ coprod.desc coprod.inl r = r) :
    I (triple g) = I g ↔ I (leftCut S g) = fold A ≫ I (targetLeftCut S g) :=
  triple_iff_left_uniformity S g (phase_right_uniformity_of_binary_cut_square pe g _
    ((binary_cut_square_iff S (targetRightRow S g) _).2 ⟨rfl, idempotent⟩))

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold
