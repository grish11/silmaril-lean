module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Tripling.Components.Structural.Payload.Cuts.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Blocks.Alternating.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.StructuralTriplingPayloadBinaryCut

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.Extension.Singleton
open Paper.Extension.Singleton.ThreeCycle (step)
open CategoryTheory CategoryTheory.Limits

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

local notation "Q" => TypeCategory Seed
local notation "I" => iterateChosen Seed

set_option backward.isDefEq.respectTransparency false

theorem iterate_binary_cut {D B : Q} (r : D ⟶ B ⨿ D) :
    I (Alternating.step r (r ≫ coprod.desc coprod.inl r)) =
      coprod.inl ≫ (coprod.associator D D D).hom ≫ I (step r) := by
  let e := coprod.associator D D D
  let first : D ⨿ D ⟶ (B ⨿ (D ⨿ D)) ⨿ D :=
    coprod.desc (r ≫ coprod.map (𝟙 B) coprod.inr ≫ coprod.inl)
      (r ≫ coprod.map coprod.inl (𝟙 D))
  let second : D ⟶ B ⨿ (D ⨿ D) := r ≫ coprod.map (𝟙 B) coprod.inl
  let joined := coprod.desc first (second ≫ coprod.inl) ≫ (coprod.associator B (D ⨿ D) D).hom
  have coord : joined ≫ coprod.map (𝟙 B) e.hom = e.hom ≫ step r := by
    apply coprod.hom_ext
    · apply coprod.hom_ext <;> simp [joined, first, e, step, coprod.associator] <;>
        (congr 1; apply coprod.hom_ext <;> simp)
    · simp [joined, second, e, step, coprod.associator]
      congr 1
      apply coprod.hom_ext <;> simp
  have cut_eq : first ≫ coprod.desc (𝟙 (B ⨿ (D ⨿ D))) second =
      Alternating.step r (r ≫ coprod.desc coprod.inl r) := by
    apply coprod.hom_ext
    · simp [first]
    · simp [first, second, coprod.desc_comp, coprod.map_desc]
  rw [← cut_eq, iterateChosen_bypass, show coprod.desc first (second ≫ coprod.inl) ≫
      (coprod.associator B (D ⨿ D) D).hom = joined from rfl,
    uniformity_of_iso Seed e _ _ coord]

theorem binary_cut_square_iff {D B : Q} (r target : D ⟶ B ⨿ D) :
    Alternating.step r (r ≫ coprod.desc coprod.inl r) ≫ coprod.map (𝟙 B) (coprod.desc (𝟙 D) (𝟙 D)) =
      coprod.desc (𝟙 D) (𝟙 D) ≫ target ↔
    target = r ∧ r ≫ coprod.desc coprod.inl r = r := by
  constructor
  · intro eq
    have first : r = target := by
      simpa using congrArg ((coprod.inl : D ⟶ D ⨿ D) ≫ ·) eq
    have second : r ≫ coprod.desc coprod.inl r = target := by
      simpa using congrArg ((coprod.inr : D ⟶ D ⨿ D) ≫ ·) eq
    exact ⟨first.symm, second.trans first.symm⟩
  · rintro ⟨rfl, h⟩
    rw [h]
    apply coprod.hom_ext <;> simp

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.StructuralTriplingPayloadBinaryCut

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.StructuralTriplingPayloadBinaryCut

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Paper.Extension.Singleton
open Paper.WithCaseReturns.BinaryFold (JoinedStep double_step)
open Paper.Extension.Singleton.ThreeCycle (fold)
open Paper.Extension.Singleton.ThreeCycle.Payload

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

local notation "S" => JoinedStep (τ := τ) (Φ := Φ) pe
local notation "Q" => Paper.Extension.Singleton.TypeCategory S
local notation "I" => iterateChosen S

theorem phase_right_uniformity_of_binary_cut_square {A D B : Q}
    (g : A ⨿ D ⟶ B ⨿ (A ⨿ D)) (target : D ⟶ (B ⨿ A) ⨿ D)
    (square : let r := targetRightRow S g
      Alternating.step r (r ≫ coprod.desc coprod.inl r) ≫
        coprod.map (𝟙 (B ⨿ A)) (coprod.desc (𝟙 D) (𝟙 D)) =
      coprod.desc (𝟙 D) (𝟙 D) ≫ target) :
    I (rightRow S g) = fold D ≫ I (targetRightRow S g) := by
  apply (right_uniformity_iff_triple S g).2
  have h := ((binary_cut_square_iff S (targetRightRow S g) target).1 square).2
  change I (targetRightRow S g ≫ coprod.desc coprod.inl
    (targetRightRow S g ≫ coprod.desc coprod.inl (targetRightRow S g))) = I (targetRightRow S g)
  rw [h]
  exact double_step pe _

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.StructuralTriplingPayloadBinaryCut
