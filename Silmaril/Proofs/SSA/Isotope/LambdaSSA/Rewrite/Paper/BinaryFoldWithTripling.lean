module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Tripling.Components.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BinaryFoldWithTripling

open Silmaril.Isotope.LambdaSSA.Region
open Paper.WithCaseReturns.BinaryFold (JoinedStep ternaryStep ternaryFold ternaryFold_arrow
  ternaryStep_iterate_first ternaryFold_iff_triple)
open Paper.WithCaseReturns.BinaryFold.WithTripling (Step TriplingStep fromBinaryFold)
open Paper.Extension.Singleton.ThreeCycle (triple projectStep_thenOnRepeat)
open Paper.Extension.Singleton (ofRegion_eq_iff sumCofan sumCofanIsColimit projectStep
  exists_projectStep iterateChosen_projectStep)
open Silmaril.Isotope.LambdaSSA
open CategoryTheory CategoryTheory.Limits
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton
  (ofType ofRegion projection iterateChosen homRel)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.StructuralValues (inclusion)

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

set_option hygiene false in
local notation "S" => JoinedStep (τ := τ) (Φ := Φ) pe
local infixr:65 " ⊕ₜ " => Silmaril.coprod

set_option hygiene false in
local notation "T" => Step (τ := τ) (Φ := Φ) pe
set_option hygiene false in
local notation "H" => fromBinaryFold (τ := τ) (Φ := Φ) pe

set_option backward.isDefEq.respectTransparency false

theorem map_projection {A B : Paper.TypeCategory (τ := τ) Φ} (f : A ⟶ B) :
    (H).map ((projection S).map f) = (projection T).map f := by
  rfl

private theorem exists_guarded {A B : τ} (f : ofType S A ⟶ ofType S B) :
    ∃ r : Region Φ, ∃ hr : ValueBranches [A] r [B], f = ofRegion S hr := by
  obtain ⟨g, rfl⟩ := (projection S).map_surjective f
  obtain ⟨r, hr, rfl⟩ := Paper.TypeCategory.exists_ofRegion g
  exact ⟨r, hr, rfl⟩

private theorem phase_representatives {A B : τ} (g : ofType S A ⟶ ofType S B ⨿ ofType S A) :
    ∃ (r s : Region Φ) (hr : ValueBranches [A ⊕ₜ (A ⊕ₜ A)] r [B])
      (hs : ValueBranches [A ⊕ₜ (A ⊕ₜ A)] s [B]),
      ofRegion S hr = iterateChosen S (ternaryStep pe g) ∧
      ofRegion S hs = (inclusion S).map (ternaryFold pe A) ≫ iterateChosen S g := by
  obtain ⟨r, hr, left⟩ := exists_guarded pe (iterateChosen S (ternaryStep pe g))
  obtain ⟨s, hs, right⟩ := exists_guarded pe ((inclusion S).map (ternaryFold pe A) ≫ iterateChosen S g)
  exact ⟨r, s, hr, hs, left.symm, right.symm⟩

theorem ternary_uniformity {A B : τ} (g : ofType S A ⟶ ofType S B ⨿ ofType S A) :
    (H).map (iterateChosen S (ternaryStep pe g)) =
      (H).map ((inclusion S).map (ternaryFold pe A) ≫ iterateChosen S g) := by
  obtain ⟨r, s, hr, hs, left, right⟩ := phase_representatives pe g
  have seed : TriplingStep pe _ r s [B] := .uniform g hr hs left right
  have equal := (ofRegion_eq_iff T hr hs).mpr (.extra hr.hasType hs.hasType (.inr seed))
  rw [← left, ← right]
  exact equal

theorem seed_derivable_iff :
    (∀ {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}, TriplingStep pe Γ r s L →
      Paper.WithCaseReturns.BinaryFold.Eqv pe Γ r s L) ↔
    (∀ {A B : τ} (g : ofType S A ⟶ ofType S B ⨿ ofType S A),
      iterateChosen S (triple g) = iterateChosen S g) := by
  constructor
  · intro derives A B g
    apply (ternaryFold_iff_triple pe g).mp
    obtain ⟨_, _, hr, hs, left, right⟩ := phase_representatives pe g
    rw [← left, ← right]
    exact (ofRegion_eq_iff S hr hs).mpr (derives (.uniform g hr hs left right))
  · intro batches Γ L r s step
    cases step with
    | uniform g hr hs left right =>
      apply (ofRegion_eq_iff S hr hs).mp
      rw [left, right]
      exact (ternaryFold_iff_triple pe g).mpr (batches g)

private theorem map_triple {A B : τ} (g : ofType S A ⟶ ofType S B ⨿ ofType S A) :
    (H).map (iterateChosen S (triple g)) = (H).map (iterateChosen S g) := by
  let fst := (sumCofan S A (A ⊕ₜ A)).inl
  have first : fst ≫ (inclusion S).map (ternaryFold pe A) = 𝟙 (ofType S A) := by
    simp only [fst, ternaryFold_arrow]
    exact (sumCofanIsColimit S A (A ⊕ₜ A)).fac (BinaryCofan.mk _ _) ⟨WalkingPair.left⟩
  rw [← ternaryStep_iterate_first pe g, Functor.map_comp, ternary_uniformity pe g,
    ← Functor.map_comp, ← Category.assoc]
  change (H).map ((fst ≫ (inclusion S).map (ternaryFold pe A)) ≫ iterateChosen S g) = _
  rw [first, Category.id_comp]

theorem triple_step {A B : τ} (g : ofType T A ⟶ ofType T B ⨿ ofType T A) :
    iterateChosen T (triple g) = iterateChosen T g := by
  obtain ⟨f, rfl⟩ := exists_projectStep T g
  let f₃ := Paper.TypeCategory.ComponentTripling.thenOnRepeat f
    (Paper.TypeCategory.ComponentTripling.thenOnRepeat f f)
  have batch (U : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop) :
      projectStep U f₃ = triple (projectStep U f) := by
    rw [show f₃ = Paper.TypeCategory.ComponentTripling.thenOnRepeat f
      (Paper.TypeCategory.ComponentTripling.thenOnRepeat f f) from rfl,
      projectStep_thenOnRepeat, projectStep_thenOnRepeat]
  have old := map_triple pe (projectStep S f)
  rw [← batch S, iterateChosen_projectStep, iterateChosen_projectStep, map_projection, map_projection] at old
  calc
    iterateChosen T (triple (projectStep T f)) = iterateChosen T (projectStep T f₃) :=
      congrArg (iterateChosen T) (batch T).symm
    _ = (projection T).map (Paper.TypeCategory.iterate f₃) := iterateChosen_projectStep T f₃
    _ = (projection T).map (Paper.TypeCategory.iterate f) := old
    _ = iterateChosen T (projectStep T f) := (iterateChosen_projectStep T f).symm

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BinaryFoldWithTripling
