module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithEntryLet.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Laws.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Blocks.Alternating.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.Thms

/-! # All existing categorical EntryLet interpretations identify doubling -/

public section

universe u v u₁ u₂ v₁ v₂

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.EntryLetDenotationDoubling

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Paper.Extension.Singleton (projection projectStep iterateChosen exists_projectStep
  iterateChosen_projectStep SeedDenotes)
open Paper.Extension.Singleton.Alternating (projectStep_double)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J] (M : TypeModel τ V)
  [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]
  (shared : ∀ X Y : V, ∃ h : J.obj X ⊗ J.obj Y = J.obj (X ⊗ Y),
    Functor.StrongPremonoidal.tensorIso (J := J) X Y = eqToIso h)

local notation "S" => Paper.WithEntryLet.Step (τ := τ) (Φ := Φ)
local notation "Q" => Paper.WithEntryLet.TypeCategory (τ := τ) (Φ := Φ)
local notation "D" => Paper.WithEntryLet.denoteFunctor (Φ := Φ) J M shared

set_option backward.isDefEq.respectTransparency false in
theorem map_double {A B : Q} (g : A ⟶ B ⨿ A) :
    (D).map (iterateChosen S (g ≫ coprod.desc coprod.inl g)) =
      (D).map (iterateChosen S g) := by
  obtain ⟨A⟩ := A
  obtain ⟨B⟩ := B
  change (projection S).obj A ⟶ (projection S).obj B ⨿ (projection S).obj A at g
  obtain ⟨q, rfl⟩ := exists_projectStep S g
  let _ : HasEff Φ Bool := ⟨fun _ => true⟩
  let Fold := Paper.WithCaseReturns.BinaryFold.JoinedStep (τ := τ) (Φ := Φ) false
  have sound : SeedDenotes (Seed := Fold) J M := by
    intro Γ r s L seed hr hs
    have e := Paper.WithCaseReturns.BinaryFold.Eqv.sound false J M shared (.extra hr hs seed) hr hs
    exact ⟨_, denoteRegion_spec J M hr, e.symm ▸ denoteRegion_spec J M hs⟩
  have eq := Paper.WithCaseReturns.BinaryFold.double_step false (projectStep Fold q)
  rw [← projectStep_double Fold, iterateChosen_projectStep Fold, iterateChosen_projectStep Fold] at eq
  have lhs := (congrArg (iterateChosen S) (projectStep_double S q).symm).trans
    (iterateChosen_projectStep S (q ≫ coprod.desc coprod.inl q))
  exact (congrArg (D).map lhs).trans
    ((congrArg (Paper.Extension.Singleton.denoteFunctor J M shared sound).map eq).trans
      (congrArg (D).map (iterateChosen_projectStep S q).symm))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.EntryLetDenotationDoubling
