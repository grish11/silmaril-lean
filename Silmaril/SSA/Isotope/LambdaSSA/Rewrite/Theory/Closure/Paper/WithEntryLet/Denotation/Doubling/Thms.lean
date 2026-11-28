module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithEntryLet.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.EntryLetDenotationDoubling

/-! # The categorical doubling boundary of the EntryLet quotient -/

public section

universe u v u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithEntryLet

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

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

/-- Every coherent shared-tensor strong Elgot Freyd interpretation of the
EntryLet quotient identifies the two iterations on any quotient step. -/
theorem denoteFunctor_map_double {A B : Q} (g : A ⟶ B ⨿ A) :
    (D).map (Paper.Extension.Singleton.iterateChosen S (g ≫ coprod.desc coprod.inl g)) =
      (D).map (Paper.Extension.Singleton.iterateChosen S g) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.EntryLetDenotationDoubling.map_double J M shared g

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithEntryLet
