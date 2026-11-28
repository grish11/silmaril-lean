module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.Joined.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseAndUnaryReturns.Thms

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithConstructorSequencing.Joined

open CategoryTheory CategoryTheory.Limits
open Semantics.Categorical
open LetIter.Semantics.Categorical (TypeModel InstructionModel)
open scoped MonoidalCategory

universe u v w u₁ u₂ v₁ v₂

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] {pe : ε}
  {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J] (M : TypeModel τ V) [InstructionModel J M Φ]
  [RegionTypingCoherent (Φ := Φ) J M]

theorem sound_proof (shared : ∀ X Y : V, ∃ h : J.obj X ⊗ J.obj Y = J.obj (X ⊗ Y),
    Functor.StrongPremonoidal.tensorIso (J := J) X Y = eqToIso h)
    {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (h : Eqv pe Γ r s L) (hr : HasType Γ r L) (hs : HasType Γ s L) :
    denoteRegion J M hr = denoteRegion J M hs := by
  apply Extension.Eqv.sound J M shared _ h hr hs
  intro _ _ _ _ step tr ts
  have eq := step.elim
    (fun e => WithCaseAndUnaryReturns.joined_eqv_sound pe J M shared (.extra tr ts e) tr ts)
    (fun e => e.sound J M tr ts)
  exact ⟨_, denoteRegion_spec J M tr, eq.symm ▸ denoteRegion_spec J M ts⟩

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithConstructorSequencing.Joined
