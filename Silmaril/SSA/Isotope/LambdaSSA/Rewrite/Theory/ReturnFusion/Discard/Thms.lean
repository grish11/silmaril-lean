module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.ReturnFusion.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.Direct.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ReturnDiscard

/-! # Denotation of a lowered pure return followed by discard -/

public section

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical

open Silmaril Silmaril.Isotope.LambdaSSA
open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory (returnRegion)

universe u v w u₁ v₁ u₂ v₂
variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  {τ : Type u} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type v} [HasTy Φ τ] [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]
  {ε : Type w} [HasEff Φ ε] {pe : ε}

/-- Evaluating a lowered pure return and discarding it agrees in denotation
with immediately returning unit, when marked primitives have value interpretations. -/
theorem denote_pure_return_discard [FreydCategory.CentralUnit J]
    (shared : ∀ E X : V, ∃ h : J.obj E ⊗ J.obj X = J.obj (E ⊗ X),
      Functor.StrongPremonoidal.tensorIso (J := J) E X = eqToIso h)
    (hInstr : ∀ f : Φ, IsPure pe f → ∃ p : M.obj (instrSrc f) ⟶ M.obj (instrTrg f),
      InstructionModel.denote (J := J) (M := M) f = J.map p)
    {X A : τ} {a : Tm Φ} (ha : Tm.HasType [X] a A) (hp : Tm.Pure pe a)
    (hd : Region.HasType [X] (Region.compLSubst (fun _ => returnRegion a)
      (fun _ => .br 0 (.unit : Tm Φ)) 0) [(Silmaril.unit : τ)]) :
    denoteRegion J M hd =
      denoteRegion J M (.br (Φ := Φ) (ℓ := 0) (L := [(Silmaril.unit : τ)]) (Γ := [X]) rfl .unit) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ReturnDiscard.denote_pure_return_discard J M shared hInstr ha hp hd

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical
