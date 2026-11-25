module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Thms
public import Silmaril.Semantics.Categories.Freyd.CentralUnit.Thms
public import Silmaril.SSA.Isotope.Bridge.Defs

/-! # Typing coherence for exact categorical LetIter -/

@[expose] public section

namespace Silmaril.Isotope.LetIter.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LetIter.LocallyNameless (Derivation Tm Equiv)

universe v₁ v₂ u₁ u₂ u₃ u₄ u₅

section

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  (J : V ⥤ C) [StrongElgotFreydCategory J]
  {τ : Type u₃} [TypeFormers τ] (M : TypeModel τ V)
  {ν : Type u₄} [DecidableEq ν]
  (Φ : Type u₅) [HasTy Φ τ] [InstructionModel J M Φ]

/-- Denotation depends on the exact typing judgment alone in this model. -/
def TypingCoherent : Prop :=
  ∀ {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {t : Tm ν Φ n} {A : τ}
    (d e : Derivation Φ Γ β t A), denote J M d = denote J M e

end

/-- Arbitrary endpoint derivations would be sound over small refined models if the
central-unit and primitive-purity conditions sufficed on their own. -/
def RefinedEquationSound : Prop :=
  ∀ {V C : Type 1} [Category.{0} V] [Category.{0} C]
    [CartesianMonoidalCategory V] [SymmetricCategory V]
    [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
    [HasFiniteCoproducts V] [HasFiniteCoproducts C]
    [DistributiveTensor V] [DistributivePremonoidalCategory C]
    [Iteration C] [ElgotCategory C]
    (J : V ⥤ C) [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
    {τ : Type} [TypeFormers τ] (M : TypeModel τ V)
    {Φ ε : Type} [HasTy Φ τ] [HasEff Φ ε] [InstructionModel J M Φ] (pe : ε),
    (∀ f : Φ, IsPure pe f → ∃ p : M.obj (instrSrc f) ⟶ M.obj (instrTrg f),
      InstructionModel.denote (J := J) (M := M) f = J.map p) →
    ∀ {n : Nat} {β : BoundCtx τ n} {t s : Tm Empty Φ n} {A : τ}
      (d : Derivation Φ (Ctx.nil : Ctx Empty τ) β t A) (e : Derivation Φ .nil β s A),
      Equiv pe .nil β t s A → denote J M d = denote J M e

end Silmaril.Isotope.LetIter.Semantics.Categorical
