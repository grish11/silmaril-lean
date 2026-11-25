module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Coherence.Defs

/-! # Categorical validity for the abort-extended LetIter theory -/

@[expose] public section

universe u

namespace Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.LocallyNameless (Derivation Tm)

variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε]
variable (pe : ε)

/-- Equality at empty free context in all coherent central-unit models with shared tensors
and pure primitive interpretations. Value and computation objects and homs lie in the
universe of the signature. -/
def RepairedCategoricalValidity {n : Nat} {β : BoundCtx τ n}
    {a b : Tm Empty Φ n} {A : τ}
    (da : Derivation Φ (Ctx.nil : Ctx Empty τ) β a A)
    (db : Derivation Φ (Ctx.nil : Ctx Empty τ) β b A) : Prop :=
  ∀ {V C : Type u} [Category.{u} V] [Category.{u} C]
    [CartesianMonoidalCategory V] [SymmetricCategory V]
    [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
    [HasFiniteCoproducts V] [HasFiniteCoproducts C]
    [DistributiveTensor V] [DistributivePremonoidalCategory C]
    [Iteration C] [ElgotCategory C] (J : V ⥤ C)
    [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
    (model : TypeModel τ V) [InstructionModel J model Φ],
    TypingCoherent (ν := Empty) J model Φ →
    (∀ R S : V, ∃ e : J.obj R ⊗ J.obj S = J.obj (R ⊗ S),
      Functor.StrongPremonoidal.tensorIso (J := J) R S = eqToIso e) →
    (∀ f : Φ, IsPure pe f → ∃ p : model.obj (instrSrc f) ⟶ model.obj (instrTrg f),
      InstructionModel.denote (J := J) (M := model) f = J.map p) →
    denote J model da = denote J model db

end Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic
