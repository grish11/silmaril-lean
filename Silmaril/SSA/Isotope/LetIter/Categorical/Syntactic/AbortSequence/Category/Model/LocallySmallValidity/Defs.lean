module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Coherence.Defs

/-! # Repaired LetIter validity over locally small models -/

@[expose] public section

namespace Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.LocallyNameless (Derivation Tm)

variable {τ Φ ε : Type} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] (pe : ε)
  {n : Nat} {β : BoundCtx τ n} {a b : Tm Empty Φ n} {A : τ}

/-- Equality in all coherent shared-tensor, central-unit strong Elgot Freyd models
with pure primitive interpretations, `Type 1` objects and `Category.{0}` homs.
The signature is small and the free context is explicitly empty. -/
def RepairedLocallySmallValidity (da : Derivation Φ (Ctx.nil : Ctx Empty τ) β a A)
    (db : Derivation Φ (Ctx.nil : Ctx Empty τ) β b A) : Prop :=
  ∀ {V C : Type 1} [Category.{0} V] [Category.{0} C]
    [CartesianMonoidalCategory V] [SymmetricCategory V]
    [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
    [HasFiniteCoproducts V] [HasFiniteCoproducts C]
    [DistributiveTensor V] [DistributivePremonoidalCategory C]
    [Iteration C] [ElgotCategory C] (J : V ⥤ C)
    [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
    (M : TypeModel τ V) [InstructionModel J M Φ],
    TypingCoherent (ν := Empty) J M Φ →
    (∀ R S : V, ∃ e : J.obj R ⊗ J.obj S = J.obj (R ⊗ S),
      Functor.StrongPremonoidal.tensorIso (J := J) R S = eqToIso e) →
    (∀ f : Φ, IsPure pe f → ∃ p : M.obj (instrSrc f) ⟶ M.obj (instrTrg f),
      InstructionModel.denote (J := J) (M := M) f = J.map p) →
    denote J M da = denote J M db

end Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic
