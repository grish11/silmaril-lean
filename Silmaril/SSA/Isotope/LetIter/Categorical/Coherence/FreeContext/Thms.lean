module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Coherence.Defs
import Silmaril.Proofs.SSA.Isotope.LetIter.Categorical.Coherence.FreeContext

/-! # Typing coherence with anonymous free slots -/

public section

universe u v u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LetIter.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LetIter.LocallyNameless (Derivation Tm)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ]

/-- Coherence on the empty free context implies coherence in every context
whose slots have no names. The finite bound context is arbitrary. -/
theorem typingCoherent_empty_of_nil
    (h : ∀ {n : Nat} {β : BoundCtx τ n} {t : Tm Empty Φ n} {A : τ}
      (d e : Derivation Φ (Ctx.nil : Ctx Empty τ) β t A), denote J M d = denote J M e) :
    TypingCoherent (ν := Empty) J M Φ :=
  TypingCoherenceProofs.typingCoherent_empty_of_nil J M h

end Silmaril.Isotope.LetIter.Semantics.Categorical
