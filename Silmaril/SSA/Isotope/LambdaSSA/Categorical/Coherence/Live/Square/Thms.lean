module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.Live.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.LiveCoherence

/-! # Compare actual dispatchers on a pure state map -/

public section

universe u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open CartesianMonoidalCategory (snd)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (caseWithContext contextualLoop)

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]

/-- A pure state square and the corresponding entry routing preserve the
contextual dispatcher. The pure uniformity field of the existing strong
Elgot Freyd interface applies to the map that retains the environment. -/
theorem cfgDispatch_of_state_square {E A B D : V} (h : A ⟶ D)
    (entry : J.obj E ⟶ J.obj (B ⨿ A))
    (small : J.obj (E ⊗ A) ⟶ J.obj (B ⨿ A))
    (large : J.obj (E ⊗ D) ⟶ J.obj (B ⨿ D))
    (comm : small ≫ J.map (coprod.map (𝟙 B) h) = J.map (E ◁ h) ≫ large) :
    caseWithContext J entry (J.map (snd E B)) (contextualLoop J small) =
      caseWithContext J (entry ≫ J.map (coprod.map (𝟙 B) h)) (J.map (snd E B))
        (contextualLoop J large) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.LiveCoherence.dispatch_square J h entry small large comm

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical
