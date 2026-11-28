module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.Live.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.LiveCoherence

/-! # Compare contextual dispatchers using a common factored transition -/

public section

universe u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open CartesianMonoidalCategory (snd)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (caseWithContext contextualLoop)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.LiveCoherence

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : V ⥤ C)

variable [Iteration C] [ElgotCategory C] [StrongElgotFreydCategory J]

/-- Factor two contextual feedback bodies through the same transition. The
outward projection keeps its exact type, and rolling moves only the state map. -/
theorem contextualLoop_of_state_factorization (roll : IterationRolling C) {E A B D : V} (h : A ⟶ D)
    (middle : J.obj (E ⊗ D) ⟶ J.obj (B ⨿ A)) :
    contextualLoop J (J.map (E ◁ h) ≫ middle) =
      J.map (E ◁ h) ≫ contextualLoop J (middle ≫ J.map (coprod.map (𝟙 B) h)) :=
  loop_factor J roll h middle

/-- If entry produces a state through the same value map, the two actual
contextual dispatchers agree. The map also acts on every repeat. -/
theorem cfgDispatch_of_state_factorization (roll : IterationRolling C) {E A B D : V} (h : A ⟶ D)
    (entry : J.obj E ⟶ J.obj (B ⨿ A)) (middle : J.obj (E ⊗ D) ⟶ J.obj (B ⨿ A)) :
    caseWithContext J entry (J.map (snd E B)) (contextualLoop J (J.map (E ◁ h) ≫ middle)) =
      caseWithContext J (entry ≫ J.map (coprod.map (𝟙 B) h)) (J.map (snd E B))
        (contextualLoop J (middle ≫ J.map (coprod.map (𝟙 B) h))) :=
  dispatch_factor J roll h entry middle

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical
