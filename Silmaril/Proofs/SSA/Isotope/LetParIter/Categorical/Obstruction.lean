module

public import Silmaril.Proofs.SSA.Isotope.LetParIter.Categorical.Tuples
public import Silmaril.SSA.Isotope.LetIter.Counterexample.Thms

public section

namespace Silmaril.Isotope.LetParIter.Categorical

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

set_option backward.isDefEq.respectTransparency false in
theorem not_all_models_extend_proof :
    ¬ (∀ {V C : Type 1} [Category.{0} V] [Category.{0} C]
      [CartesianMonoidalCategory V] [SymmetricCategory V]
      [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
      [HasFiniteCoproducts V] [HasFiniteCoproducts C]
      [DistributiveTensor V] [DistributivePremonoidalCategory C]
      [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J],
      ∃ order : ∀ X Y : C, Preorder (X ⟶ Y),
        letI := order
        Nonempty (FreydCategory.OrderedParallel J)) := by
  intro all
  apply LetIter.Semantics.Categorical.closedLetEtaUnsound
  intro V C _ _ _ _ _ _ _ _ _ _ _ _ J _ τ _ M Φ _ _ t A d
  obtain ⟨order, hP⟩ := all J
  let _ := order
  obtain ⟨P⟩ := hP
  dsimp only
  simp only [LetIter.Semantics.Categorical.denote,
    LetIter.ProofRelevant.Semantics.Categorical.bind, ← J.map_comp,
    envSnoc_zero, extend_snd_proof J P]

end Silmaril.Isotope.LetParIter.Categorical
