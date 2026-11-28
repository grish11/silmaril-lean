module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Rounds.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.RoundsIteration
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.PhaseIteration

/-! # Unrolling holds in every Elgot Freyd category -/

public section

universe v₁ v₂ u₁ u₂

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits

section Phases

universe v u

variable {D : Type u} [Category.{v} D] [HasBinaryCoproducts D] (S : PhaseSystem D)
  {Y : D} (h : S.obj 0 ⟶ Y ⨿ S.obj 0)

/-- In a phase system the loop on `n + 1` rounds enters a cycle of `n + 1`
phases, and the fold is a simulation of that cycle onto one round. This
uses no uniformity along the fold. -/
theorem PhaseSystem.exists_cycle (n : Nat) :
    ∃ (start : S.obj 0 ⟶ S.obj n) (cycle : S.obj n ⟶ Y ⨿ S.obj n),
      start ≫ S.fold n = 𝟙 _ ∧
      cycle ≫ coprod.map (𝟙 Y) (S.fold n) = S.fold n ≫ h ∧
      S.iter (roundsStep h n) = start ≫ S.iter cycle :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.PhaseIteration.exists_cycle S h n

/-- The one further premise: uniformity along the fold of `n + 1` phases
onto `h`. With it the loop on `n + 1` rounds is the loop on one round. -/
theorem PhaseSystem.iter_roundsStep_of_fold (n : Nat)
    (fold : ∀ c : S.obj n ⟶ Y ⨿ S.obj n,
      c ≫ coprod.map (𝟙 Y) (S.fold n) = S.fold n ≫ h → S.iter c = S.fold n ≫ S.iter h) :
    S.iter (roundsStep h n) = S.iter h :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.PhaseIteration.iter_roundsStep_of_fold S h n fold

end Phases

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  (J : V ⥤ C) [ElgotFreydCategory J]

/-- The loop on any number of rounds of a step whose state is a pure
object is the loop on one round. The step and its exit object are
arbitrary. This is the phase system of `J` at `X`: its injections and
its fold are pure, so all three uniformities are pure uniformity. It uses
preservation of binary coproducts by `J`. -/
theorem iterate_roundsStep {X : V} {Y : C} (h : J.obj X ⟶ Y ⨿ J.obj X) (n : Nat) :
    iterate (roundsStep h n) = iterate h :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.RoundsIteration.iterate_roundsStep J h n

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical
