module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.EntryLet.Obstruction.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Denotation.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Sequencing.EntryLet.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.EntryLetReflection

/-! # Standard Paper equations and their categorical interpretation -/

public section

universe v₁ v₂ u₁ u₂

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.EntryLetObstruction

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open SequencingObstruction (Instruction)
open Semantics.Categorical (RegionTypingCoherent denoteRegion denoteSingletonRegion)
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J]
  (M : TypeModel (Ty Empty) V) [InstructionModel J M Instruction]
  [RegionTypingCoherent (Φ := Instruction) J M]

variable (shared : ∀ E X : V, ∃ h : J.obj E ⊗ J.obj X = J.obj (E ⊗ X),
  Functor.StrongPremonoidal.tensorIso (J := J) E X = eqToIso h)
include shared

/-- The exact two-transfer witness has the same region denotation in every
coherent shared-tensor model, for every interpretation of its request. -/
theorem flatRequest_denoteRegion_eq :
    denoteRegion J M flatRequest_typed.hasType = denoteRegion J M movedRequest_typed.hasType :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.EntryLetReflection.denoteRegion_eq J M shared

/-- The public singleton interpretation assigns equal arrows to the two
distinct standard Paper classes. -/
theorem flatRequest_denoteArrow_eq :
    TypeCategory.denoteArrow J M (TypeCategory.ofRegion flatRequest_typed) =
      TypeCategory.denoteArrow J M (TypeCategory.ofRegion movedRequest_typed) := by
  rw [TypeCategory.denoteArrow_ofRegion J M shared, TypeCategory.denoteArrow_ofRegion J M shared]
  unfold denoteSingletonRegion
  rw [flatRequest_denoteRegion_eq J M shared]

/-- The same pair witnesses failure of reflection in each model of the
stated class, so equality in the whole class does not imply Paper equality. -/
theorem denoteArrow_not_injective :
    ¬ Function.Injective (fun f : TypeCategory.ofType (Φ := Instruction) U ⟶ TypeCategory.ofType U =>
      TypeCategory.denoteArrow J M f) :=
  fun h => flatRequest_arrow_ne_moved (h (flatRequest_denoteArrow_eq J M shared))

end Silmaril.Isotope.LambdaSSA.Region.Paper.EntryLetObstruction
