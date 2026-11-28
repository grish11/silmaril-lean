module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.EntryLet.Obstruction.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Sequencing.EntryLet.Thms

/-! # Categorical equality of the separated flat CFGs -/

public section

universe v₁ v₂ u₁ u₂

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.EntryLetReflection

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.EntryLetObstruction
open SequencingObstruction (Instruction)
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
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

theorem denoteRegion_eq
    (shared : ∀ E X : V, ∃ h : J.obj E ⊗ J.obj X = J.obj (E ⊗ X),
      Functor.StrongPremonoidal.tensorIso (J := J) E X = eqToIso h) :
    denoteRegion J M flatRequest_typed.hasType = denoteRegion J M movedRequest_typed.hasType := by
  have hp : Tm.HasType [U] request U := .op (.var rfl)
  have hd : ValueBranches [U, U] (.br 0 (.var 0) : Region Instruction) [U, U, U] :=
    .br rfl (.var rfl)
  have hb : ∀ i : Fin 2, ValueBranches [U, U] (blocks i) [U, U, U] :=
    Fin.cases (.br rfl (.var rfl)) (fun _ => .br rfl (.var rfl))
  exact denoteRegion_cfgEntryLet J M shared (fun _ : Fin 2 => U) hp hd.hasType (fun i => (hb i).hasType)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.EntryLetReflection
