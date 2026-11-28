module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback.Denotation.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback.Live.Defs

/-! # Denotational equality at the two separated syntax arrows -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback.Live

open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

universe u₁ u₂ v₁ v₂
variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J]
  (M : TypeModel (Ty Atom) V) [InstructionModel J M Op] [RegionTypingCoherent (Φ := Op) J M]
  (shared : ∀ U W : V, ∃ h : J.obj U ⊗ J.obj W = J.obj (U ⊗ W),
    Functor.StrongPremonoidal.tensorIso (J := J) U W = eqToIso h)
include shared

/-- The exact effectful written entry and reachable heterogeneous table
have the denotation of their packed singleton readback. -/
theorem denote_readback :
    denoteSingletonRegion J M written_typed.hasType =
      denoteSingletonRegion J M (packedReadbackRep labels entry_typed rows_typed).property.hasType :=
  denote_packed_table M J shared labels entry_typed rows_typed

/-- The corresponding equality holds at the literal constructor entry. -/
theorem denote_constructorEntry_readback :
    let he : ValueBranches [Payload] (.br 0 (.var 0) : Region Op) (List.ofFn labels ++ [Result]) :=
      .br (ℓ := 0) rfl (.var (i := 0) rfl)
    denoteSingletonRegion J M (ValueBranches.cfg labels he rows_typed).hasType =
      denoteSingletonRegion J M (packedReadbackRep labels he rows_typed).property.hasType :=
  denote_packed_table M J shared labels (.br (ℓ := 0) rfl (.var (i := 0) rfl)) rows_typed

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback.Live
