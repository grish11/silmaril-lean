module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback.Denotation.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Denotation.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Singleton.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithAdministrativeReturns.WithGuardedTablePacking (Pack)
open Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback
  (denote_packed_table)
open Paper.Extension.Singleton (SeedDenotes)
open Semantics.Categorical
open Semantics.Categorical.SingletonDispatcher (payload_labelInject)
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

universe u v u₁ u₂ v₁ v₂
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J] (M : TypeModel τ V)
  [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]
  (shared : ∀ E X : V, ∃ h : J.obj E ⊗ J.obj X = J.obj (E ⊗ X),
    Functor.StrongPremonoidal.tensorIso (J := J) E X = eqToIso h)

set_option backward.isDefEq.respectTransparency false in
include shared in
/-- The singleton comparison of the captured table determines the full region arrows:
the input unitor and the singleton exit payload are invertible. -/
theorem pack_denotes : SeedDenotes (Seed := Pack (τ := τ) (Φ := Φ)) J M := by
  intro Γ r s L seed hr hs
  cases seed with
  | @table n R X D e blocks he hb =>
    have eq := denote_packed_table M J shared R he hb
    have source : J.map (λ_ (M.obj X)).hom ≫ J.map (λ_ (M.obj X)).inv = 𝟙 _ := by
      rw [← J.map_comp, Iso.hom_inv_id, J.map_id]
    have payload : J.map (singletonLabelPayload M D) ≫ J.map (labelInject M 0 (L := [D]) rfl) = 𝟙 _ := by
      rw [← J.map_comp, payload_labelInject, J.map_id]
    change denoteSingletonRegion J M hr = denoteSingletonRegion J M hs at eq
    have closed := congrArg (fun f => J.map (λ_ (M.obj X)).hom ≫ f ≫
      J.map (labelInject M 0 (L := [D]) rfl)) eq
    simp only [denoteSingletonRegion, Category.assoc, reassoc_of% source, payload, Category.comp_id] at closed
    exact ⟨_, denoteRegion_spec J M hr, closed.symm ▸ denoteRegion_spec J M hs⟩

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking
