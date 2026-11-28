module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithEntryLet.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Denotation.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Sequencing.EntryLet.Thms

public section

universe u v v₁ v₂ u₁ u₂

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithEntryLet

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.Paper.WithEntryLet
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

theorem entryLet (n : Nat) : CfgEta.EntryLet (Eqv (τ := τ) (Φ := Φ)) n := by
  intro Γ L S a d blocks R ha hd hb
  exact .extra (.cfg R (.let₁ ha hd.hasType) (fun i => (hb i).hasType))
    (.let₁ ha (.cfg R hd.hasType (fun i => (hb i).hasType.renameVars ((Ren.wk Γ S).lift (R i)))))
    (.seq R ha hd hb)

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J]
  (M : TypeModel τ V) [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]

theorem seedDenotes
    (shared : ∀ X Y : V, ∃ h : J.obj X ⊗ J.obj Y = J.obj (X ⊗ Y),
      Functor.StrongPremonoidal.tensorIso (J := J) X Y = eqToIso h) :
    Region.Paper.Extension.Singleton.SeedDenotes (Seed := Step (τ := τ) (Φ := Φ)) J M := by
  intro Γ r s L step hr hs
  cases step with
  | seq R ha hd hb =>
    have left := denoteRegion_spec J M (.cfg R (.let₁ ha hd.hasType) (fun i => (hb i).hasType))
    have right := denoteRegion_spec J M (.let₁ ha (.cfg R hd.hasType
      (fun i => (hb i).hasType.renameVars ((Ren.wk _ _).lift (R i)))))
    have eq := denoteRegion_cfgEntryLet J M shared R ha hd.hasType (fun i => (hb i).hasType)
    exact ⟨_, left, eq.symm ▸ right⟩

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithEntryLet
