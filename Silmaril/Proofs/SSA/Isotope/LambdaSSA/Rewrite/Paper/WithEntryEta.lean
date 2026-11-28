module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithEntryEta.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.EntryLet.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Denotation.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Family.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Eta.Thms

public section

universe u v v₁ v₂ u₁ u₂

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithEntryEta

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.Paper.WithEntryEta
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

private theorem reentryFamily {n : Nat} {Γ : VCtx τ} {L : LCtx τ} {blocks : Fin n → Region Φ}
    (R : Fin n → τ) (hb : ∀ i, ValueBranches (R i :: Γ) (blocks i) (List.ofFn R ++ L)) :
    LSubst.ValueFamily Γ (List.ofFn R ++ L) L (cfgEntryContinuations blocks) :=
  fun _ A hi => .cfg R (.br hi (.var rfl))
    (fun i => (hb i).renameVars ((Ren.wk Γ A).lift (R i)))

theorem reentry {n : Nat} {Γ : VCtx τ} {L : LCtx τ} {entry : Region Φ}
    {blocks : Fin n → Region Φ} (R : Fin n → τ)
    (he : ValueBranches Γ entry (List.ofFn R ++ L))
    (hb : ∀ i, ValueBranches (R i :: Γ) (blocks i) (List.ofFn R ++ L)) :
    Eqv Γ (.cfg entry n blocks) (entry.lsubst (cfgEntryContinuations blocks)) L :=
  .extra (.cfg R he.hasType (fun i => (hb i).hasType))
    (he.lsubst (reentryFamily R hb)).hasType (.reentry R he hb)

theorem entryLet (n : Nat) : CfgEta.EntryLet (Eqv (τ := τ) (Φ := Φ)) n := by
  intro Γ L S a d blocks R ha hd hb
  have before := reentry R (.let₁ ha hd) hb
  change Eqv Γ (.cfg (.let₁ a d) n blocks)
    (.let₁ a (d.lsubst (liftLSubstVars (cfgEntryContinuations blocks)))) L at before
  rw [lift_cfgEntryContinuations] at before
  exact before.trans (.let₁ ha (reentry R hd
    (fun i => (hb i).renameVars ((Ren.wk Γ S).lift (R i)))).symm)

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
  | reentry R he hb =>
    have left := denoteRegion_spec J M (.cfg R he.hasType (fun i => (hb i).hasType))
    have eq := denoteRegion_cfgEta_sharedTensor J M shared R he.hasType
      (fun i => (hb i).hasType) (PureBranches.of_valueBranches J M he) hs
    exact ⟨_, left, eq.symm ▸ denoteRegion_spec J M hs⟩

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithEntryEta
