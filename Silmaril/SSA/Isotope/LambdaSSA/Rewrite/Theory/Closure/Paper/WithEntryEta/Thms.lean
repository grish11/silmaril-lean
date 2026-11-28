module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithEntryEta.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.EntryLet.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Denotation.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithEntryEta

/-! # Derivations and categorical soundness for literal CFG η -/

public section

universe u v v₁ v₂ u₁ u₂

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithEntryEta

open Silmaril Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- Literal CFG η gives a proof in the opt-in region relation. -/
theorem reentry {n : Nat} {Γ : VCtx τ} {L : LCtx τ} {entry : Region Φ}
    {blocks : Fin n → Region Φ} (R : Fin n → τ)
    (he : ValueBranches Γ entry (List.ofFn R ++ L))
    (hb : ∀ i, ValueBranches (R i :: Γ) (blocks i) (List.ofFn R ++ L)) :
    Eqv Γ (.cfg entry n blocks) (entry.lsubst (cfgEntryContinuations blocks)) L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithEntryEta.reentry R he hb

/-- Apply η before the let and reverse η after weakening the table. -/
theorem entryLet (n : Nat) : CfgEta.EntryLet (Eqv (τ := τ) (Φ := Φ)) n :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithEntryEta.entryLet n

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J]
  (M : TypeModel τ V) [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]
  (shared : ∀ X Y : V, ∃ h : J.obj X ⊗ J.obj Y = J.obj (X ⊗ Y),
    Functor.StrongPremonoidal.tensorIso (J := J) X Y = eqToIso h)
include shared

/-- The structural branch guard gives soundness of the literal η seed in
the coherent shared-tensor model. -/
theorem seedDenotes : Extension.Singleton.SeedDenotes (Seed := Step (τ := τ) (Φ := Φ)) J M :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithEntryEta.seedDenotes J M shared

/-- Every derivation in the extended region relation preserves exact typed
denotation at its whole outward interface. -/
theorem sound {Γ : VCtx τ} {r s : Region Φ} {L : LCtx τ}
    (eq : Eqv Γ r s L) (hr : HasType Γ r L) (hs : HasType Γ s L) :
    denoteRegion J M hr = denoteRegion J M hs :=
  eq.sound J M shared (seedDenotes J M shared) hr hs

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithEntryEta
