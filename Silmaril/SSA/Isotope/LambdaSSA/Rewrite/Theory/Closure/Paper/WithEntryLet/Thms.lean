module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithEntryLet.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Denotation.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithEntryLet

/-! # Sound entry-let equations in the opt-in Paper quotient -/

public section

universe u v v₁ v₂ u₁ u₂

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithEntryLet

open Silmaril Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- Every instance of the typed schema is derivable in the extension. -/
theorem entryLet (n : Nat) : CfgEta.EntryLet (Eqv (τ := τ) (Φ := Φ)) n :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithEntryLet.entryLet n

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J]
  (M : TypeModel τ V) [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]

variable (shared : ∀ X Y : V, ∃ h : J.obj X ⊗ J.obj Y = J.obj (X ⊗ Y),
  Functor.StrongPremonoidal.tensorIso (J := J) X Y = eqToIso h)
include shared

/-- The typed seed has a common denotation at both endpoints in the
coherent shared-tensor strong Elgot Freyd model. -/
theorem seedDenotes : Extension.Singleton.SeedDenotes (Seed := Step (τ := τ) (Φ := Φ)) J M :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithEntryLet.seedDenotes J M shared

/-- Contextual entry-let derivations preserve exact typed region denotation. -/
theorem sound {Γ : VCtx τ} {r s : Region Φ} {L : LCtx τ}
    (eq : Eqv Γ r s L) (hr : HasType Γ r L) (hs : HasType Γ s L) :
    denoteRegion J M hr = denoteRegion J M hs :=
  eq.sound J M shared (seedDenotes J M shared) hr hs

/-- The existing singleton interpretation descends through the opt-in quotient. -/
@[expose] noncomputable def denoteFunctor : TypeCategory (τ := τ) (Φ := Φ) ⥤ C :=
  Extension.Singleton.denoteFunctor J M shared (seedDenotes J M shared)

/-- The descended functor computes from the original guarded representative. -/
theorem denoteFunctor_map_ofRegion {A B : τ} {r : Region Φ} (hr : ValueBranches [A] r [B]) :
    (denoteFunctor J M shared).map (Extension.Singleton.ofRegion Step hr) =
      denoteSingletonRegion J M hr.hasType :=
  Extension.Singleton.denoteFunctor_map_ofRegion J M shared (seedDenotes J M shared) hr

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithEntryLet
