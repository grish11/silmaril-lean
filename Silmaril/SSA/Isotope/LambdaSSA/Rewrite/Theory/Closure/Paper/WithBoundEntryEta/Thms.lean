module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.EntryLet.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Denotation.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta

/-! # Derivations and categorical soundness for once-bound CFG η -/

public section

universe u v v₁ v₂ u₁ u₂

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta

open Silmaril Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- The additional rule binds each entry branch argument before re-entry. -/
theorem reentry {n : Nat} {Γ : VCtx τ} {L : LCtx τ} {entry : Region Φ}
    {blocks : Fin n → Region Φ} (R : Fin n → τ)
    (he : HasType Γ entry (List.ofFn R ++ L))
    (hb : ∀ i, HasType (R i :: Γ) (blocks i) (List.ofFn R ++ L)) :
    Eqv Γ (.cfg entry n blocks) (entry.bindBranchArguments.lsubst (cfgEntryContinuations blocks)) L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.reentry R he hb

/-- The zero-row instance binds a branch argument once, at its exact type. -/
theorem bindBranch {Γ : VCtx τ} {L : LCtx τ} {i : Nat} {a : Tm Φ} {A : τ}
    (hi : At L i A) (ha : Tm.HasType Γ a A) :
    Eqv Γ (.br i a) (.let₁ a (.br i (.var 0))) L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.bindBranch hi ha

/-- Applying once-bound η in both directions moves an exact entry let
outside the CFG and weakens the table across its binder. -/
theorem entryLet {n : Nat} {Γ : VCtx τ} {L : LCtx τ} {S : τ} {a : Tm Φ} {d : Region Φ}
    {blocks : Fin n → Region Φ} (R : Fin n → τ)
    (ha : Tm.HasType Γ a S)
    (hd : HasType (S :: Γ) d (List.ofFn R ++ L))
    (hb : ∀ i, HasType (R i :: Γ) (blocks i) (List.ofFn R ++ L)) :
    Eqv Γ (.cfg (.let₁ a d) n blocks)
      (.let₁ a (.cfg d n (fun i => (blocks i).renameVars (Silmaril.DeBruijn.lift Nat.succ)))) L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.entryLet R ha hd hb

/-- The literal substitution is derivable for the particular re-entry family.
Each continuation branches on its payload once before entering a table
weakened past that payload. Local labels introduced under nested CFGs
forward their payload once as well. This includes the constructor-guarded
rule by passing the underlying exact typing of its two guards. -/
theorem literal_reentry {n : Nat} {Γ : VCtx τ} {L : LCtx τ} {entry : Region Φ}
    {blocks : Fin n → Region Φ} (R : Fin n → τ)
    (he : HasType Γ entry (List.ofFn R ++ L))
    (hb : ∀ i, HasType (R i :: Γ) (blocks i) (List.ofFn R ++ L)) :
    Eqv Γ (.cfg entry n blocks) (entry.lsubst (cfgEntryContinuations blocks)) L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.literal_reentry R he hb

/-- The constructor-guarded presentation's literal rule follows at the
same exact region interface. -/
theorem guarded_reentry {n : Nat} {Γ : VCtx τ} {L : LCtx τ} {entry : Region Φ}
    {blocks : Fin n → Region Φ} (R : Fin n → τ)
    (he : ValueBranches Γ entry (List.ofFn R ++ L))
    (hb : ∀ i, ValueBranches (R i :: Γ) (blocks i) (List.ofFn R ++ L)) :
    Eqv Γ (.cfg entry n blocks) (entry.lsubst (cfgEntryContinuations blocks)) L :=
  literal_reentry R he.hasType (fun i => (hb i).hasType)

/-- Recover the original entry-let interface with constructor-valued branches. -/
theorem guarded_entryLet (n : Nat) : CfgEta.EntryLet (Eqv (τ := τ) (Φ := Φ)) n :=
  fun R ha hd hb => entryLet R ha hd.hasType (fun i => (hb i).hasType)

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

/-- The once-bound seed preserves denotation in coherent shared-tensor models. -/
theorem seedDenotes : Extension.Singleton.SeedDenotes (Seed := Step (τ := τ) (Φ := Φ)) J M :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.seedDenotes J M shared

/-- Every derivation in the extended region relation preserves exact typed
denotation at its whole outward interface. -/
theorem sound {Γ : VCtx τ} {r s : Region Φ} {L : LCtx τ}
    (eq : Eqv Γ r s L) (hr : HasType Γ r L) (hs : HasType Γ s L) :
    denoteRegion J M hr = denoteRegion J M hs :=
  eq.sound J M shared (seedDenotes J M shared) hr hs

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta
