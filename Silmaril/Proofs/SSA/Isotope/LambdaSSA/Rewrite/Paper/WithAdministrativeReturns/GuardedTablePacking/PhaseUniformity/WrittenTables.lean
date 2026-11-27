module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Written.Defs
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.NestedRegression
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.EnvRegression

/-! # Router tables of written programs are mixed tables -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Tables

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity (Eqv Step)
open Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
open Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop
open Paper.WithAdministrativeReturns.BitFragment.Recursive (Program)
open Paper.WithCaseBind.BitQuery (signature)
open Paper.TypeCategory (ofType ofRegion iterate sumIso phaseFold classFold coprod_desc_ofRegion
  iterate_uniformity_ofBranchValue)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit)

local notation "N" => Step (τ := Ty Empty) (Φ := signature.Instr) false
local notation "π" => Paper.Extension.Singleton.projection (Step (τ := Ty Empty) (Φ := signature.Instr) false)

set_option backward.isDefEq.respectTransparency false
open _root_.Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory (seqValueBranches caseValueBranches)
open Paper.TypeCategory (ofRegion_id ofRegion_comp)
open Paper.Extension.Singleton (iterateSum iterateSum_map)
open Paper.Extension.Singleton.ValueCoproducts (exactCopair)
open Paper.Extension.Singleton.Generation (exactCopair_ofRegion)

local notation "QLit" => Paper.Extension.Singleton.ofRegion (Step (τ := Ty Empty) (Φ := signature.Instr) false)
local notation "U" => (Ty.unit : Ty Empty)
open Paper.WithAdministrativeReturns.WithGuardedTablePacking (Valid)
open Paper.WithAdministrativeReturns.BitFragment.Recursive (Code Normal)

/-! ## Every request schedule on one slot is a mixed row -/

theorem ofNormal_normal : ∀ n : Normal 2 1, (MixRow.ofNormal n).normal = n
  | .ret e s => by
    have s0 : s = 0 := Fin.eq_zero s
    subst s0
    rfl
  | .ask l s left right => by
    have s0 : s = 0 := Fin.eq_zero s
    subst s0
    rfl

theorem mixRow_program (m : MixRow) : m.program = envCode m.normal := by
  cases m <;> rfl

theorem mixRowOf_normal (p : Program) : p.normalize id = (mixRowOf p).normal :=
  (ofNormal_normal (p.normalize id)).symm

/-! ## The transfer -/

section Transfer

variable {K : Nat}

theorem row_prog_congr {p p' : Program} (e : p = p') (a : Bool → Bool → Act K) :
    QLit (routerRow_typed K p a) = QLit (routerRow_typed K p' a) := by
  subst e
  rfl

/-- A table of written programs equals the mixed table of the rows they
normalize to, with the same actions, at every entry. -/
theorem mixed_normal_table (t : Router K) (row : Fin (K + 1) → MixRow) (h : t.Normalizes row)
    (j : Fin (K + 1)) : Eqv false [State] (t.entered j) ((mixWritten row t.act).entered j) [Bit] :=
  dispatch_rows_eqv t.rows_typed (mixWritten row t.act).rows_typed
    (fun i => (normal_row K (t.prog i) (t.act i)).trans
      (row_prog_congr ((congrArg envCode (h i)).trans (mixRow_program (row i)).symm) (t.act i))) j

theorem normalizes_mixRows (t : Router K) : t.Normalizes t.mixRows := fun i => mixRowOf_normal (t.prog i)

/-- Every table of written programs is a mixed table. -/
theorem written_mixed (t : Router K) (j : Fin (K + 1)) :
    Eqv false [State] (t.entered j) ((mixWritten t.mixRows t.act).entered j) [Bit] :=
  mixed_normal_table t t.mixRows (normalizes_mixRows t) j

/-- Every entry of a table of written programs has tidy landings. -/
theorem written_slanded (t : Router K) (j : Fin (K + 1)) :
    ∃ L : Bool → SLanding, (∀ q, (L q).Tidy) ∧ SLanded (t.entered j) L := by
  obtain ⟨cyc, fuel, hc, hs⟩ := classification (mixSil t.mixRows t.act)
  obtain ⟨L, tidy, hl⟩ := mix_slanded t.mixRows t.act (cyc := cyc) (fuel := fuel) ⟨hc, hs⟩ j
  exact ⟨L, tidy, fun q => (const_congr (t.entered_typed j) ((mixWritten t.mixRows t.act).entered_typed j)
    (written_mixed t j) q).trans (hl q)⟩

end Transfer

/-- Two tables of written programs are equal at given original entries
exactly when they are valid in every supported model. -/
theorem written_complete {K K' : Nat} (t : Router K) (t' : Router K') (i : Fin (K + 1)) (i' : Fin (K' + 1)) :
    Eqv false [State] (t.entered i) (t'.entered i') [Bit] ↔
      Valid (t.entered_typed i).hasType (t'.entered_typed i').hasType := by
  obtain ⟨L, tidy, hl⟩ := written_slanded t i
  obtain ⟨L', tidy', hl'⟩ := written_slanded t' i'
  exact slanded_complete (t.entered_typed i) (t'.entered_typed i') hl hl' tidy tidy'

/-! ## Regression -/

theorem letStash_normalizes (l₁ l₂ s n f : Bool) : (letStash l₁ l₂ s n f).Normalizes (stashRow l₁ l₂ s) :=
    fun i => by
  match i with
  | 0 => cases s <;> rfl
  | 1 => rfl

/-- The written table with lets equals the mixed table of its rows. -/
theorem letStash_eqv_stash (l₁ l₂ s n f : Bool) (j : Fin 2) :
    Eqv false [State] ((letStash l₁ l₂ s n f).entered j)
      ((mixWritten (stashRow l₁ l₂ s) (stashAct n f)).entered j) [Bit] :=
  mixed_normal_table (letStash l₁ l₂ s n f) (stashRow l₁ l₂ s) (letStash_normalizes l₁ l₂ s n f) j

/-- Extensionally equivalent presentations are equal: whichever Bit the
blind request enters the silent cycle with, and whether the cycle
negates the Bit. -/
theorem letStash_eqv (l₁ l₂ s n f n' f' : Bool) :
    Eqv false [State] ((letStash l₁ l₂ s n f).entered 0) ((letStash l₁ l₂ s n' f').entered 0) [Bit] :=
  (letStash_eqv_stash l₁ l₂ s n f 0).trans
    ((stash_eqv l₁ l₂ s n f n' f').trans (letStash_eqv_stash l₁ l₂ s n' f' 0).symm)

/-- A changed blind query is distinguished: the let that binds the first
reply differs from the let that binds the entry state. -/
theorem letStash_ne_slot (l₁ l₂ n f n' f' : Bool) :
    ¬ Eqv false [State] ((letStash l₁ l₂ false n f).entered 0) ((letStash l₁ l₂ true n' f').entered 0) [Bit] :=
  fun e => stash_ne_slot l₁ l₂ n f n' f'
    ((letStash_eqv_stash l₁ l₂ false n f 0).symm.trans (e.trans (letStash_eqv_stash l₁ l₂ true n' f' 0)))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Tables
