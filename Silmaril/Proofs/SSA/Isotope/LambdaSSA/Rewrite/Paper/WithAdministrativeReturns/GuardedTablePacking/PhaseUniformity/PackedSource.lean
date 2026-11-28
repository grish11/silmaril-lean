module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Packed.Defs
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.WrittenTables
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.ValidSeq

/-! # Packed loops at their packed state, and source loops that factor through them -/

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

section Packed

variable {K : Nat}

/-- A packed loop is the dispatcher of its entered loops, in default Paper. -/
theorem loop_as_dispatch {rows : Fin (K + 1) → Region signature.Instr}
    (h : ∀ i, ValueBranches [State] (rows i) [Silmaril.coprod Bit (States K)]) :
    ofRegion (dispatchLoop_typed h) = ofRegion (dispatch_typed K fun i => dispatchEntered_typed h i) := by
  apply inj_ext K
  intro j
  rw [inj_dispatch K (fun i => dispatchEntered_typed h i) j]
  exact (dispatchEntered_arrow h j).symm

/-- Two packed loops are equal exactly when they are equal at every
original entry. -/
theorem loop_eqv_iff_entries (t t' : Router K) :
    Eqv false [States K] t.loop t'.loop [Bit] ↔
      ∀ i, Eqv false [State] (t.entered i) (t'.entered i) [Bit] := by
  constructor
  · intro e i
    apply (Paper.Extension.Singleton.ofRegion_eq_iff N (t.entered_typed i) (t'.entered_typed i)).1
    exact (q_comp (entry_typed K i) t.loop_typed).trans
      ((congrArg (QLit (entry_typed K i) ≫ ·)
        ((Paper.Extension.Singleton.ofRegion_eq_iff N t.loop_typed t'.loop_typed).2 e)).trans
        (q_comp (entry_typed K i) t'.loop_typed).symm)
  · intro e
    apply (Paper.Extension.Singleton.ofRegion_eq_iff N t.loop_typed t'.loop_typed).1
    exact (congrArg (π).map (loop_as_dispatch t.rows_typed)).trans
      ((q_dispatch_congr K (fun i => dispatchEntered_typed t.rows_typed i)
        (fun i => dispatchEntered_typed t'.rows_typed i)
        (fun i => (Paper.Extension.Singleton.ofRegion_eq_iff N (t.entered_typed i) (t'.entered_typed i)).2
          (e i))).trans (congrArg (π).map (loop_as_dispatch t'.rows_typed)).symm)

/-- Two packed loops are equal on their packed state exactly when they
are valid in every supported model. -/
theorem loop_complete (t t' : Router K) :
    Eqv false [States K] t.loop t'.loop [Bit] ↔ Valid t.loop_typed.hasType t'.loop_typed.hasType :=
  ⟨fun e => Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.valid_of_eqv false e _ _,
    fun v => (loop_eqv_iff_entries t t').2 fun i =>
      (written_complete t t' i i).2 (Valid.seq (entry_typed K i) t.loop_typed t'.loop_typed v)⟩

/-! ## Source loops that factor through a packed loop -/

variable {S : Ty Empty} {enc dec src src' : Region signature.Instr}

/-- A source loop on any state type that factors through a packed loop,
along a decoding with a section, is complete: two such loops with the
same encoding are equal exactly when they are valid in every supported
model. -/
theorem factored_complete (he : ValueBranches [S] enc [States K]) (hd : ValueBranches [States K] dec [S])
    (hs : ValueBranches [S] src [Bit]) (hs' : ValueBranches [S] src' [Bit]) (ret : Retracts S enc dec)
    (t t' : Router K) (hf : Factors dec src t) (hf' : Factors dec src' t') :
    Eqv false [S] src src' [Bit] ↔ Valid hs.hasType hs'.hasType := by
  refine ⟨fun e =>
    Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.valid_of_eqv false e _ _,
    fun v => ?_⟩
  have loops : Valid t.loop_typed.hasType t'.loop_typed.hasType :=
    Valid.trans
      (Valid.symm
        (Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.valid_of_eqv false hf
          (seqRegion_typed hd hs).hasType t.loop_typed.hasType))
      (Valid.trans (Valid.seq hd hs hs' v)
        (Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.valid_of_eqv false hf'
          (seqRegion_typed hd hs').hasType t'.loop_typed.hasType))
  have packed : QLit (seqRegion_typed hd hs) = QLit (seqRegion_typed hd hs') :=
    (Paper.Extension.Singleton.ofRegion_eq_iff N (seqRegion_typed hd hs) (seqRegion_typed hd hs')).2
      (hf.trans (((loop_complete t t').2 loops).trans hf'.symm))
  have one : QLit he ≫ QLit hd = 𝟙 _ :=
    (q_comp he hd).symm.trans
      (((Paper.Extension.Singleton.ofRegion_eq_iff N (seqRegion_typed he hd) (idRegion_typed S)).2 ret).trans
        ((congrArg (π).map (ofRegion_id S)).trans ((π).map_id _)))
  have back : ∀ {k : Region signature.Instr} (hk : ValueBranches [S] k [Bit]),
      QLit hk = QLit he ≫ QLit (seqRegion_typed hd hk) := fun hk =>
    ((Category.id_comp _).symm.trans (congrArg (· ≫ QLit hk) one.symm)).trans
      ((Category.assoc _ _ _).trans (congrArg (QLit he ≫ ·) (q_comp hd hk).symm))
  apply (Paper.Extension.Singleton.ofRegion_eq_iff N hs hs').1
  exact (back hs).trans ((congrArg (QLit he ≫ ·) packed).trans (back hs').symm)

end Packed

/-! ## Regression: two tagged live Bits -/

/-- The packed loops of the written table with lets and of its mixed
table are equal on the packed state of two tagged Bits. -/
theorem letStash_loop_eqv (l₁ l₂ s n f : Bool) :
    Eqv false [States 1] (letStash l₁ l₂ s n f).loop (mixWritten (stashRow l₁ l₂ s) (stashAct n f)).loop
      [Bit] :=
  (loop_eqv_iff_entries _ _).2 (letStash_eqv_stash l₁ l₂ s n f)

/-- A changed blind query is distinguished on the packed state. -/
theorem letStash_loop_ne (l₁ l₂ n f n' f' : Bool) :
    ¬ Eqv false [States 1] (letStash l₁ l₂ false n f).loop (letStash l₁ l₂ true n' f').loop [Bit] :=
  fun e => letStash_ne_slot l₁ l₂ n f n' f' ((loop_eqv_iff_entries _ _).1 e 0)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Tables
