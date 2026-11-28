module

public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.SilentClassify
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.SilentPoint

/-! # Mixed tables: completeness at the original entries, and the regression -/

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

/-! ## Completeness -/

section Complete

variable {M M' : Nat} {r r' : Region signature.Instr} {L : Bool → Landing M} {L' : Bool → Landing M'}

/-- Loops with landings are equal exactly when their landings agree at
each constant. -/
theorem landed_iff_rel (h : ValueBranches [State] r [Bit]) (h' : ValueBranches [State] r' [Bit])
    (hl : Landed r L) (hl' : Landed r' L') : Eqv false [State] r r' [Bit] ↔ ∀ q, (L q).Rel (L' q) :=
  ⟨fun e q => TableModel.landed_rel h h' hl hl'
      (Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.valid_of_eqv false e _ _) q,
    landed_eqv h h' hl hl'⟩

/-- And exactly when they are valid in every supported model. -/
theorem landed_complete (h : ValueBranches [State] r [Bit]) (h' : ValueBranches [State] r' [Bit])
    (hl : Landed r L) (hl' : Landed r' L') : Eqv false [State] r r' [Bit] ↔ Valid h.hasType h'.hasType :=
  ⟨fun e => Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.valid_of_eqv false e _ _,
    fun v => landed_eqv h h' hl hl' (TableModel.landed_rel h h' hl hl' v)⟩

end Complete

/-! ## The written table -/

section Written

variable {K : Nat} (row : Fin (K + 1) → MixRow) (act : Fin (K + 1) → Bool → Bool → Act K)
  {rank : Fin (K + 1) → Bool → Nat} {fuel : Nat} (hr : Ranked row act rank fuel)

theorem mix_written_eqv (j : Fin (K + 1)) :
    Eqv false [State] ((mixWritten row act).entered j) ((mixRouter row act).entered j) [Bit] :=
  .paper ((Paper.TypeCategory.ofRegion_eq_iff _ _).mp (mix_written_arrow row act j))

include hr in
theorem written_landed (j : Fin (K + 1)) :
    Landed ((mixWritten row act).entered j) (mixLanding row act fuel j) :=
  landed_congr ((mixWritten row act).entered_typed j) ((mixRouter row act).entered_typed j)
    (mix_written_eqv row act j) (mix_landed row act hr j)

include hr in
theorem written_case (j : Fin (K + 1)) :
    Eqv false [State] ((mixWritten row act).entered j) (mixCase row act fuel j) [Bit] :=
  landed_case ((mixWritten row act).entered_typed j) (written_landed row act hr j)

end Written

/-! ## Regression -/

theorem hop_ranked (l f s : Bool) : Ranked (hopRow l) (hopAct f s) hopRank 3 := by
  refine ⟨fun i g => ?_, fun i g e hrow j q hact e' hrow' => ?_⟩
  · match i with
    | 0 => exact Nat.lt_succ_self 2
    | 1 => exact Nat.lt_succ_of_lt (Nat.lt_succ_self 1)
    | 2 => exact Nat.succ_pos 2
  · match i with
    | 0 =>
      cases hrow
      cases hact
      exact Nat.lt_succ_self 1
    | 1 =>
      cases hrow
      cases g
      · cases hact
      · cases hact
        cases hrow'
    | 2 => cases hrow

/-- A silent cycle has no ranking. -/
theorem spin_not_ranked (rank : Fin 1 → Bool → Nat) (fuel : Nat) : ¬ Ranked spinRow spinAct rank fuel :=
  fun h => Nat.lt_irrefl _ (h.2 0 false 1 rfl 0 false rfl 1 rfl)

/-- Entered with `true`, two silent hops reach a return. -/
theorem hop_return (l : Bool) : mixLanding (hopRow l) (hopAct true true) 3 0 true = .ret true := by
  rfl

/-- Entered with `false`, two silent hops change the Bit and reach the
request row with `true`. -/
theorem hop_request (l : Bool) :
    mixLanding (hopRow l) (hopAct true true) 3 0 false =
      .at (mixSource (hopRow l) (hopAct true true) 3) (splitIdx 2 true) true := by
  rfl

/-- The tables are equal at the first row exactly when the hop changes
the Bit in the same way and the request row is entered with the same Bit. -/
theorem hop_eqv_iff (l f s f' s' : Bool) :
    Eqv false [State] ((mixWritten (hopRow l) (hopAct f s)).entered 0)
      ((mixWritten (hopRow l) (hopAct f' s')).entered 0) [Bit] ↔ f = f' ∧ s = s' := by
  constructor
  · intro e
    have h := (landed_iff_rel ((mixWritten (hopRow l) (hopAct f s)).entered_typed 0)
      ((mixWritten (hopRow l) (hopAct f' s')).entered_typed 0)
      (written_landed (hopRow l) (hopAct f s) (hop_ranked l f s) 0)
      (written_landed (hopRow l) (hopAct f' s') (hop_ranked l f' s') 0)).1 e
    cases f <;> cases f' <;> cases s <;> cases s' <;> first
      | exact ⟨rfl, rfl⟩
      | exact False.elim (h true)
      | exact absurd (And.left (h true)) (by decide)
      | exact absurd (And.left (h false)) (by decide)
  · rintro ⟨rfl, rfl⟩
    exact Paper.Extension.Eqv.refl ((mixWritten (hopRow l) (hopAct f s)).entered_typed 0).hasType

/-! ## Silent cycles -/

section Cycles

variable {K : Nat} (row : Fin (K + 1) → MixRow) (act : Fin (K + 1) → Bool → Bool → Act K)
  {cyc : Fin (K + (K + 1) + 1) → Bool} {fuel : Nat} (hcl : Classified row act cyc fuel)

include hcl in
theorem written_case3 (j : Fin (K + 1)) :
    Eqv false [State] ((mixWritten row act).entered j) (mixCase3 row act cyc fuel j) [Bit] :=
  landed_case ((mixWritten row act).entered_typed j) (written_landed3 row act hcl j)

end Cycles

theorem all_classified {K : Nat} (act : Fin (K + 1) → Bool → Bool → Act K)
    (h : ∀ i g, ∃ j q, act i true g = .go j q) : Classified (fun _ => .pure 1) act allCyc 0 :=
  ⟨fun y _ => by
      obtain ⟨j, q, e⟩ := h (splitRow y) (splitBit y)
      refine ⟨splitIdx j q, q, ?_, rfl⟩
      show some (redirect (act (splitRow y) true (splitBit y))) = _
      rw [e]
      rfl,
    fun a => by
      cases a with
      | ret b => exact True.intro
      | go y q => exact rfl,
    fun x a b hx => by cases hx⟩

theorem flip_classified : Classified spinRow flipAct allCyc 0 :=
  all_classified flipAct fun _ g => ⟨0, !g, rfl⟩

theorem spin_classified : Classified spinRow spinAct allCyc 0 :=
  all_classified spinAct fun _ g => ⟨0, g, rfl⟩

theorem lead_classified : Classified leadRow leadAct allCyc 0 :=
  all_classified leadAct fun i g => by
    match i with
    | 0 => exact ⟨1, g, rfl⟩
    | 1 => exact ⟨1, !g, rfl⟩

/-- A silent cycle that negates the Bit lands in the canonical silent
self-loop at both constants. -/
theorem flip_landing (q : Bool) : mixLanding3 spinRow flipAct allCyc 0 0 q = .spin := by
  rfl

/-- The cycle that negates the Bit, the cycle that keeps it, and the hop
into a cycle are equal: all are the canonical silent self-loop. -/
theorem flip_eqv_spin :
    Eqv false [State] ((mixWritten spinRow flipAct).entered 0) ((mixWritten spinRow spinAct).entered 0) [Bit] :=
  landed_eqv ((mixWritten spinRow flipAct).entered_typed 0) ((mixWritten spinRow spinAct).entered_typed 0)
    (written_landed3 spinRow flipAct flip_classified 0) (written_landed3 spinRow spinAct spin_classified 0)
    fun _ => True.intro

theorem lead_eqv_flip :
    Eqv false [State] ((mixWritten leadRow leadAct).entered 0) ((mixWritten spinRow flipAct).entered 0) [Bit] :=
  landed_eqv ((mixWritten leadRow leadAct).entered_typed 0) ((mixWritten spinRow flipAct).entered_typed 0)
    (written_landed3 leadRow leadAct lead_classified 0) (written_landed3 spinRow flipAct flip_classified 0)
    fun _ => True.intro

theorem echo_ranked : Ranked echoRow echoPure (fun _ _ => 0) 1 :=
  ⟨fun _ _ => Nat.zero_lt_one, fun i g e hrow j q hact => by
    cases hrow
    cases hact⟩

/-- The silent cycle is not an immediate return. -/
theorem flip_ne_return :
    ¬ Eqv false [State] ((mixWritten spinRow flipAct).entered 0) ((mixWritten echoRow echoPure).entered 0)
      [Bit] := fun e =>
  (landed_iff_rel ((mixWritten spinRow flipAct).entered_typed 0) ((mixWritten echoRow echoPure).entered_typed 0)
    (written_landed3 spinRow flipAct flip_classified 0) (written_landed echoRow echoPure echo_ranked 0)).1 e
    false

/-- The silent cycle is not a loop that sends a request. -/
theorem flip_ne_request {M : Nat} (s : LTable M) (i : Fin (M + 1)) :
    ¬ Eqv false [State] ((mixWritten spinRow flipAct).entered 0) (s.entered i) [Bit] := fun e =>
  (landed_iff_rel ((mixWritten spinRow flipAct).entered_typed 0) (s.entered_typed i)
    (written_landed3 spinRow flipAct flip_classified 0)
    (landed_of_pointed (pointed_of_eqv (s.entered_typed i) s i
      (Paper.Extension.Eqv.refl (s.entered_typed i).hasType)))).1 e false

theorem tri_classified (l : Bool) : Classified (triRow l) triAct triCyc 1 := by
  refine ⟨fun y hy => ?_, fun a => ?_, fun x a b hx => ?_⟩
  · match y with
    | 0 => cases hy
    | 1 => exact ⟨_, _, rfl, rfl⟩
    | 2 => cases hy
    | 3 => cases hy
    | 4 => exact ⟨_, _, rfl, rfl⟩
    | 5 => cases hy
  · cases a with
    | ret b => exact True.intro
    | go y q =>
      match y with
      | 0 => exact rfl
      | 1 => exact rfl
      | 2 => exact rfl
      | 3 => exact rfl
      | 4 => exact rfl
      | 5 => exact rfl
  · match x with
    | 0 => cases hx
    | 1 => cases hx
    | 2 => cases a <;> cases b <;> first | exact True.intro | exact rfl
    | 3 => cases hx
    | 4 => cases hx
    | 5 => cases a <;> cases b <;> first | exact True.intro | exact rfl

/-- One row with both outcomes: entered with `false` its silent path ends
in the cycle, entered with `true` it reaches the request row. -/
theorem tri_cycle (l : Bool) : mixLanding3 (triRow l) triAct triCyc 1 0 false = .spin := by
  rfl

theorem tri_request (l : Bool) :
    mixLanding3 (triRow l) triAct triCyc 1 0 true =
      .at (mixSource3 (triRow l) triAct triCyc 1) (splitIdx 2 true) true := by
  rfl

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Tables
