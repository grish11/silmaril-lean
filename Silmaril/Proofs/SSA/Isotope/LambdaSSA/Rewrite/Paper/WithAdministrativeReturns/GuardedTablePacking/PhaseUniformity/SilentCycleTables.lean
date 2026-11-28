module

public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.SilentCycle

/-! # Mixed tables with silent cycles: three landings at the original entries -/

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

section Cut

variable {M : Nat} {sil : Fin (M + 1) → Option (Act M)} {cyc : Fin (M + 1) → Bool}

theorem cut_some {y : Fin (M + 1)} {A : Act M} (h : cutSil sil cyc y = some A) : sil y = some A := by
  unfold cutSil at h
  cases hy : cyc y with
  | true =>
    rw [hy] at h
    cases h
  | false =>
    rw [hy] at h
    exact h

theorem cut_none {y : Fin (M + 1)} (h : cutSil sil cyc y = none) (hy : cyc y = false) : sil y = none := by
  unfold cutSil at h
  rw [hy] at h
  exact h

/-- The successor of a silent state. -/
def silNext (sil : Fin (M + 1) → Option (Act M)) (y : Fin (M + 1)) : Fin (M + 1) :=
  match sil y with
  | some (.go z _) => z
  | _ => y

theorem silNext_eq {y z : Fin (M + 1)} {q : Bool} (h : sil y = some (.go z q)) : silNext sil y = z := by
  unfold silNext
  rw [h]

end Cut

theorem landing_congr {M : Nat} {L L' : Landing M} (e : L = L') :
    QLit (Landing.region_typed L) = QLit (Landing.region_typed L') := by
  subst e
  rfl

theorem ask_act_eq {K : Nat} {m : MixRow} {r : EnvRow} (h : m = .ask r) (a₀ : Bool → Bool → Act K) :
    m.act K a₀ = a₀ := by
  subst h
  rfl

theorem settledAct_carries' {M : Nat} (c : Fin (M + 1) → Bool) (sil : Fin (M + 1) → Option (Act M))
    (hcar : ∀ y A, sil y = some A → A.Carries c) (fuel : Nat) (m : MixRow) (x : Fin (M + 1))
    (a₀ : Bool → Bool → Act M) (h₀ : ∀ a b, (a₀ a b).Carries c) (a b : Bool) :
    (m.settledAct sil fuel x (c x) a₀ a b).Carries c := by
  cases m with
  | ask r => exact resolve_carries sil c hcar fuel _ (h₀ a b)
  | pure e => exact rfl

section Mix

variable {K : Nat} (row : Fin (K + 1) → MixRow) (act : Fin (K + 1) → Bool → Bool → Act K)
  {cyc : Fin (K + (K + 1) + 1) → Bool} {fuel : Nat} (hcl : Classified row act cyc fuel)

theorem cut_hsil (y : Fin (K + (K + 1) + 1)) (A : Act (K + (K + 1)))
    (h : cutSil (mixSil row act) cyc y = some A) :
    ofRegion (seqValueBranches (const_typed (splitBit y)) ((splitRouter (mixRouter row act)).rows_typed y)) =
      ofRegion (act_typed (K + (K + 1)) A) :=
  mix_hsil row act y A (cut_some h)

theorem cut_hcar (y : Fin (K + (K + 1) + 1)) (A : Act (K + (K + 1)))
    (h : cutSil (mixSil row act) cyc y = some A) : A.Carries splitBit :=
  mix_hcar row act y A (cut_some h)

include hcl in
theorem mix_hcyc (y : Fin (K + (K + 1) + 1)) (hy : cyc y = true) :
    ofRegion (seqValueBranches (const_typed (splitBit y)) ((splitRouter (mixRouter row act)).rows_typed y)) =
        ofRegion (act_typed (K + (K + 1))
          (.go (silNext (mixSil row act) y) (splitBit (silNext (mixSil row act) y)))) ∧
      cyc (silNext (mixSil row act) y) = true := by
  obtain ⟨z, q, hz, cz⟩ := hcl.cyclic y hy
  have carried : splitBit z = q := mix_hcar row act y (.go z q) hz
  rw [silNext_eq hz, carried]
  exact ⟨mix_hsil row act y (.go z q) hz, cz⟩

include hcl in
/-- A state of the closed silent set, entered with its Bit, is the
canonical silent self-loop. -/
theorem mix_cycle (y : Fin (K + (K + 1) + 1)) (hy : cyc y = true) :
    QLit (const_typed (splitBit y)) ≫ QLit ((splitRouter (mixRouter row act)).entered_typed y) =
      QLit spinRegion_typed :=
  cycle_spin (splitRouter (mixRouter row act)) splitBit cyc (silNext (mixSil row act)) (mix_hact row act)
    (mix_hcyc row act hcl) y hy

include hcl in
/-- At a request row, the resolved table is the table of resolved request
rows. -/
theorem resolved_rows3 (y : Fin (K + (K + 1) + 1)) (hy : mixSil row act y = none) :
    Eqv false [State]
      (((splitRouter (mixRouter row act)).resolved (cutSil (mixSil row act) cyc) fuel).entered y)
      ((envRouter (fun x => (row (splitRow x)).envRow) (mixAct3 row act cyc fuel)).entered y) [Bit] :=
  router_bisimulation_eqv _ _ (fun x y => x = y ∧ mixSil row act x = none)
    ⟨fun x y ⟨e, hx⟩ => by
        subst e
        obtain ⟨r, hm⟩ := silent_none hx
        exact ask_program hm,
      fun x y ⟨e, hx⟩ a b => by
        subst e
        obtain ⟨r, hm⟩ := silent_none hx
        have same := ask_act hm (cutSil (mixSil row act) cyc) fuel x (splitBit x) (act (splitRow x)) redirect a b
        have quiet := hcl.quiet x a b hx
        rw [← ask_act_eq hm (act (splitRow x))] at quiet
        show Act.Rel (fun x y => x = y ∧ mixSil row act x = none)
          (resolveN (cutSil (mixSil row act) cyc) fuel
            (redirect ((row (splitRow x)).act K (act (splitRow x)) a b)))
          ((row (splitRow x)).settledAct (cutSil (mixSil row act) cyc) fuel x (splitBit x)
            (fun a b => redirect (act (splitRow x) a b)) a b)
        rw [← same]
        exact rel_settled (mixSil row act) _ quiet⟩ y y ⟨rfl, hy⟩

include hcl in
theorem resolved_source3 (y : Fin (K + (K + 1) + 1)) (hy : mixSil row act y = none) :
    QLit (const_typed (splitBit y)) ≫
        QLit (((splitRouter (mixRouter row act)).resolved (cutSil (mixSil row act) cyc) fuel).entered_typed y) =
      QLit (const_typed (splitBit y)) ≫ QLit ((mixSource3 row act cyc fuel).entered_typed y) :=
  (congrArg (QLit (const_typed (splitBit y)) ≫ ·)
    ((Paper.Extension.Singleton.ofRegion_eq_iff N _ _).2 (resolved_rows3 row act hcl y hy))).trans
    (carried_const splitBit (fun x => (row (splitRow x)).envRow) (mixAct3 row act cyc fuel)
      (fun x a b => settledAct_carries' splitBit (cutSil (mixSil row act) cyc) (cut_hcar row act) fuel
        (row (splitRow x)) x _ (fun _ _ => redirect_carries _) a b) y)

include hcl in
/-- A resolved action continued in the resolved table is its landing:
a returned Bit, the request trees, or the canonical silent self-loop. -/
theorem landing_arrow3 (a : Act (K + (K + 1))) (hs : a.Settled (cutSil (mixSil row act) cyc))
    (hc : a.Carries splitBit) :
    (π).map (Act.arrow ((splitRouter (mixRouter row act)).resolved (cutSil (mixSil row act) cyc) fuel) a) =
      QLit (Landing.region_typed (a.landing3 cyc (mixSource3 row act cyc fuel))) := by
  cases a with
  | ret b => rw [arrow_ret]
  | go y q =>
    have cy : splitBit y = q := hc
    subst cy
    rw [arrow_go, (π).map_comp]
    cases hy : cyc y with
    | true =>
      have land : (Act.go y (splitBit y)).landing3 cyc (mixSource3 row act cyc fuel) = .spin := by
        show (match cyc y with | true => Landing.spin | false => _) = _
        rw [hy]
      have same := silent_entered (splitRouter (mixRouter row act)) splitBit (cutSil (mixSil row act) cyc) fuel
        (cut_hsil row act) (cut_hcar row act) (mix_hact row act) (fun x a b => hcl.settled _) y
      rw [landing_congr land, same]
      exact mix_cycle row act hcl y hy
    | false =>
      have land : (Act.go y (splitBit y)).landing3 cyc (mixSource3 row act cyc fuel) =
          .at (mixSource3 row act cyc fuel) y (splitBit y) := by
        show (match cyc y with | true => Landing.spin | false => _) = _
        rw [hy]
      rw [landing_congr land]
      exact (resolved_source3 row act hcl y (cut_none hs hy)).trans
        (q_const (splitBit y) ((mixSource3 row act cyc fuel).entered_typed y)).symm

include hcl in
/-- A classified mixed table entered with each constant is its landing. -/
theorem mix_landed3 (j : Fin (K + 1)) :
    Landed ((mixRouter row act).entered j) (mixLanding3 row act cyc fuel j) := fun q => by
  apply (Paper.Extension.Singleton.ofRegion_eq_iff N (constEntry_typed q ((mixRouter row act).entered_typed j))
    (Landing.region_typed (mixLanding3 row act cyc fuel j q))).1
  have fold : QLit ((splitRouter (mixRouter row act)).entered_typed (splitIdx j q)) =
      QLit ((mixRouter row act).entered_typed j) :=
    (Paper.Extension.Singleton.ofRegion_eq_iff N _ _).2 (router_split_fold (mixRouter row act) j q)
  have entry := silent_entry (splitRouter (mixRouter row act)) splitBit (cutSil (mixSil row act) cyc) fuel
    (cut_hsil row act) (cut_hcar row act) (mix_hact row act) (fun x a b => hcl.settled _) (splitIdx j q)
    (hcl.settled _)
  rw [splitBit_idx] at entry
  have carries := resolve_carries (cutSil (mixSil row act) cyc) splitBit (cut_hcar row act) fuel
    (.go (splitIdx j q) q) (splitBit_idx j q)
  exact (q_const q ((mixRouter row act).entered_typed j)).trans
    ((congrArg (QLit (const_typed q) ≫ ·) fold.symm).trans
      ((((π).map_comp _ _).symm.trans (congrArg (π).map entry)).trans
        (landing_arrow3 row act hcl _ (hcl.settled _) carries)))

include hcl in
theorem written_landed3 (j : Fin (K + 1)) :
    Landed ((mixWritten row act).entered j) (mixLanding3 row act cyc fuel j) :=
  landed_congr ((mixWritten row act).entered_typed j) ((mixRouter row act).entered_typed j)
    (.paper ((Paper.TypeCategory.ofRegion_eq_iff _ _).mp (mix_written_arrow row act j)))
    (mix_landed3 row act hcl j)

end Mix

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Tables
