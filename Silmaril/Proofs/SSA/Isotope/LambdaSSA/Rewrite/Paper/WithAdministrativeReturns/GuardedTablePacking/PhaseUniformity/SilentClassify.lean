module

public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.SilentCycleTables

/-! # Every finite table of silent states has a classification -/

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

section Classify

variable {M : Nat} (sil : Fin (M + 1) → Option (Act M))

/-- The silent path from a state never reaches a return or a request. -/
def Diverges (y : Fin (M + 1)) : Prop := ∀ n, ¬ (resolveN sil n (.go y false)).Settled sil

theorem settled_bit (n : Nat) (y : Fin (M + 1)) (q q' : Bool)
    (h : (resolveN sil n (.go y q)).Settled sil) : (resolveN sil n (.go y q')).Settled sil := by
  cases hy : sil y with
  | none =>
    rw [resolveN_none sil n q' hy]
    exact hy
  | some A =>
    cases n with
    | zero =>
      have e : sil y = none := h
      rw [hy] at e
      cases e
    | succ n =>
      rw [resolveN_some sil n q hy] at h
      rw [resolveN_some sil n q' hy]
      exact h

theorem settled_succ : ∀ (n : Nat) (a : Act M), (resolveN sil n a).Settled sil →
    (resolveN sil (n + 1) a).Settled sil
  | n, .ret b, _ => by
    rw [resolveN_ret]
    exact True.intro
  | 0, .go y q, h => by
    rw [resolveN_none sil 1 q h]
    exact h
  | n + 1, .go y q, h => by
    cases hy : sil y with
    | none =>
      rw [resolveN_none sil (n + 2) q hy]
      exact hy
    | some A =>
      rw [resolveN_some sil n q hy] at h
      rw [resolveN_some sil (n + 1) q hy]
      exact settled_succ n A h

theorem settled_mono {n m : Nat} (le : n ≤ m) (a : Act M) (h : (resolveN sil n a).Settled sil) :
    (resolveN sil m a).Settled sil := by
  induction le with
  | refl => exact h
  | step _ ih => exact settled_succ sil _ a ih

theorem diverges_step {y : Fin (M + 1)} (h : Diverges sil y) :
    ∃ z q, sil y = some (.go z q) ∧ Diverges sil z := by
  cases hy : sil y with
  | none => exact absurd hy (h 0)
  | some A =>
    cases A with
    | ret b =>
      have s := h 1
      rw [resolveN_some sil 0 false hy] at s
      exact absurd True.intro s
    | go z q =>
      refine ⟨z, q, rfl, fun n hs => h (n + 1) ?_⟩
      rw [resolveN_some sil n false hy]
      exact settled_bit sil n z false q hs

theorem diverges_back {y z : Fin (M + 1)} {q : Bool} (hy : sil y = some (.go z q)) (h : Diverges sil z) :
    Diverges sil y := fun n hs => by
  cases n with
  | zero =>
    have e : sil y = none := hs
    rw [hy] at e
    cases e
  | succ n =>
    rw [resolveN_some sil n false hy] at hs
    exact h n (settled_bit sil n z q false hs)

open Classical in
/-- The states whose silent path never ends. -/
noncomputable def divCyc (y : Fin (M + 1)) : Bool := decide (Diverges sil y)

open Classical in
theorem divCyc_of {y : Fin (M + 1)} (h : Diverges sil y) : divCyc sil y = true := decide_eq_true h

open Classical in
theorem divCyc_not {y : Fin (M + 1)} (h : ¬ Diverges sil y) : divCyc sil y = false := decide_eq_false h

open Classical in
theorem of_divCyc {y : Fin (M + 1)} (h : divCyc sil y = true) : Diverges sil y := of_decide_eq_true h

theorem divCyc_cyclic : Cyclic sil (divCyc sil) := fun y hy => by
  obtain ⟨z, q, hz, dz⟩ := diverges_step sil (of_divCyc sil hy)
  exact ⟨z, q, hz, divCyc_of sil dz⟩

theorem settled_cut {a : Act M} (h : a.Settled sil) : a.Settled (cutSil sil (divCyc sil)) := by
  cases a with
  | ret b => exact True.intro
  | go y q =>
    have e : sil y = none := h
    show cutSil sil (divCyc sil) y = none
    unfold cutSil
    cases divCyc sil y <;> first | rfl | exact e

/-- Away from the diverging states, stopping at them changes nothing. -/
theorem cut_resolve : ∀ (n : Nat) (y : Fin (M + 1)) (q : Bool), ¬ Diverges sil y →
    resolveN (cutSil sil (divCyc sil)) n (.go y q) = resolveN sil n (.go y q)
  | 0, _, _, _ => rfl
  | n + 1, y, q, nd => by
    have cy : divCyc sil y = false := divCyc_not sil nd
    cases hy : sil y with
    | none =>
      have c : cutSil sil (divCyc sil) y = none := by
        unfold cutSil
        rw [cy]
        exact hy
      rw [resolveN_none sil (n + 1) q hy, resolveN_none _ (n + 1) q c]
    | some A =>
      have c : cutSil sil (divCyc sil) y = some A := by
        unfold cutSil
        rw [cy]
        exact hy
      rw [resolveN_some sil n q hy, resolveN_some _ n q c]
      cases A with
      | ret b => rw [resolveN_ret, resolveN_ret]
      | go z q' => exact cut_resolve n z q' fun dz => nd (diverges_back sil hy dz)

/-- Every finite table of silent states has a classification: a closed
set of states whose silent paths never end, and a fuel that resolves
every action to a return, a request state or a state of that set. -/
theorem classification :
    ∃ (cyc : Fin (M + 1) → Bool) (fuel : Nat), Cyclic sil cyc ∧
      ∀ a, (resolveN (cutSil sil cyc) fuel a).Settled (cutSil sil cyc) := by
  classical
  have ends : ∀ y, ∃ n, Diverges sil y ∨ (resolveN sil n (.go y false)).Settled sil := fun y => by
    by_cases d : Diverges sil y
    · exact ⟨0, .inl d⟩
    · obtain ⟨n, hn⟩ := not_forall.1 d
      exact ⟨n, .inr (not_not.1 hn)⟩
  choose time htime using ends
  refine ⟨divCyc sil, Finset.univ.sup time, divCyc_cyclic sil, fun a => ?_⟩
  cases a with
  | ret b =>
    rw [resolveN_ret]
    exact True.intro
  | go y q =>
    by_cases d : Diverges sil y
    · have c : cutSil sil (divCyc sil) y = none := by
        unfold cutSil
        rw [divCyc_of sil d]
      rw [resolveN_none _ _ q c]
      exact c
    · rw [cut_resolve sil _ y q d]
      have at_time := (htime y).resolve_left d
      exact settled_cut sil (settled_mono sil (Finset.le_sup (Finset.mem_univ y)) _
        (settled_bit sil _ y false q at_time))

end Classify

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Tables
