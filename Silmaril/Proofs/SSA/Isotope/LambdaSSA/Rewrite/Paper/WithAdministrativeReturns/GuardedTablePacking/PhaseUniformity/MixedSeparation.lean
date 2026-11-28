module

public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.MixedTables
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.TableSeparation

/-! # Labels of mixed tables and a variant that differs after the backedge -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.TableModel

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithAdministrativeReturns
open Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
open Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop
open Paper.WithAdministrativeReturns.BitFragment.Recursive (Program)
open Paper.WithCaseBind.BitQuery (signature Trace model modelCoherent Event)
open Paper.WithCaseBind.BitQuery.RequestTree
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli (value instructions)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit bit)
open Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Silmaril.Semantics.NondeterministicTrace (Tagged)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.BitLoop

local notation "J" => _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli.J (m := Trace)
local notation "M" => _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli.types

noncomputable local instance : InstructionModel J M signature.Instr := instructions model
local instance : RegionTypingCoherent (Φ := signature.Instr) J M := modelCoherent

set_option backward.isDefEq.respectTransparency false

theorem injVal_cases : ∀ (K : Nat) (v : value (States K)), ∃ i s, v = injVal K i s
  | 0, v => ⟨0, v, rfl⟩
  | K + 1, v => by
    rcases v with s | v'
    · exact ⟨0, s, rfl⟩
    · obtain ⟨i, s, rfl⟩ := injVal_cases K v'
      exact ⟨i.succ, s, rfl⟩

/-- A poll row contributes one event with the poll's label and no fault. -/
theorem poll_step_outcome {K : Nat} (t : Table K) (i : Fin (K + 1)) (a : Poll)
    (h : t.prog i = a.program) (g : Bool) {y : Except Bool (value Bit ⊕ value (States K))} {w : Word}
    (hm : (y, w) ∈ (t.stepM (injVal K i (Sum.inl (bit g)))).outcomes) :
    ∃ tag pl, w = FreeMonoid.of (event a.label g (tag, pl)) ∧ ∃ z, y = .ok z := by
  rw [step_run, h, Tagged.mem_bind] at hm
  rcases hm with ⟨t', rfl, ht⟩ | ⟨x, u, v, hx, hk, rfl⟩
  · rw [WithGuardedTablePacking.BitLoop.stepModel_outcomes] at ht
    obtain ⟨tag, pl, hy, -⟩ := (poll_outcomes a g _ _).1 ht
    cases hy
  · rw [WithGuardedTablePacking.BitLoop.stepModel_outcomes] at hx
    obtain ⟨tag, pl, -, rfl⟩ := (poll_outcomes a g _ _).1 hx
    rcases x with b | s
    · obtain ⟨rfl, rfl⟩ := mem_pure.1 hk
      exact ⟨tag, pl, mul_one _, _, rfl⟩
    · obtain ⟨rfl, rfl⟩ := mem_pure.1 hk
      exact ⟨tag, pl, mul_one _, _, rfl⟩

/-- In a table of polls with one common label, every request of every
complete run carries that label. -/
theorem labels {K : Nat} (t : Table K) (poll : Fin (K + 1) → Poll) (l : Bool)
    (hprog : ∀ i, t.prog i = (poll i).program) (hl : ∀ i, (poll i).label = l)
    (i : Fin (K + 1)) (g : Bool) {obs : Except Bool (value Bit) × Word}
    (h : obs ∈ t.observations i g) : ∀ e ∈ FreeMonoid.toList obs.2, e.label = l := by
  rw [observations_eq] at h
  refine iter_induction t.stepM (fun _ => {obs | ∀ e ∈ FreeMonoid.toList obs.2, e.label = l}) ?_ ?_ ?_ _ h
  · intro v t' w hw
    obtain ⟨i, s, rfl⟩ := injVal_cases K v
    obtain ⟨g, rfl⟩ := state_cases s
    obtain ⟨tag, pl, -, z, hz⟩ := poll_step_outcome t i (poll i) (hprog i) g hw
    cases hz
  · intro v b w hw
    obtain ⟨i, s, rfl⟩ := injVal_cases K v
    obtain ⟨g, rfl⟩ := state_cases s
    obtain ⟨tag, pl, rfl, -⟩ := poll_step_outcome t i (poll i) (hprog i) g hw
    intro e he
    have : e = event (poll i).label g (tag, pl) := by simpa using he
    rw [this]
    exact hl i
  · intro v next u r v' hu hv
    obtain ⟨i, s, rfl⟩ := injVal_cases K v
    obtain ⟨g, rfl⟩ := state_cases s
    obtain ⟨tag, pl, rfl, -⟩ := poll_step_outcome t i (poll i) (hprog i) g hu
    intro e he
    have cases : e = event (poll i).label g (tag, pl) ∨ e ∈ FreeMonoid.toList v' := by simpa using he
    rcases cases with rfl | tail
    · exact hl i
    · exact hv e tail

/-- The first poll repeats into the second class, where the second poll returns. -/
theorem pingPong_witness (q p : Poll) (g s c : Bool) :
    (Except.ok (bit c), FreeMonoid.of (event q.label g (!q.returnRight, s)) *
      FreeMonoid.of (event p.label s (p.returnRight, c))) ∈
      (Table.pingPong q.program p.program).observations 0 g := by
  have zero : (Table.pingPong q.program p.program).prog 0 = q.program := rfl
  have one : (Table.pingPong q.program p.program).prog 1 = p.program := rfl
  rw [observations_eq, iter_unfold]
  refine .inr (.inr ⟨injVal 1 1 (Sum.inl (bit s)), _, _, ?_, ?_, rfl⟩)
  · rw [step_run, zero, Tagged.mem_bind]
    refine .inr ⟨Sum.inr (Sum.inl (bit s)), _, 1, ?_, mem_pure.2 ⟨rfl, rfl⟩, mul_one _⟩
    rw [WithGuardedTablePacking.BitLoop.stepModel_outcomes]
    exact (poll_outcomes q g _ _).2 ⟨!q.returnRight, s, by rw [flag_not]; rfl, rfl⟩
  · rw [iter_unfold]
    refine .inr (.inl ⟨bit c, rfl, ?_⟩)
    rw [step_run, one, Tagged.mem_bind]
    refine .inr ⟨Sum.inl (bit c), _, 1, ?_, mem_pure.2 ⟨rfl, rfl⟩, mul_one _⟩
    rw [WithGuardedTablePacking.BitLoop.stepModel_outcomes]
    exact (poll_outcomes p s _ _).2 ⟨p.returnRight, c, by rw [flag_self]; rfl, rfl⟩

theorem observations_of_eqv {K K' : Nat} {t : Table K} {t' : Table K'} {i : Fin (K + 1)}
    {i' : Fin (K' + 1)}
    (e : WithGuardedTablePacking.WithPhaseUniformity.Eqv false [State] (t.entered i) (t'.entered i') [Bit])
    (g : Bool) : t.observations i g = t'.observations i' g := by
  have eq := WithGuardedTablePacking.WithPhaseUniformity.Eqv.sound false J M (fun _ _ => ⟨rfl, rfl⟩) e
    (t.entered_typed i).hasType (t'.entered_typed i').hasType
  unfold Table.observations denoteSingletonRegion
  rw [eq]

theorem pingPong_ne {q p p' : Poll} (same : q.label = p.label) (other : p'.label ≠ p.label) :
    ¬ WithGuardedTablePacking.WithPhaseUniformity.Eqv false [State]
      ((Table.pingPong q.program p'.program).entered 0)
      ((Table.pingPong q.program p.program).entered 0) [Bit] := by
  intro e
  have mem := pingPong_witness q p' false false false
  rw [observations_of_eqv e false] at mem
  have all := labels (Table.pingPong q.program p.program) (Fin.cases q (fun _ => p)) p.label
    (fun i => Fin.cases rfl (fun _ => rfl) i) (fun i => Fin.cases same (fun _ => rfl) i) 0 false mem
  exact other (all (event p'.label false (p'.returnRight, false)) (by simp))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.TableModel
