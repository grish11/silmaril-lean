module

public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.TableModel

/-! # A handoff table differs from its first poll only after the backedge -/

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

theorem handoff_zero (p q : Program) : (Table.handoff p q).prog 0 = p := by
  simp [Table.handoff]

theorem handoff_one (p q : Program) : (Table.handoff p q).prog 1 = q := by
  simp [Table.handoff]

/-- The first poll takes its backedge into state one, where the second
poll returns. -/
theorem handoff_witness (a b : Poll) (g s c : Bool) :
    (Except.ok (bit c), FreeMonoid.of (event a.label g (!a.returnRight, s)) *
      FreeMonoid.of (event b.label s (b.returnRight, c))) ∈
      (Table.handoff a.program b.program).observations 0 g := by
  rw [observations_eq, iter_unfold]
  refine .inr (.inr ⟨injVal 1 1 (Sum.inl (bit s)), _, _, ?_, ?_, rfl⟩)
  · rw [step_run, handoff_zero, Tagged.mem_bind]
    refine .inr ⟨Sum.inr (Sum.inl (bit s)), _, 1, ?_, mem_pure.2 ⟨rfl, rfl⟩, mul_one _⟩
    rw [WithGuardedTablePacking.BitLoop.stepModel_outcomes]
    exact (poll_outcomes a g _ _).2 ⟨!a.returnRight, s, by rw [flag_not]; rfl, rfl⟩
  · rw [iter_unfold]
    refine .inr (.inl ⟨bit c, rfl, ?_⟩)
    rw [step_run, handoff_one, Tagged.mem_bind]
    refine .inr ⟨Sum.inl (bit c), _, 1, ?_, mem_pure.2 ⟨rfl, rfl⟩, mul_one _⟩
    rw [WithGuardedTablePacking.BitLoop.stepModel_outcomes]
    exact (poll_outcomes b s _ _).2 ⟨b.returnRight, c, by rw [flag_self]; rfl, rfl⟩

/-- Every complete run of a poll loop sends only that poll's label, and
its last reply is on the returning side. -/
def Shape (a : Poll) (obs : Except Bool (value Bit) × Word) : Prop :=
  FreeMonoid.toList obs.2 ≠ [] ∧ (∀ e ∈ FreeMonoid.toList obs.2, e.label = a.label) ∧
    ∀ e, (FreeMonoid.toList obs.2).getLast? = some e → e.right = a.returnRight

theorem shape (a : Poll) (g : Bool) {obs : Except Bool (value Bit) × Word}
    (h : obs ∈ loopObservations a.program g) : Shape a obs := by
  rw [WithGuardedTablePacking.BitLoop.loopObservations_eq] at h
  refine iter_induction (stepModel a.program) (fun _ => {obs | Shape a obs}) ?_ ?_ ?_ _ h
  · intro s t w hw
    obtain ⟨g, rfl⟩ := state_cases s
    rw [WithGuardedTablePacking.BitLoop.stepModel_outcomes] at hw
    obtain ⟨tag, pl, hy, -⟩ := (poll_outcomes a g _ _).1 hw
    cases hy
  · intro s b w hw
    obtain ⟨g, rfl⟩ := state_cases s
    rw [WithGuardedTablePacking.BitLoop.stepModel_outcomes] at hw
    obtain ⟨tag, pl, hy, rfl⟩ := (poll_outcomes a g _ _).1 hw
    have side := tag_of_return hy
    show Shape a _
    refine ⟨by simp, ?_, ?_⟩
    · intro e he
      have : e = event a.label g (tag, pl) := by simpa using he
      rw [this]
      rfl
    · intro e he
      have : e = event a.label g (tag, pl) := by simpa using he.symm
      rw [this]
      exact side
  · intro s next u r v hu hv
    obtain ⟨g, rfl⟩ := state_cases s
    rw [WithGuardedTablePacking.BitLoop.stepModel_outcomes] at hu
    obtain ⟨tag, pl, -, rfl⟩ := (poll_outcomes a g _ _).1 hu
    obtain ⟨nonempty, labels, last⟩ := hv
    show Shape a _
    refine ⟨by simp, ?_, ?_⟩
    · intro e he
      have cases : e = event a.label g (tag, pl) ∨ e ∈ FreeMonoid.toList v := by simpa using he
      rcases cases with rfl | tail
      · rfl
      · exact labels e tail
    · intro e he
      apply last e
      have split : FreeMonoid.toList (FreeMonoid.of (event a.label g (tag, pl)) * v) =
          event a.label g (tag, pl) :: FreeMonoid.toList v := by simp
      rw [split] at he
      cases hv' : FreeMonoid.toList v with
      | nil => exact (nonempty hv').elim
      | cons x xs =>
        rw [hv'] at he
        simpa using he

theorem handoff_not_poll {a b : Poll} (ne : a ≠ b) (g s c : Bool) :
    (Except.ok (bit c), FreeMonoid.of (event a.label g (!a.returnRight, s)) *
      FreeMonoid.of (event b.label s (b.returnRight, c))) ∉ loopObservations a.program g := by
  intro h
  obtain ⟨-, labels, last⟩ := shape a g h
  have l := labels (event b.label s (b.returnRight, c)) (by simp)
  have r := last (event b.label s (b.returnRight, c)) (by simp)
  obtain ⟨la, ra⟩ := a
  obtain ⟨lb, rb⟩ := b
  cases (show lb = la from l)
  cases (show rb = ra from r)
  exact ne rfl

theorem handoff_observations_ne {a b : Poll} (ne : a ≠ b) (g : Bool) :
    (Table.handoff a.program b.program).observations 0 g ≠ loopObservations a.program g :=
  fun eq => handoff_not_poll ne g false false (eq ▸ handoff_witness a b g false false)

theorem handoff_ne {a b : Poll} (ne : a ≠ b) :
    ¬ WithGuardedTablePacking.WithPhaseUniformity.Eqv false [State]
      ((Table.handoff a.program b.program).entered 0) (loopRegion a.program) [Bit] := by
  intro e
  have eq := WithGuardedTablePacking.WithPhaseUniformity.Eqv.sound false J M (fun _ _ => ⟨rfl, rfl⟩) e
    ((Table.handoff a.program b.program).entered_typed 0).hasType (loop_typed a.program).hasType
  refine handoff_observations_ne ne false ?_
  unfold Table.observations loopObservations denoteSingletonRegion
  rw [eq]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.TableModel
