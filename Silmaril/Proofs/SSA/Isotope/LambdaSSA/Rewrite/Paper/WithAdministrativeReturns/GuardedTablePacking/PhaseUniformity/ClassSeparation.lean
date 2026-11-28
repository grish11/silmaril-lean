module

public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.ClassTables
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.MixedSeparation

/-! # A variant of the uneven table that differs after one backedge -/

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

/-- In any table, a poll row that repeats into a poll row that returns. -/
theorem repeat_return {K : Nat} (t : Table K) (i : Fin (K + 1)) (q p : Poll) (hq : t.prog i = q.program)
    (hp : t.prog (t.next i) = p.program) (g s c : Bool) :
    (Except.ok (bit c), FreeMonoid.of (event q.label g (!q.returnRight, s)) *
      FreeMonoid.of (event p.label s (p.returnRight, c))) ∈ t.observations i g := by
  rw [observations_eq, iter_unfold]
  refine .inr (.inr ⟨injVal K (t.next i) (Sum.inl (bit s)), _, _, ?_, ?_, rfl⟩)
  · rw [step_run, hq, Tagged.mem_bind]
    refine .inr ⟨Sum.inr (Sum.inl (bit s)), _, 1, ?_, mem_pure.2 ⟨rfl, rfl⟩, mul_one _⟩
    rw [WithGuardedTablePacking.BitLoop.stepModel_outcomes]
    exact (poll_outcomes q g _ _).2 ⟨!q.returnRight, s, by rw [flag_not]; rfl, rfl⟩
  · rw [iter_unfold]
    refine .inr (.inl ⟨bit c, rfl, ?_⟩)
    rw [step_run, hp, Tagged.mem_bind]
    refine .inr ⟨Sum.inl (bit c), _, 1, ?_, mem_pure.2 ⟨rfl, rfl⟩, mul_one _⟩
    rw [WithGuardedTablePacking.BitLoop.stepModel_outcomes]
    exact (poll_outcomes p s _ _).2 ⟨p.returnRight, c, by rw [flag_self]; rfl, rfl⟩

/-- The polls of the three classes. -/
def cyclePolls (a b c : Poll) (i : Fin 3) : Poll :=
  match i with
  | 0 => a
  | 1 => b
  | 2 => c

theorem uneven_ne {a b c d : Poll} (ha : a.label = b.label) (hc : c.label = b.label)
    (other : d.label ≠ b.label) :
    ¬ WithGuardedTablePacking.WithPhaseUniformity.Eqv false [State]
      ((Table.unevenWith a.program b.program c.program d.program).entered 5)
      ((Table.cycle3 a.program b.program c.program).entered 1) [Bit] := by
  intro e
  have mem := repeat_return (Table.unevenWith a.program b.program c.program d.program) 5 b d rfl rfl
    false false false
  rw [observations_of_eqv e false] at mem
  have progs : ∀ i, (Table.cycle3 a.program b.program c.program).prog i = (cyclePolls a b c i).program := by
    intro i
    match i with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
  have same : ∀ i, (cyclePolls a b c i).label = b.label := by
    intro i
    match i with
    | 0 => exact ha
    | 1 => rfl
    | 2 => exact hc
  have all := labels (Table.cycle3 a.program b.program c.program) (cyclePolls a b c) b.label progs same
    1 false mem
  exact other (all (event d.label false (d.returnRight, false)) (by simp))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.TableModel
