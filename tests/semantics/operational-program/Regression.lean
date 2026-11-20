module

import Silmaril.Semantics.Operational.Program.Thms

open Silmaril.Semantics.Operational

private inductive Stage where
  | start | returned | trapped | fault | bad | inert | loop
  deriving DecidableEq

private def machine : HasOpSem (Option Stage) Stage (Except Nat Bool) where
  initial program state := program = some state
  semantics := {
    step source target := (source = .start ∧ (target = .returned ∨ target = .trapped ∨ target = .fault ∨ target = .bad)) ∨
      (source = .loop ∧ target = .loop)
    observe source outcome := (source = .returned ∧ outcome = .returned (.ok true)) ∨
      (source = .trapped ∧ outcome = .trap) ∨ (source = .fault ∧ outcome = .returned (.error 7))
    ub source := source = .bad }

example : machine.NoEntry none := by simp [HasOpSem.NoEntry, machine]
example : machine.semantics.Stuck .inert := by
  simp [WithUB.Stuck, OpSem.Normal, machine]
example : machine.semantics.toOpSem.Diverges .loop := ⟨fun _ => .loop, rfl, fun _ => Or.inr ⟨rfl, rfl⟩⟩

private theorem reachesUB : machine.semantics.UBReachable .start :=
  ⟨.bad, .single (Or.inl ⟨rfl, Or.inr (Or.inr (Or.inr rfl))⟩), rfl⟩

example : machine.May (some .start) (.returned (.ok true)) :=
  ⟨.start, rfl, .returned, .single (Or.inl ⟨rfl, Or.inl rfl⟩), Or.inl ⟨rfl, rfl⟩⟩

example : machine.May (some .start) .trap :=
  ⟨.start, rfl, .trapped, .single (Or.inl ⟨rfl, Or.inr (Or.inl rfl)⟩), Or.inr (Or.inl ⟨rfl, rfl⟩)⟩

example : (machine.mapObservations (fun value => value.mapError Nat.succ)).May
    (some .start) (.returned (.error 8)) :=
  (HasOpSem.mapObservations_may_iff _ _).mpr ⟨.returned (.error 7),
    ⟨.start, rfl, .fault, .single (Or.inl ⟨rfl, Or.inr (Or.inr (Or.inl rfl))⟩), Or.inr (Or.inr ⟨rfl, rfl⟩)⟩, rfl⟩

example : ¬ machine.safeFragment.May (some .start) (.returned (.ok true)) := by
  rintro ⟨source, equal, _⟩
  have init : source.val = .start := (Option.some.inj equal).symm
  exact source.property (init ▸ reachesUB)

example : ¬ machine.safeFragment.UBReachable (some .start) := HasOpSem.safeFragment_noUB

#print axioms HasOpSem.refines_of_sim
#print axioms HasOpSem.safeFragment_may_iff
#print axioms HasOpSem.mapObservations_may_iff
#print axioms HasOpSem.equivalent_iff
