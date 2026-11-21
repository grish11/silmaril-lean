module

import Silmaril.Semantics.Operational.Policy.Thms

open Silmaril.Semantics.Operational

private inductive Cell where
  | write (value : Nat)
  | read (stored : Option Nat)
  | done (value : Nat)
  | trapped
  | waiting

private def cell : WithUB Cell Nat := .ofOpSem {
  step := fun source target => match source with
    | .write value => target = .read (some value)
    | .read (.some value) => target = .done value
    | .read .none => target = .trapped
    | _ => False
  observe := fun source outcome => match source with
    | .done value => outcome = .returned value
    | .trapped => outcome = .trap
    | _ => False }

private def fits : Cell → Prop
  | .read (.some value) => value < 4
  | _ => True

private def bounded := cell.enforce fits

example : ¬ cell.UBReachable (.write 92) := WithUB.ofOpSem_safe _ _

example (value : Nat) (outside : 4 ≤ value) : bounded.UBReachable (.write value) :=
  ⟨.read (some value), .single ⟨trivial, rfl⟩, .inr (Nat.not_lt_of_ge outside)⟩

example : bounded.toOpSem.May (.write 2) (.returned 2) := by
  have first : bounded.step (.write 2) (.read (some 2)) := ⟨trivial, rfl⟩
  have second : bounded.step (.read (some 2)) (.done 2) := ⟨by change 2 < 4; decide +kernel, rfl⟩
  exact ⟨.done 2, (Relation.ReflTransGen.single first).tail second, trivial, rfl⟩

example : bounded.toOpSem.TrapReachable (.read none) :=
  ⟨.trapped, .single ⟨trivial, rfl⟩, trivial, rfl⟩

example : ¬ cell.toOpSem.Diverges .waiting :=
  OpSem.Normal.not_diverges (sem := cell.toOpSem) (source := .waiting) (fun _ impossible => impossible)

example : (bounded.lift Option.some).ub none ∧
    ∀ outcome, ¬ (bounded.lift Option.some).toOpSem.May none outcome := by
  have outside : ¬ ∃ left : Cell, some left = none := by simp
  have result := WithUB.lift_outside (sem := bounded) outside
  exact ⟨result.1, result.2.2⟩

example : (bounded.lift Option.some).toOpSem.May (some (.write 2)) (.returned 2) ↔
    bounded.toOpSem.May (.write 2) (.returned 2) := WithUB.lift_may_iff (fun _ _ => Option.some.inj)

private def eraseRead : Cell → Option Cell
  | .read _ => none
  | state => some state

example : (cell.push eraseRead).toOpSem.May (some (.write 2)) (.returned 92) := by
  let pushed := cell.push eraseRead
  have first : pushed.step (some (.write 2)) none := ⟨.write 2, .read (some 2), rfl, rfl, rfl⟩
  have second : pushed.step none (some (.done 92)) := ⟨.read (some 92), .done 92, rfl, rfl, rfl⟩
  exact ⟨some (.done 92), (Relation.ReflTransGen.single first).tail second, .done 92, rfl, rfl⟩

example : ¬ cell.Compatible eraseRead := by
  intro compatible
  obtain ⟨next, step, equal⟩ := compatible.step (left := .read (some 1)) (source := .read (some 2))
    (target := .done 1) rfl rfl
  change next = .done 2 at step
  subst next
  cases equal

#print axioms WithUB.AgreeWhenSafe.may_iff
#print axioms OpSim.trans
#print axioms WithUB.Included.antisymm
#print axioms WithUB.enforce_safe_iff
#print axioms WithUB.Compatible.push_diverges_iff
#print axioms WithUB.lift_may_iff
#print axioms WithUB.lift_safe_iff
#print axioms WithUB.restrict_readback
