module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Defs

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Proofs

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.RTL.SSA
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (Reg)

/-- A returning machine run must have enough fuel for any known running prefix. -/
theorem run_after_prefix {program : Prog Reg} {steps : Nat} {s finish : State Reg}
    (prefixPath : StepsNWithin program [] steps s finish) {fuel : Nat} {returned : List Word} {final : Memory}
    (observed : run program fuel s = .returned returned final) :
    ∃ remaining, fuel = steps + remaining ∧ run program remaining finish = .returned returned final := by
  induction prefixPath generalizing fuel with
  | refl => exact ⟨fuel, (Nat.zero_add fuel).symm, observed⟩
  | @head n s u t move path ih =>
    cases fuel with
    | zero => cases observed
    | succ fuel =>
      have stepEq : step program s = .running u := move.1
      rw [run, stepEq] at observed
      have suffix : run program fuel u = .returned returned final := observed
      obtain ⟨remaining, length, result⟩ := ih suffix
      exact ⟨remaining, by omega, result⟩

theorem fuel_of_steps {program : Prog Reg} {s finish : State Reg}
    (path : Steps program s finish) {returned : List Word} {final : Memory}
    (observed : step program finish = .returned returned final) :
    ∃ fuel, run program fuel s = .returned returned final := by
  induction path using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨1, by simp [run, observed]⟩
  | @head a c move _ ih =>
    obtain ⟨fuel, result⟩ := ih
    have stepEq : step program a = .running c := move
    exact ⟨fuel + 1, by rw [run, stepEq]; exact result⟩

theorem run_through_prefix {program : Prog Reg} {steps : Nat} {s finish : State Reg}
    (path : StepsNWithin program [] steps s finish) (remaining : Nat) :
    run program (steps + remaining) s = run program remaining finish := by
  induction path with
  | refl => simp
  | @head n s u t move path ih =>
    have stepEq : step program s = .running u := move.1
    rw [show n + 1 + remaining = (n + remaining) + 1 by omega, run, stepEq]
    exact ih

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Proofs
