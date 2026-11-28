module

public import Silmaril.Machine.MulticoreVM.ThreadSync.Legacy.Thms

namespace Silmaril.Machine.MulticoreVM.ThreadSync.Legacy

open Silmaril.Semantics.ConcurrentTrace (Word)

private def initial : Toy.Config :=
  Toy.put (Toy.init 0 ⟨2, [.add 3, .emit]⟩) 1 ⟨9, [.emit]⟩

private def final : Toy.Config :=
  Toy.put (Toy.put initial 0 ⟨5, []⟩) 1 ⟨9, []⟩

private def schedule : Schedule Toy.ThreadId PUnit :=
  [⟨0, ⟨⟩⟩, ⟨1, ⟨⟩⟩, ⟨0, ⟨⟩⟩]

private def word : Word Toy.ThreadId Nat := [.event 1 9, .event 0 5]

-- The add consumes a decision and emits nothing. Both emits retain their owners and order.
private theorem toyRun : execute Toy.exec (toySchedule schedule) initial = some (final, word) := by
  simp [execute, Toy.exec, toySchedule, schedule, initial, final, word, Toy.put, Toy.init, nameFragment]
  funext thread
  by_cases atZero : thread = 0 <;> simp [Toy.put, atZero]

example (words : Nat → Nat) :
    execute (ThreadSync.exec (liftProgram toyLocal)) (liftSchedule schedule) (liftStore words initial) =
      some (liftStore words final, [.event 1 (.localOutput 9), .event 0 (.localOutput 5)]) := by
  rw [execute_toy, toyRun]
  rfl

-- A later decision for a finished core rejects the whole schedule on both sides.
example (words : Nat → Nat) :
    execute (ThreadSync.exec (liftProgram toyLocal))
      (liftSchedule (schedule ++ [⟨0, ⟨⟩⟩])) (liftStore words initial) = none := by
  rw [execute_toy]
  rfl

end Silmaril.Machine.MulticoreVM.ThreadSync.Legacy
