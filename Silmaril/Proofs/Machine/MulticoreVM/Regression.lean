module

public import Silmaril.Machine.MulticoreVM.Toy.Thms
public import Silmaril.Semantics.ConcurrentTrace.Thms

namespace Silmaril.Machine.MulticoreVM.Toy

open Silmaril.Semantics.ConcurrentTrace (Word ofWord)

private def boot : Config := init 0 ⟨1, [.spawn 7 [.add 2, .emit], .emit]⟩

private def childRun (child : ThreadId) : Schedule ThreadId (Option ThreadId) :=
  [⟨0, some child⟩, ⟨child, none⟩, ⟨child, none⟩]

private def finished (child : ThreadId) : Config :=
  put (put boot 0 ⟨1, [.emit]⟩) child ⟨9, []⟩

private def childWord (child : ThreadId) : Word ThreadId Nat :=
  [.sync [0, child], .event child 9]

-- Running the child first fails. The parent cannot reuse an allocated ID.
example : execute exec [⟨1, none⟩, ⟨0, some 1⟩] boot = none := rfl
example : execute exec [⟨0, some 0⟩] boot = none := rfl

private theorem childRun_exec {child : ThreadId} (fresh : child ≠ 0) :
    execute exec (childRun child) boot = some (finished child, childWord child) := by
  simp [childRun, execute, exec, init, boot, put, fresh, finished, childWord, nameFragment]
  funext t
  by_cases h : t = child <;> simp [put, h]

-- Both fresh names are available, with the same selected current thread.
example : execute exec (childRun 1) boot = some (finished 1, childWord 1) := childRun_exec (by decide)
example : execute exec (childRun 2) boot = some (finished 2, childWord 2) := childRun_exec (by decide)

example : finished 1 0 = some ⟨1, [.emit]⟩ ∧ finished 1 1 = some ⟨9, []⟩ :=
  ⟨rfl, rfl⟩

example : (finished 1, childWord 1) ∈ namedOutcomes (run step 3) boot :=
  (mem_run_iff_exists_schedule 3).mpr
    ⟨childRun 1, rfl, (execute_iff_scheduled exec (childRun 1)).mp (childRun_exec (by decide))⟩

-- The participant list keeps the child's output after its creation marker.
example : ofWord (childWord 1) ≠ ofWord ([.event 1 9, .sync [0, 1]] : Word ThreadId Nat) := by
  intro h
  have bad := (Semantics.ConcurrentTrace.swap_eq_iff
    (.sync [0, 1]) (.event (Event := Nat) 1 9)).mp h
  rcases bad with impossible | independent
  · cases impossible
  · cases independent with
    | syncEvent absent => exact absent (by simp)

-- Both emit steps consume instructions and leave different payloads in the chronological word.
example :
    ∃ final,
      execute exec [⟨0, none⟩, ⟨1, none⟩]
          (put (init 0 ⟨4, [.emit]⟩) 1 ⟨9, [.emit]⟩) =
        some (final, [.event 0 4, .event 1 9]) ∧
      execute exec [⟨1, none⟩, ⟨0, none⟩]
          (put (init 0 ⟨4, [.emit]⟩) 1 ⟨9, [.emit]⟩) =
        some (final, [.event 1 9, .event 0 4]) ∧
      ofWord ([.event 0 4, .event 1 9] : Word ThreadId Nat) = ofWord [.event 1 9, .event 0 4] := by
  obtain ⟨final, a, b, equiv⟩ :=
    emit_commutes (put (init 0 ⟨4, [.emit]⟩) 1 ⟨9, [.emit]⟩)
      (a := 0) (b := 1) (by decide) rfl rfl
  exact ⟨final, a, b, (Semantics.ConcurrentTrace.ofWord_eq_iff _ _).mpr equiv⟩

end Silmaril.Machine.MulticoreVM.Toy

namespace Silmaril.Machine.MulticoreVM

private def choose : Transition Bool Unit Unit Unit :=
  fun _ _ _ fragment _ => fragment = []

-- A fixed decision admits two different states with the same silent observation.
example :
    (false, []) ∈ scheduledOutcomes choose [⟨(), ()⟩] false ∧
    (true, []) ∈ scheduledOutcomes choose [⟨(), ()⟩] false := by
  change Scheduled choose [⟨(), ()⟩] false [] false ∧ Scheduled choose [⟨(), ()⟩] false [] true
  exact ⟨.cons (fragment := []) rfl (.nil false), .cons (fragment := []) rfl (.nil true)⟩

end Silmaril.Machine.MulticoreVM
