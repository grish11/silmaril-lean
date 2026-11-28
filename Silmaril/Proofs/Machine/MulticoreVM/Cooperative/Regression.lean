module

import Silmaril.Machine.MulticoreVM.Cooperative.Thms

namespace Silmaril.Proofs.Machine.MulticoreVM.Cooperative.Regression

open Silmaril.Machine.MulticoreVM
open Silmaril.Machine.MulticoreVM.Cooperative
open Silmaril.Semantics.ConcurrentTrace (Word)

private def atomicStep : Transition Nat Bool Unit Nat :=
  ofExecutor fun thread _ state =>
    match thread, state with
    | false, 0 => some (1, [.event 7])
    | true, 1 => some (2, [])
    | true, 2 => some (3, [.event 9])
    | false, 3 => some (4, [.sync [false, true], .event 11])
    | _, _ => none

private def program : Program Nat Bool Unit Nat where
  atomic := atomicStep
  yieldTo thread state next := thread = false ∧ state = 1 ∧ next = 1
  finished _ state := state = 4

private def mixed : Schedule Bool Unit :=
  [⟨false, ()⟩, ⟨true, ()⟩, ⟨true, ()⟩, ⟨false, ()⟩]

private def output : Word Bool Nat :=
  [.event false 7, .event true 9, .sync [false, true], .event false 11]

private theorem mixed_atomic : Scheduled atomicStep mixed 0 output 4 := by
  refine .cons (next := 1) (fragment := [.event 7]) rfl ?_
  refine .cons (next := 2) (fragment := []) rfl ?_
  refine .cons (next := 3) (fragment := [.event 9]) rfl ?_
  exact .cons (fragment := [.sync [false, true], .event 11]) rfl (.nil 4)

-- Both atomic actions are available in order under the arbitrary scheduler.
example : Scheduled atomicStep [⟨false, ()⟩, ⟨true, ()⟩] 0 [.event false 7] 2 :=
  .cons (next := 1) (fragment := [.event 7]) rfl (.cons (fragment := []) rfl (.nil 2))

-- The first ordinary action retains ownership, so a dispatch to the second thread fails.
example : ¬ ∃ word final, Scheduled (Step program anyDispatch)
    [⟨false, .dispatch⟩, ⟨false, .atomic ()⟩, ⟨true, .dispatch⟩, ⟨true, .atomic ()⟩]
    (Config.start 0) word final := by
  rintro ⟨_, _, path⟩
  cases path with
  | cons first rest =>
    cases first
    cases rest with
    | cons first rest =>
      cases first
      cases rest with
      | cons first _ => cases first

-- Completion cannot be used as a substitute for yield while that thread is unfinished.
example : ¬ Step program anyDispatch false .complete ⟨1, some false⟩ [] (Config.start 1) := by
  intro h
  cases h with
  | complete finished => cases (show 1 = 4 from finished)

example : Scheduled (Step program anyDispatch)
    [⟨false, .dispatch⟩, ⟨false, .atomic ()⟩, ⟨false, .yield⟩,
      ⟨true, .dispatch⟩, ⟨true, .atomic ()⟩]
    (Config.start 0) [.event false 7] ⟨2, some true⟩ := by
  have live0 : ¬ program.finished false 0 := show (0 : Nat) ≠ 4 by decide
  have live1 (thread : Bool) : ¬ program.finished thread 1 := show (1 : Nat) ≠ 4 by decide
  refine Scheduled.cons (decision := ⟨false, Action.dispatch⟩)
    (Step.dispatch trivial ⟨live0, Or.inl ⟨(), [.event 7], 1, rfl⟩⟩) ?_
  refine Scheduled.cons (decision := ⟨false, Action.atomic ()⟩)
    (Step.atomic (fragment := [.event 7]) (next := 1) live0 rfl) ?_
  refine Scheduled.cons (decision := ⟨false, Action.yield⟩)
    (Step.yield (next := 1) (live1 false) ⟨rfl, rfl, rfl⟩) ?_
  refine Scheduled.cons (decision := ⟨true, Action.dispatch⟩)
    (Step.dispatch trivial ⟨live1 true, Or.inl ⟨(), [], 2, rfl⟩⟩) ?_
  exact Scheduled.cons (decision := ⟨true, Action.atomic ()⟩)
    (Step.atomic (fragment := []) (next := 2) (live1 true) rfl) (.nil _)

-- Retirement of a finished owner is distinct from its final atomic instruction.
example : Step program anyDispatch false .complete ⟨4, some false⟩ [] (Config.start 4) :=
  .complete rfl

-- The canonical lift dispatches both threads, reselects true after a silent step,
-- preserves the sync participants, and consumes a final pending yield at exhaustion.
example : Scheduled (Step (everyAtomic atomicStep) anyDispatch) (instrument mixed)
    (Config.start (0, false)) output (Config.start (4, false)) :=
  scheduled_instrument mixed_atomic

example : Scheduled atomicStep (atomicSchedule (instrument mixed)) 0 output 4 :=
  scheduled_refines (everyAtomic_refines atomicStep) (scheduled_instrument mixed_atomic)

-- The terminal synthetic yield needs no remaining instruction, and there is no dispatch after it.
example (thread : Bool) (next : Config (Nat × Bool) Bool) :
    ¬ Step (everyAtomic atomicStep) anyDispatch thread .dispatch (Config.start (4, false)) [] next := by
  intro h
  cases h with
  | dispatch _ ready =>
    rcases ready.2 with ⟨_, fragment, target, _, _, step⟩ | ⟨_, pending, _⟩
    · cases thread <;> cases (show none = some (target.1, fragment) from step)
    · cases pending

example : Scheduled (Step (everyAtomic atomicStep) anyDispatch) (instrument [])
    (Config.start (4, false)) [] (Config.start (4, false)) :=
  scheduled_instrument (.nil _)

end Silmaril.Proofs.Machine.MulticoreVM.Cooperative.Regression
