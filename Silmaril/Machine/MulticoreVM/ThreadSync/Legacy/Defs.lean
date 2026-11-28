module

public import Silmaril.Machine.MulticoreVM.ThreadSync.Defs
public import Silmaril.Machine.MulticoreVM.Toy.Defs

/-! # The local-step fragment of the pre-synchronization VM -/

@[expose] public section

namespace Silmaril.Machine.MulticoreVM.ThreadSync.Legacy

open Silmaril.Semantics.ConcurrentTrace (LocalLetter Word mapWord)

universe u

variable {Thread Key Value Local Output : Type u}

abbrev Store (Thread Local : Type u) := Thread → Option Local

/-- A deterministic local action can decline to step, or return new local state and at
most one output. It receives only the current thread and its local state. -/
abbrev LocalExec (Thread Local Output : Type u) :=
  Thread → Local → Option (Local × Option Output)

/-- Run a local action through the original VM interface. Only the current slot changes. -/
def exec [DecidableEq Thread] (localExec : LocalExec Thread Local Output)
    (thread : Thread) (_ : PUnit) (store : Store Thread Local) :
    Option (Store Thread Local × Fragment Thread Output) := do
  let localState ← store thread
  let (next, output) ← localExec thread localState
  return (Function.update store thread (some next), output.toList.map LocalLetter.event)

/-- Keep vacant slots vacant and mark every allocated slot runnable. -/
def liftStore (words : Key → Value) (store : Store Thread Local) : Config Thread Key Value Local :=
  ⟨words, fun thread => (store thread).map ThreadState.runnable⟩

/-- Interpret an old local action as a synchronization VM local step. -/
def liftProgram (localExec : LocalExec Thread Local Output) : Program Thread Key Value Local Output :=
  fun thread localState =>
    (localExec thread localState).map fun (next, output) => .localStep next output

/-- Preserve every scheduler decision, supplying an empty wake selection each time. -/
def liftSchedule (schedule : Schedule Thread PUnit) : Schedule Thread (List Thread) :=
  schedule.map fun decision => ⟨decision.thread, []⟩

/-- Preserve chronological order and thread names, wrapping each output in `localOutput`. -/
def liftWord (word : Word Thread Output) : Word Thread (Event Thread Key Value Output) :=
  mapWord id Event.localOutput word

/-- Embed a legacy final store and named word. -/
def liftOutcome (words : Key → Value) (outcome : Outcome (Store Thread Local) Thread Output) :
    Outcome (Config Thread Key Value Local) Thread (Event Thread Key Value Output) :=
  (liftStore words outcome.1, liftWord outcome.2)

/-- Extract a local callback from the existing Toy executor by running with no child choice
on the selected core alone. The correspondence establishes when this agrees with whole-store
execution. -/
def toyLocal : LocalExec Toy.ThreadId Toy.Core Nat := fun thread core => do
  let (next, fragment) ← Toy.exec thread none (Toy.init thread core)
  let nextCore ← next thread
  match fragment with
  | [] => some (nextCore, none)
  | [.event value] => some (nextCore, some value)
  | _ => none

/-- Select the same Toy threads with no child ID on any decision. -/
def toySchedule (schedule : Schedule Toy.ThreadId PUnit) :
    Schedule Toy.ThreadId (Option Toy.ThreadId) :=
  schedule.map fun decision => ⟨decision.thread, none⟩

end Silmaril.Machine.MulticoreVM.ThreadSync.Legacy
