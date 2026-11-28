module

public import Silmaril.Machine.MulticoreVM.Scheduler.Defs
public import Silmaril.Machine.MulticoreVM.Placed.StoreProjection.Defs
public import Silmaril.Machine.MulticoreVM.Synchronized.Defs

/-! # Physical instantiation of the synchronized register VM -/

@[expose] public section

namespace Silmaril.Machine.MulticoreVM.Synchronized.Physical

abbrev Config (CoreId : Type) := Placed.Config CoreId ThreadId Shared Slot

/-- The distinguished configured slot backs the shared word map. Every executing
core accesses that same map, regardless of where the active thread resides. -/
def view {CoreId : Type} (memoryCore : CoreId) :
    Placed.StoreView CoreId ThreadId Shared Slot Synchronized.Config :=
  fun cores threads => ⟨(cores memoryCore).getD (fun _ => 0), threads⟩

def lifecycle : Scheduler.Lifecycle ThreadId Slot Choice Event where
  runnable := Runnable
  releases _ _ _ fragment _ := fragment = [.event .yield]

/-- Run an instruction against the shared words and write back only the backing
slot. The scheduler around this relation checks residence and updates placement. -/
def instruction {CoreId : Type} [DecidableEq CoreId] (memoryCore : CoreId) :
    Placed.Instruction CoreId ThreadId Shared Slot Choice Event :=
  fun _ thread choice initial fragment next =>
    ∃ words nextWords, initial.cores memoryCore = some words ∧
      Synchronized.exec thread choice ⟨words, initial.threads⟩ = some (⟨nextWords, next.threads⟩, fragment) ∧
      next.cores = Function.update initial.cores memoryCore (some nextWords)

abbrev Scheduled {CoreId : Type} [DecidableEq CoreId] (memoryCore : CoreId)
    (cores : Scheduler.CorePolicy CoreId ThreadId Shared Slot)
    (threads : Scheduler.ThreadPolicy CoreId ThreadId Shared Slot) :=
  Scheduler.Scheduled cores threads lifecycle (instruction memoryCore)

end Silmaril.Machine.MulticoreVM.Synchronized.Physical
