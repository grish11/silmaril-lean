module

public import Silmaril.Machine.MulticoreVM.Synchronized.Physical.Defs

public section

namespace Silmaril.Proofs.Machine.MulticoreVM.Synchronized.Physical

open Silmaril.Machine.MulticoreVM.Synchronized
open Silmaril.Machine.MulticoreVM.Synchronized.Physical

theorem instruction_refines {CoreId : Type} [DecidableEq CoreId] (memoryCore : CoreId) :
    (instruction memoryCore).RefinesBy (view memoryCore) step := by
  intro _ thread choice initial fragment next _ h
  obtain ⟨words, nextWords, before, executed, writes⟩ := h
  have after : next.cores memoryCore = some nextWords := by rw [writes, Function.update_self]
  simpa only [view, before, after, Option.getD_some, step, Silmaril.Machine.MulticoreVM.ofExecutor]
    using executed

end Silmaril.Proofs.Machine.MulticoreVM.Synchronized.Physical
