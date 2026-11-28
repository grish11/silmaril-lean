module

public import Silmaril.Machine.MulticoreVM.Cooperative.Defs
public import Silmaril.Machine.MulticoreVM.ThreadSync.Defs
import Silmaril.Proofs.Machine.MulticoreVM.Cooperative.ThreadSync

public section

namespace Silmaril.Machine.MulticoreVM.Cooperative

universe u

variable {Thread Key Value Local Output Choice Event : Type u}
variable [DecidableEq Thread] [DecidableEq Key] [DecidableEq Value]
variable {keyed : ThreadSync.Program Thread Key Value Local Output}
variable {cfg next : ThreadSync.Config Thread Key Value Local} {thread : Thread}
variable {program : Program (ThreadSync.Config Thread Key Value Local) Thread Choice Event}
variable {policy : DispatchPolicy (ThreadSync.Config Thread Key Value Local) Thread}

/-- An already-dispatched live owner has the same yield transition when the cooperative
program delegates that instruction to ThreadSync. Both sides commit its continuation and
release dispatch. The generic schedule records the yield with an empty fragment, while
ThreadSync emits the yield marker in its fragment. -/
theorem threadSync_owned_yield_iff
    (live : ¬ program.finished thread cfg)
    (yieldStep : program.yieldTo thread cfg next ↔
      ThreadSync.step keyed thread [] cfg [.event .yield] next) :
    Step program policy thread .yield ⟨cfg, some thread⟩ [] ⟨next, none⟩ ↔
      ThreadSync.cooperativeStep keyed thread [] ⟨cfg, some thread⟩
        [.event .yield] ⟨next, none⟩ :=
  Proofs.Machine.MulticoreVM.Cooperative.threadSync_owned_yield_iff live yieldStep

end Silmaril.Machine.MulticoreVM.Cooperative
