module

public import Silmaril.Machine.MulticoreVM.Placed.Defs

@[expose] public section

namespace Silmaril.Machine.MulticoreVM.Placed

universe u

variable {CoreId ThreadId Core Thread Choice Event State : Type u}

/-- A state observation may read both stores, which C8 placement commands preserve. -/
abbrev StoreView (CoreId ThreadId Core Thread State : Type u) :=
  (CoreId → Option Core) → (ThreadId → Option Thread) → State

/-- The instruction obligation for an abstract state obtained from the two stores. -/
def Instruction.RefinesBy (instruction : Instruction CoreId ThreadId Core Thread Choice Event)
    (view : StoreView CoreId ThreadId Core Thread State) (step : Transition State ThreadId Choice Event) :
    Prop :=
  ∀ ⦃core thread choice initial fragment next⦄, initial.placement core = some thread →
    instruction core thread choice initial fragment next →
    step thread choice (view initial.cores initial.threads) fragment (view next.cores next.threads)

end Silmaril.Machine.MulticoreVM.Placed
