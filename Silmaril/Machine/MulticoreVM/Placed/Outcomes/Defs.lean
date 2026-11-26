module

public import Silmaril.Machine.MulticoreVM.Placed.StoreProjection.Defs

@[expose] public section

namespace Silmaril.Machine.MulticoreVM.Placed

open Silmaril.Semantics.ConcurrentTrace (Trace ofWord)

universe u

variable {CoreId ThreadId Core Thread Choice Event : Type u}

abbrev TaggedOutcome (CoreId ThreadId Core Thread Event : Type u) :=
  Config CoreId ThreadId Core Thread × TaggedWord CoreId ThreadId Event

/-- Observe the concurrent thread trace of a tagged chronological word. -/
def threadTrace (word : TaggedWord CoreId ThreadId Event) : Trace ThreadId Event :=
  ofWord (threadWord word)

/-- Project a tagged outcome to the chosen abstract state and the named thread word. -/
def forgetCore {State : Type u} (view : StoreView CoreId ThreadId Core Thread State)
    (outcome : TaggedOutcome CoreId ThreadId Core Thread Event) : Outcome State ThreadId Event :=
  (view outcome.1.cores outcome.1.threads, threadWord outcome.2)

/-- Project a tagged outcome to the chosen abstract state and the concurrent thread trace. -/
def observeThreadQuotient {State : Type u} (view : StoreView CoreId ThreadId Core Thread State)
    (outcome : TaggedOutcome CoreId ThreadId Core Thread Event) : State × Trace ThreadId Event :=
  (view outcome.1.cores outcome.1.threads, threadTrace outcome.2)

/-- The certified final configurations and tagged words of a successful concrete schedule. -/
def taggedOutcomes [DecidableEq CoreId]
    (instruction : Instruction CoreId ThreadId Core Thread Choice Event)
    (schedule : Schedule CoreId ThreadId Choice) (initial : Config CoreId ThreadId Core Thread) :
    Set (TaggedOutcome CoreId ThreadId Core Thread Event) :=
  { outcome | Scheduled instruction schedule initial outcome.2 outcome.1 }

end Silmaril.Machine.MulticoreVM.Placed
