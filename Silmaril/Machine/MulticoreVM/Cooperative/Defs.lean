module

public import Silmaril.Machine.MulticoreVM.Defs

/-! # A single yield-only cooperative dispatcher -/

@[expose] public section

namespace Silmaril.Machine.MulticoreVM.Cooperative

universe u

/-- Ordinary instructions and the program's explicit yield instruction.
`finished` identifies program completion. It is independent of whether an ordinary
transition happens to be available. -/
structure Program (State Thread Choice Event : Type u) where
  atomic : Transition State Thread Choice Event
  yieldTo : Thread → State → State → Prop
  finished : Thread → State → Prop

/-- An idle dispatcher can select a policy-approved thread that can take an instruction. -/
abbrev DispatchPolicy (State Thread : Type u) := State → Thread → Prop

def anyDispatch {State Thread : Type u} : DispatchPolicy State Thread := fun _ _ => True

structure Config (State Thread : Type u) where
  vm : State
  owner : Option Thread

/-- The initial dispatcher is idle. An empty run leaves it idle. -/
def Config.start {State Thread : Type u} (vm : State) : Config State Thread := ⟨vm, none⟩

/-- The thread ID is carried by the enclosing scheduler decision.
`complete` is runtime bookkeeping for a finished owner. -/
inductive Action (Choice : Type u) where
  | dispatch
  | atomic (choice : Choice)
  | yield
  | complete

variable {State Thread Choice Event Abstract : Type u}

def Program.Runnable (program : Program State Thread Choice Event) (thread : Thread)
    (state : State) : Prop :=
  ¬ program.finished thread state ∧
    ((∃ choice fragment next, program.atomic thread choice state fragment next) ∨
      ∃ next, program.yieldTo thread state next)

/-- Ordinary instructions retain the owner, including the last ordinary instruction.
Only a program yield or retirement of a finished owner releases it. Dispatch, yield,
and retirement are recorded in the schedule and emit no letters. -/
inductive Step (program : Program State Thread Choice Event)
    (policy : DispatchPolicy State Thread) :
    Transition (Config State Thread) Thread (Action Choice) Event
  | dispatch {thread state} :
      policy state thread → program.Runnable thread state →
      Step program policy thread .dispatch ⟨state, none⟩ [] ⟨state, some thread⟩
  | atomic {thread choice state fragment next} :
      ¬ program.finished thread state → program.atomic thread choice state fragment next →
      Step program policy thread (.atomic choice) ⟨state, some thread⟩ fragment ⟨next, some thread⟩
  | yield {thread state next} :
      ¬ program.finished thread state → program.yieldTo thread state next →
      Step program policy thread .yield ⟨state, some thread⟩ [] ⟨next, none⟩
  | complete {thread state} :
      program.finished thread state →
      Step program policy thread .complete ⟨state, some thread⟩ [] ⟨state, none⟩

/-- Erase administrative decisions while retaining every atomic step, including silent ones. -/
def atomicSchedule : Schedule Thread (Action Choice) → Schedule Thread Choice
  | [] => []
  | ⟨thread, .atomic choice⟩ :: tail => ⟨thread, choice⟩ :: atomicSchedule tail
  | _ :: tail => atomicSchedule tail

/-- Each ordinary step must simulate the same named atomic step under the state view.
A yield can update program control, provided the state view hides that update. -/
structure Program.Refines (program : Program State Thread Choice Event) (view : State → Abstract)
    (step : Transition Abstract Thread Choice Event) : Prop where
  atomic : ∀ {thread choice state fragment next}, program.atomic thread choice state fragment next →
    step thread choice (view state) fragment (view next)
  yield_preserves : ∀ {thread state next}, program.yieldTo thread state next → view next = view state

/-- Require a synthetic yield after each atomic instruction. The Boolean records a pending
yield, which is enabled even when the atomic instruction exhausted the underlying program.
Start with `Config.start (state, false)`. An atomic step is the only instruction that can
start a dispatch from this state. Underlying exhaustion means there is no dispatch for that
thread after the pending yield is consumed. -/
def everyAtomic (step : Transition State Thread Choice Event) :
    Program (State × Bool) Thread Choice Event where
  atomic thread choice state fragment next :=
    state.2 = false ∧ next.2 = true ∧ step thread choice state.1 fragment next.1
  yieldTo _ state next := state.2 = true ∧ next = (state.1, false)
  finished _ _ := False

/-- A canonical finite lift, including the final synthetic yield. -/
def instrument : Schedule Thread Choice → Schedule Thread (Action Choice)
  | [] => []
  | decision :: tail =>
      ⟨decision.thread, .dispatch⟩ :: ⟨decision.thread, .atomic decision.choice⟩ ::
        ⟨decision.thread, .yield⟩ :: instrument tail

/-- Finite cooperative outcomes indexed by the number of atomic steps. The final owner
and any program-control state hidden by `view` are omitted from the observation. -/
def observedOutcomes (program : Program State Thread Choice Event)
    (policy : DispatchPolicy State Thread) (view : State → Abstract)
    (initial : Config State Thread) (n : Nat) : Set (Outcome Abstract Thread Event) :=
  { p | ∃ moves final, (atomicSchedule moves).length = n ∧
      Scheduled (Step program policy) moves initial p.2 final ∧ view final.vm = p.1 }

end Silmaril.Machine.MulticoreVM.Cooperative
