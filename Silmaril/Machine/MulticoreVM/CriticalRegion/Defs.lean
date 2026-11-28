module

public import Silmaril.Machine.MulticoreVM.Defs

/-! # A single dispatcher with flat critical regions -/

@[expose] public section

namespace Silmaril.Machine.MulticoreVM.CriticalRegion

universe u

/-- The model supplies the state, ordinary instructions and effects, and the
continuation updates for the two control instructions. -/
structure Program (State Thread Instruction Event : Type u) where
  atomic : Transition State Thread Instruction Event
  enter : Thread → State → State → Prop
  leave : Thread → State → State → Prop
  finished : Thread → State → Prop

structure Config (State Thread : Type u) where
  vm : State
  owner : Option Thread

def Config.start {State Thread : Type u} (vm : State) : Config State Thread := ⟨vm, none⟩

inductive Action (Instruction : Type u) where
  | atomic (instruction : Instruction)
  | enter
  | leave

variable {State Thread Instruction Event Abstract : Type u}

/-- Completion requires every thread to have finished and the region to be free.
A finite prefix can end in any configuration, including a finished but still held region. -/
def Program.Completed (program : Program State Thread Instruction Event)
    (cfg : Config State Thread) : Prop :=
  cfg.owner = none ∧ ∀ thread, program.finished thread cfg.vm

/-- Outside a region any enabled thread can act. In a held region only the owner
can act. Enter and leave are flat and emit no instruction effects. -/
inductive Step (program : Program State Thread Instruction Event) :
    Transition (Config State Thread) Thread (Action Instruction) Event
  | atomic {thread instruction state owner fragment next} :
      (owner = none ∨ owner = some thread) →
      ¬ program.finished thread state → program.atomic thread instruction state fragment next →
      Step program thread (.atomic instruction) ⟨state, owner⟩ fragment ⟨next, owner⟩
  | enter {thread state next} :
      ¬ program.finished thread state → program.enter thread state next →
      Step program thread .enter ⟨state, none⟩ [] ⟨next, some thread⟩
  | leave {thread state next} :
      ¬ program.finished thread state → program.leave thread state next →
      Step program thread .leave ⟨state, some thread⟩ [] ⟨next, none⟩

/-- The decision log records control instructions independently of the effect word.
Erasure removes only controls, even when an ordinary instruction has an empty fragment. -/
def atomicSchedule : Schedule Thread (Action Instruction) → Schedule Thread Instruction
  | [] => []
  | ⟨thread, .atomic instruction⟩ :: tail => ⟨thread, instruction⟩ :: atomicSchedule tail
  | _ :: tail => atomicSchedule tail

/-- Both control updates must stutter after projection. This permits, for example,
a concrete program counter to move past an enter or leave without an abstract step. -/
structure Program.Refines (program : Program State Thread Instruction Event)
    (view : State → Abstract) (step : Transition Abstract Thread Instruction Event) : Prop where
  atomic : ∀ {thread instruction state fragment next},
    program.atomic thread instruction state fragment next →
      step thread instruction (view state) fragment (view next)
  enter_preserves : ∀ {thread state next}, program.enter thread state next → view next = view state
  leave_preserves : ∀ {thread state next}, program.leave thread state next → view next = view state

/-- Interpret exactly the transitions of the arbitrary atomic VM. -/
def regionFree (step : Transition State Thread Instruction Event) :
    Program State Thread Instruction Event where
  atomic := step
  enter _ _ _ := False
  leave _ _ _ := False
  finished _ _ := False

def liftSchedule (schedule : Schedule Thread Instruction) : Schedule Thread (Action Instruction) :=
  schedule.map fun decision => ⟨decision.thread, .atomic decision.choice⟩

/-- Observe the projected final state and chronological effects of finite prefixes,
indexed by instruction count. -/
def observedOutcomes (program : Program State Thread Instruction Event) (view : State → Abstract)
    (initial : Config State Thread) (n : Nat) : Set (Outcome Abstract Thread Event) :=
  { p | ∃ moves final, (atomicSchedule moves).length = n ∧
      Scheduled (Step program) moves initial p.2 final ∧ view final.vm = p.1 }

end Silmaril.Machine.MulticoreVM.CriticalRegion
