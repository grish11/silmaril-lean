module

public import Silmaril.Machine.MulticoreVM.Placed.Defs

/-! # Physical core selection and thread dispatch -/

@[expose] public section

namespace Silmaril.Machine.MulticoreVM.Scheduler

universe u

variable {CoreId ThreadId Core Thread Choice Event : Type u}

abbrev Config (CoreId ThreadId Core Thread : Type u) := Placed.Config CoreId ThreadId Core Thread
abbrev Store (ThreadId Thread : Type u) := ThreadId → Option Thread

/-- A core policy grants an opportunity to a physical slot, including an idle slot. -/
abbrev CorePolicy (CoreId ThreadId Core Thread : Type u) :=
  Config CoreId ThreadId Core Thread → CoreId → Prop

/-- Selection requires a present core and leaves the whole machine unchanged. -/
def CorePolicy.Selects (policy : CorePolicy CoreId ThreadId Core Thread)
    (initial : Config CoreId ThreadId Core Thread) (core : CoreId)
    (next : Config CoreId ThreadId Core Thread) : Prop :=
  policy initial core ∧ (initial.cores core).isSome ∧ next = initial

/-- A decision for the selected core. Assignment may displace its resident; migration
moves a resident from another core onto a selected idle core. -/
inductive Dispatch (CoreId ThreadId : Type u) where
  | idle
  | keep (thread : ThreadId)
  | assign (thread : ThreadId)
  | migrate (source : CoreId) (thread : ThreadId)

def Dispatch.thread : Dispatch CoreId ThreadId → Option ThreadId
  | .idle => none
  | .keep thread | .assign thread | .migrate _ thread => some thread

/-- A policy for what to do on the core already selected. -/
abbrev ThreadPolicy (CoreId ThreadId Core Thread : Type u) :=
  Config CoreId ThreadId Core Thread → CoreId → Dispatch CoreId ThreadId → Prop

/-- A thread is eligible when it is allocated and its local state is runnable. -/
def Eligible (runnable : ThreadId → Thread → Prop) (threads : Store ThreadId Thread)
    (thread : ThreadId) : Prop :=
  ∃ localState, threads thread = some localState ∧ runnable thread localState

/-- The legal placement operations for a dispatch. Their successor configurations
carry C8's endpoint and uniqueness certificates. -/
inductive Places [DecidableEq CoreId] (core : CoreId) (initial : Config CoreId ThreadId Core Thread) :
    Dispatch CoreId ThreadId → Config CoreId ThreadId Core Thread → Prop
  | idle {next} :
      initial.ReplacesPlacement next (Function.update initial.placement core none) →
      Places core initial .idle next
  | keep {thread} : initial.placement core = some thread →
      Places core initial (.keep thread) initial
  | assign {thread next} : (∀ c, initial.placement c ≠ some thread) →
      initial.ReplacesPlacement next (Function.update initial.placement core (some thread)) →
      Places core initial (.assign thread) next
  | migrate {source thread next} :
      initial.placement source = some thread → initial.placement core = none →
      initial.ReplacesPlacement next
        (Function.update (Function.update initial.placement source none) core (some thread)) →
      Places core initial (.migrate source thread) next

/-- A successful dispatch obeys the thread policy, uses a present core, checks
runnability for every chosen thread, and realizes a legal placement. -/
def ThreadPolicy.Schedules [DecidableEq CoreId] (policy : ThreadPolicy CoreId ThreadId Core Thread)
    (runnable : ThreadId → Thread → Prop) (core : CoreId) (dispatch : Dispatch CoreId ThreadId)
    (initial next : Config CoreId ThreadId Core Thread) : Prop :=
  policy initial core dispatch ∧ (initial.cores core).isSome ∧
    (∀ ⦃thread⦄, dispatch.thread = some thread → Eligible runnable initial.threads thread) ∧
    Places core initial dispatch next

/-- The VM identifies runnable local states and instructions that voluntarily release
the slot. The release rule can inspect the actual transition and its result. -/
structure Lifecycle (ThreadId Thread Choice Event : Type u) where
  runnable : ThreadId → Thread → Prop
  releases : ThreadId → Choice → Store ThreadId Thread → Fragment ThreadId Event →
    Store ThreadId Thread → Prop

/-- Release on voluntary relinquishment or when the current thread ceases to be runnable. -/
def Lifecycle.ReleasesSlot (life : Lifecycle ThreadId Thread Choice Event) (thread : ThreadId)
    (choice : Choice) (initial : Store ThreadId Thread) (fragment : Fragment ThreadId Event)
    (next : Store ThreadId Thread) : Prop :=
  life.releases thread choice initial fragment next ∨ ¬ Eligible life.runnable next thread

/-- Enforce the lifecycle on a C8 instruction. The executing thread must start runnable.
On release only its slot is cleared, otherwise placement stays as it was. -/
def Lifecycle.instruction [DecidableEq CoreId] (life : Lifecycle ThreadId Thread Choice Event)
    (instruction : Placed.Instruction CoreId ThreadId Core Thread Choice Event) :
    Placed.Instruction CoreId ThreadId Core Thread Choice Event :=
  fun core thread choice initial fragment next =>
    Eligible life.runnable initial.threads thread ∧
    instruction core thread choice initial fragment next ∧
    (let release := life.ReleasesSlot thread choice initial.threads fragment next.threads
     (release → next.placement = Function.update initial.placement core none) ∧
     (¬ release → next.placement = initial.placement))

/-- An advance executes one instruction on the selected core after dispatch. -/
abbrev Advance [DecidableEq CoreId] (life : Lifecycle ThreadId Thread Choice Event)
    (instruction : Placed.Instruction CoreId ThreadId Core Thread Choice Event)
    (core : CoreId) (thread : ThreadId) (choice : Choice)
    (initial : Config CoreId ThreadId Core Thread) (word : Placed.TaggedWord CoreId ThreadId Event)
    (next : Config CoreId ThreadId Core Thread) : Prop :=
  Placed.Step (life.instruction instruction) (.execute core thread choice) initial word next

/-- The C8 placement commands for a dispatch. Keeping the resident leaves C8 untouched. -/
def Dispatch.placedActions (core : CoreId) :
    Dispatch CoreId ThreadId → Placed.Schedule CoreId ThreadId Choice
  | .idle => [.idle core]
  | .keep _ => []
  | .assign thread => [.assign core thread]
  | .migrate source _ => [.migrate source core]

/-- A schedule records which policies' decisions were taken and whether an instruction
was attempted in that opportunity. Each decision is validated at its own stage. -/
structure Turn (CoreId ThreadId Choice : Type u) where
  core : CoreId
  dispatch : Dispatch CoreId ThreadId
  choice : Option Choice

def Turn.placedActions (turn : Turn CoreId ThreadId Choice) : Placed.Schedule CoreId ThreadId Choice :=
  turn.dispatch.placedActions turn.core ++
    match turn.dispatch.thread, turn.choice with
    | some thread, some choice => [.execute turn.core thread choice]
    | _, _ => []

/-- One core opportunity and dispatch, with either a scheduling-only outcome or
one machine advance. The instruction runs in the successor of thread dispatch. -/
inductive Round [DecidableEq CoreId] (cores : CorePolicy CoreId ThreadId Core Thread)
    (threads : ThreadPolicy CoreId ThreadId Core Thread) (life : Lifecycle ThreadId Thread Choice Event)
    (instruction : Placed.Instruction CoreId ThreadId Core Thread Choice Event) :
    Turn CoreId ThreadId Choice → Config CoreId ThreadId Core Thread →
      Placed.TaggedWord CoreId ThreadId Event → Config CoreId ThreadId Core Thread → Prop
  | place {core dispatch initial selected next} :
      cores.Selects initial core selected →
      threads.Schedules life.runnable core dispatch selected next →
      Round cores threads life instruction ⟨core, dispatch, none⟩ initial [] next
  | execute {core dispatch thread choice initial selected placed word next} :
      cores.Selects initial core selected →
      threads.Schedules life.runnable core dispatch selected placed →
      dispatch.thread = some thread →
      Advance life instruction core thread choice placed word next →
      Round cores threads life instruction ⟨core, dispatch, some choice⟩ initial word next

/-- Successful finite prefixes, including prefixes that end after placement. -/
inductive Scheduled [DecidableEq CoreId] (cores : CorePolicy CoreId ThreadId Core Thread)
    (threads : ThreadPolicy CoreId ThreadId Core Thread) (life : Lifecycle ThreadId Thread Choice Event)
    (instruction : Placed.Instruction CoreId ThreadId Core Thread Choice Event) :
    List (Turn CoreId ThreadId Choice) → Config CoreId ThreadId Core Thread →
      Placed.TaggedWord CoreId ThreadId Event → Config CoreId ThreadId Core Thread → Prop
  | nil (cfg) : Scheduled cores threads life instruction [] cfg [] cfg
  | cons {turn schedule initial word next tail final} :
      Round cores threads life instruction turn initial word next →
      Scheduled cores threads life instruction schedule next tail final →
      Scheduled cores threads life instruction (turn :: schedule) initial (word ++ tail) final

/-- The abstract schedule keeps every instruction, including silent yields and waits. -/
def threadSchedule (schedule : List (Turn CoreId ThreadId Choice)) :
    MulticoreVM.Schedule ThreadId Choice :=
  Placed.threadSchedule (schedule.flatMap Turn.placedActions)

end Silmaril.Machine.MulticoreVM.Scheduler
