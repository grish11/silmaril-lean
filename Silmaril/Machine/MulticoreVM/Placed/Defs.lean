module

public import Silmaril.Machine.MulticoreVM.Defs

/-! # Core placement for a current-thread virtual machine -/

@[expose] public section

namespace Silmaril.Machine.MulticoreVM.Placed

open Silmaril.Semantics.ConcurrentTrace (Letter Word)

universe u

variable {CoreId ThreadId Core Thread Choice Event : Type u}

/-- Separate core and thread stores with a partial injection from present cores to allocated
threads. A present core may be idle, and an allocated thread may wait without a core. -/
structure Config (CoreId ThreadId Core Thread : Type u) where
  cores : CoreId → Option Core
  threads : ThreadId → Option Thread
  placement : CoreId → Option ThreadId
  endpoints : ∀ ⦃c t⦄, placement c = some t → (cores c).isSome ∧ (threads t).isSome
  unique : ∀ ⦃c d t⦄, placement c = some t → placement d = some t → c = d

namespace Config

abbrev Resident (cfg : Config CoreId ThreadId Core Thread) :=
  {t : ThreadId // ∃ c, cfg.placement c = some t}

abbrev PresentCore (cfg : Config CoreId ThreadId Core Thread) :=
  {c : CoreId // (cfg.cores c).isSome}

/-- The successor changes only placement. Its `Config` type certifies the resulting placement. -/
def ReplacesPlacement (initial next : Config CoreId ThreadId Core Thread)
    (placement : CoreId → Option ThreadId) : Prop :=
  next.cores = initial.cores ∧ next.threads = initial.threads ∧ next.placement = placement

end Config

/-- A sync records both the executing pair and the original thread participant list. -/
inductive TaggedLetter (CoreId ThreadId Event : Type u) where
  | event (core : CoreId) (thread : ThreadId) (value : Event)
  | sync (core : CoreId) (thread : ThreadId) (participants : List ThreadId)

abbrev TaggedWord (CoreId ThreadId Event : Type u) := List (TaggedLetter CoreId ThreadId Event)

/-- Attribute every letter in an instruction fragment to its executing core and thread. -/
def tagFragment (core : CoreId) (thread : ThreadId) (fragment : Fragment ThreadId Event) :
    TaggedWord CoreId ThreadId Event :=
  fragment.map fun
    | .event value => .event core thread value
    | .sync participants => .sync core thread participants

/-- Recover the thread event or the original sync participant list. -/
def TaggedLetter.dropCore : TaggedLetter CoreId ThreadId Event → Letter ThreadId Event
  | .event _ thread value => .event thread value
  | .sync _ _ participants => .sync participants

/-- Read a sync as an opaque marker on the executing core. `some` carries an ordinary payload,
and `none` marks a sync whose participants are omitted. -/
def TaggedLetter.dropThread : TaggedLetter CoreId ThreadId Event → Letter CoreId (Option Event)
  | .event core _ value => .event core (some value)
  | .sync core _ _ => .event core none

def threadWord (word : TaggedWord CoreId ThreadId Event) : Word ThreadId Event :=
  word.map TaggedLetter.dropCore

def coreWord (word : TaggedWord CoreId ThreadId Event) : Word CoreId (Option Event) :=
  word.map TaggedLetter.dropThread

/-- A scheduled instruction names the executing pair and its auxiliary choice. Placement
commands carry the cores and threads needed to check and apply the update. -/
inductive Action (CoreId ThreadId Choice : Type u) where
  | execute (core : CoreId) (thread : ThreadId) (choice : Choice)
  | idle (core : CoreId)
  | assign (core : CoreId) (thread : ThreadId)
  | migrate (source target : CoreId)

def Action.threadDecision : Action CoreId ThreadId Choice → Option (Decision ThreadId Choice)
  | .execute _ thread choice => some ⟨thread, choice⟩
  | _ => none

abbrev Schedule (CoreId ThreadId Choice : Type u) := List (Action CoreId ThreadId Choice)

/-- Keep every instruction, including those with empty fragments. Erase placement commands. -/
def threadSchedule (schedule : Schedule CoreId ThreadId Choice) :
    MulticoreVM.Schedule ThreadId Choice := schedule.filterMap Action.threadDecision

/-- Instruction semantics may consult the core and update the certified configuration. The
surrounding `Step` relation checks residence and attributes the emitted fragment. -/
abbrev Instruction (CoreId ThreadId Core Thread Choice Event : Type u) :=
  CoreId → ThreadId → Choice → Config CoreId ThreadId Core Thread → Fragment ThreadId Event →
    Config CoreId ThreadId Core Thread → Prop

/-- Lift a thread-store transition with unchanged core state and placement. In particular a
spawn may allocate a fresh thread in the store while leaving it waiting for placement. -/
def ofThreadStep (step : Transition (ThreadId → Option Thread) ThreadId Choice Event) :
    Instruction CoreId ThreadId Core Thread Choice Event :=
  fun _ thread choice initial fragment next =>
    step thread choice initial.threads fragment next.threads ∧
      next.cores = initial.cores ∧ next.placement = initial.placement

/-- The instruction obligation for forward refinement on the thread store. It needs to hold
only when the executing thread is resident on the given core. -/
def Instruction.Refines (instruction : Instruction CoreId ThreadId Core Thread Choice Event)
    (step : Transition (ThreadId → Option Thread) ThreadId Choice Event) : Prop :=
  ∀ ⦃core thread choice initial fragment next⦄, initial.placement core = some thread →
    instruction core thread choice initial fragment next →
    step thread choice initial.threads fragment next.threads

/-- Idle clears a configured core. Assign installs a waiting thread on a configured core,
leaving any displaced thread allocated. Migrate moves a resident thread atomically to a
configured idle core and leaves the source idle. All three commands leave the stores intact. -/
inductive Step [DecidableEq CoreId]
    (instruction : Instruction CoreId ThreadId Core Thread Choice Event) :
    Action CoreId ThreadId Choice → Config CoreId ThreadId Core Thread →
      TaggedWord CoreId ThreadId Event → Config CoreId ThreadId Core Thread → Prop
  | execute {core thread choice initial fragment next} :
      initial.placement core = some thread → instruction core thread choice initial fragment next →
      Step instruction (.execute core thread choice) initial (tagFragment core thread fragment) next
  | idle {core initial next} :
      (initial.cores core).isSome →
      initial.ReplacesPlacement next (Function.update initial.placement core none) →
      Step instruction (.idle core) initial [] next
  | assign {core thread initial next} :
      (initial.cores core).isSome → (initial.threads thread).isSome →
      (∀ c, initial.placement c ≠ some thread) →
      initial.ReplacesPlacement next (Function.update initial.placement core (some thread)) →
      Step instruction (.assign core thread) initial [] next
  | migrate {source target thread initial next} :
      initial.placement source = some thread → initial.placement target = none →
      (initial.cores target).isSome →
      initial.ReplacesPlacement next
        (Function.update (Function.update initial.placement source none) target (some thread)) →
      Step instruction (.migrate source target) initial [] next

/-- Successful finite concrete executions. Each action must succeed, and its fragment is
appended in chronological order. -/
inductive Scheduled [DecidableEq CoreId]
    (instruction : Instruction CoreId ThreadId Core Thread Choice Event) :
    Schedule CoreId ThreadId Choice → Config CoreId ThreadId Core Thread →
      TaggedWord CoreId ThreadId Event → Config CoreId ThreadId Core Thread → Prop
  | nil (cfg) : Scheduled instruction [] cfg [] cfg
  | cons {action schedule initial fragment next tail final} :
      Step instruction action initial fragment next → Scheduled instruction schedule next tail final →
      Scheduled instruction (action :: schedule) initial (fragment ++ tail) final

end Silmaril.Machine.MulticoreVM.Placed
