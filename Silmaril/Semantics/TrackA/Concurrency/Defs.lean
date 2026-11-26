module

public import Silmaril.Semantics.Operational.Execution

/-! Primitive SC for fixed thread, lock and resource identifiers. Each step is one
successful memory or mutex operation. A blocked acquire emits no event. -/

@[expose] public section

namespace Silmaril.Semantics.TrackA.Concurrency

inductive AccessMode where
  | plain
  | scAtomic
  deriving DecidableEq, Repr

/-- A load can choose the rest of the thread's program using the observed value. -/
inductive Program (Lock Resource : Type) where
  | done
  | load (mode : AccessMode) (atResource : Resource) (next : Nat → Program Lock Resource)
  | store (mode : AccessMode) (atResource : Resource) (value : Nat) (next : Program Lock Resource)
  | acquire (lock : Lock) (next : Program Lock Resource)
  | release (lock : Lock) (next : Program Lock Resource)

inductive Action (Lock Resource : Type) where
  | read (mode : AccessMode) (atResource : Resource) (value : Nat)
  | write (mode : AccessMode) (atResource : Resource) (value : Nat)
  | acquire (lock : Lock)
  | release (lock : Lock)
  deriving DecidableEq, Repr

structure Event (Thread Lock Resource : Type) where
  thread : Thread
  action : Action Lock Resource
  deriving DecidableEq, Repr

structure Shared (Thread Lock Resource : Type) where
  memory : Resource → Nat
  owner : Lock → Option Thread

def Shared.initial {T L R : Type} (memory : R → Nat) : Shared T L R :=
  ⟨memory, fun _ => none⟩

abbrev Local (T L R : Type) := Program L R × Shared T L R

structure Config (Thread Lock Resource : Type) where
  code : Thread → Program Lock Resource
  shared : Shared Thread Lock Resource

abbrev SingleMutexConfig (Thread Resource : Type) := Config Thread Unit Resource

variable {T L R : Type}

def Config.initial (code : T → Program L R) (memory : R → Nat) : Config T L R :=
  ⟨code, Shared.initial memory⟩

def Config.localState (s : Config T L R) (thread : T) : Local T L R :=
  (s.code thread, s.shared)

def Config.single (s : Local Unit L R) : Config Unit L R :=
  ⟨fun _ => s.1, s.2⟩

/-- A single owner per lock. Waiters are determined by pending commands and
current ownership. There is no queue or handoff policy in the state. -/
def Config.Held (s : Config T L R) (thread : T) (lock : L) : Prop :=
  s.shared.owner lock = some thread

def Config.Waiting (s : Config T L R) (thread : T) (lock : L) : Prop :=
  (∃ next, s.code thread = .acquire lock next) ∧ s.shared.owner lock ≠ none

def Config.Done (s : Config T L R) : Prop :=
  ∀ thread, s.code thread = .done

variable [DecidableEq T] [DecidableEq L] [DecidableEq R]

/-- Read the current value, or commit a store immediately. Mutexes are
non-reentrant and release is enabled only for the current owner. -/
def primitive (thread : T) (s : Local T L R) : Option (Event T L R × Local T L R) :=
  match s.1 with
  | .done => none
  | .load mode loc next =>
      let value := s.2.memory loc
      some (⟨thread, .read mode loc value⟩, next value, s.2)
  | .store mode loc value next =>
      some (⟨thread, .write mode loc value⟩, next,
        { s.2 with memory := Function.update s.2.memory loc value })
  | .acquire lock next =>
      if s.2.owner lock = none then
        some (⟨thread, .acquire lock⟩, next,
          { s.2 with owner := Function.update s.2.owner lock (some thread) })
      else none
  | .release lock next =>
      if s.2.owner lock = some thread then
        some (⟨thread, .release lock⟩, next,
          { s.2 with owner := Function.update s.2.owner lock none })
      else none

/-- Run one thread in a fixed environment with no interleaved peer steps.
The local state carries the same shared memory and mutex owners as SC. -/
def sequential (thread : T) : Cslib.LTS (Local T L R) (Event T L R) :=
  ⟨fun s event s' => primitive thread s = some (event, s')⟩

def Config.stepFor (s : Config T L R) (thread : T) : Option (Event T L R × Config T L R) :=
  (primitive thread (s.localState thread)).map fun (event, next, shared) =>
    (event, ⟨Function.update s.code thread next, shared⟩)

/-- A scheduler chooses which thread takes the next successful primitive step. -/
def sc : Cslib.LTS (Config T L R) (Event T L R) :=
  ⟨fun s event s' => s.stepFor event.thread = some (event, s')⟩

/-- A terminal unfinished configuration. For a general program this includes
a wrong-owner release as well as lock deadlock. -/
def Config.Stuck (s : Config T L R) : Prop :=
  sc.IsTerminal s ∧ ¬ s.Done

/-- Two distinct threads blocked on locks owned by each other. -/
def Config.LockCycle₂ (s : Config T L R) : Prop :=
  ∃ t u l k, t ≠ u ∧ s.Held t l ∧ s.Held u k ∧ s.Waiting t k ∧ s.Waiting u l

/-- Replay exactly the scheduled steps. Selecting a disabled thread fails. -/
def replay (s : Config T L R) : List T → Option (List (Event T L R) × Config T L R)
  | [] => some ([], s)
  | t :: ts => do
      let (event, next) ← s.stepFor t
      let (events, last) ← replay next ts
      return (event :: events, last)

/-- Enumerate from an explicitly supplied thread list. Coverage is required
only for completeness. -/
def successors (threads : List T) (s : Config T L R) : List (Event T L R × Config T L R) :=
  threads.filterMap s.stepFor

end Silmaril.Semantics.TrackA.Concurrency
