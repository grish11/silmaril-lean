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

/-! ## Race classification

Event positions distinguish repeated labels. Raw tests are total on lists.
Their interpretation as races and synchronization of an execution requires
a generated SC history.
-/

inductive RaceProfile where
  /-- Mutex synchronization only. All memory accesses are treated as ordinary. -/
  | mutexOnly
  /-- SC atomic stores and loads have release/acquire semantics. Two atomic
  accesses are exempt from races. A plain/atomic pair can still race. -/
  | mixed
  deriving DecidableEq, Repr

def Action.access : Action L R → Option (AccessMode × R × Bool)
  | .read mode loc _ => some (mode, loc, false)
  | .write mode loc _ => some (mode, loc, true)
  | _ => none

/-- Different threads, the same resource, and at least one write. -/
def conflicts (a b : Event T L R) : Bool :=
  match a.action.access, b.action.access with
  | some (_, x, writesA), some (_, y, writesB) =>
      decide (a.thread ≠ b.thread ∧ x = y) && (writesA || writesB)
  | _, _ => false

def Action.isAtomic : Action L R → Bool
  | .read .scAtomic _ _ | .write .scAtomic _ _ => true
  | _ => false

def Action.writesTo (loc : R) : Action L R → Bool
  | .write _ other _ => decide (loc = other)
  | _ => false

/-- An acquire is ordered after earlier releases of the same mutex,
including the preceding handoff. Program order chains the intervening
critical sections in any generated execution. -/
def mutexSync (a b : Action L R) : Bool :=
  match a, b with
  | .release l, .acquire k => decide (l = k)
  | _, _ => false

/-- Raw test on candidate atomic write and read labels. With `i < j` and the
labels taken from positions `i` and `j` of a generated SC history, this recognizes
the last preceding write to the read's resource. Any intervening write to that
resource, including a plain write, breaks the edge. The test is total on
arbitrary inputs and checks neither label provenance nor recorded values. -/
def atomicSync (xs : List (Event T L R)) (i j : Nat) (a b : Action L R) : Bool :=
  match a, b with
  | .write .scAtomic loc _, .read .scAtomic other _ =>
      decide (loc = other) && !(((xs.take j).drop (i + 1)).any fun event => event.action.writesTo loc)
  | _, _ => false

/-- Program-order or synchronization edges on labels, oriented by occurrence
index. Their execution interpretation requires a generated SC history. -/
def direct (profile : RaceProfile) (xs : List (Event T L R)) (i j : Nat) : Bool :=
  if i < j then
    match xs[i]?, xs[j]? with
    | some a, some b =>
        decide (a.thread = b.thread) || mutexSync a.action b.action ||
          (match profile with
          | .mutexOnly => false
          | .mixed => atomicSync xs i j a.action b.action)
    | _, _ => false
  else false

/-- Search for a nonempty path of at most the given number of edges. -/
def happensBeforeWithin (profile : RaceProfile) (xs : List (Event T L R)) (i : Nat) :
    Nat → Nat → Bool
  | 0, _ => false
  | fuel + 1, j =>
      direct profile xs i j || (List.range j).any fun k =>
        if k < j then happensBeforeWithin profile xs i fuel k && direct profile xs k j else false

/-- All paths fit the bound because edges strictly increase the event index. -/
def happensBefore (profile : RaceProfile) (xs : List (Event T L R)) (i j : Nat) : Bool :=
  happensBeforeWithin profile xs i (j + 1) j

def racePair (profile : RaceProfile) (xs : List (Event T L R)) (i j : Nat) : Bool :=
  if i < j then
    match xs[i]?, xs[j]? with
    | some a, some b =>
        conflicts a b && !happensBefore profile xs i j &&
          (match profile with
          | .mutexOnly => true
          | .mixed => !(a.action.isAtomic && b.action.isAtomic))
    | _, _ => false
  else false

def hasRace (profile : RaceProfile) (xs : List (Event T L R)) : Bool :=
  (List.range xs.length).any fun j => (List.range j).any (racePair profile xs · j)

abbrev RaceFree (profile : RaceProfile) (xs : List (Event T L R)) : Prop :=
  hasRace profile xs = false

inductive RaceClass where
  | clean
  | racy
  deriving DecidableEq, Repr

/-- Total classification of event labels. A clean result concerns the input
list alone. Use `ClassifiedRun` for semantic claims or `classifyHistory` to
validate a caller-supplied history against a given initial configuration. -/
def classify (profile : RaceProfile) (xs : List (Event T L R)) : RaceClass :=
  if hasRace profile xs then .racy else .clean

/-- Semantic classification, explicitly requiring that the labelled SC machine
generates the history from the given initial configuration. -/
def ClassifiedRun (profile : RaceProfile) (s : Config T L R) (xs : List (Event T L R))
    (t : Config T L R) (result : RaceClass) : Prop :=
  sc.MTr s xs t ∧ classify profile xs = result

/-- Validate the entire supplied history by replaying its thread schedule and
comparing every emitted label. Invalid histories have no classification.
A successful result classifies a finite execution prefix. -/
def classifyHistory (profile : RaceProfile) (start : Config T L R)
    (xs : List (Event T L R)) : Option RaceClass :=
  match replay start (xs.map Event.thread) with
  | some (actual, _) => if actual = xs then some (classify profile xs) else none
  | none => none

def FilteredRun (profile : RaceProfile) (s : Config T L R) (xs : List (Event T L R))
    (t : Config T L R) : Prop :=
  ClassifiedRun profile s xs t .clean

/-- The online semantics commits an ordinary step only if the resulting
history is still race-free. -/
inductive GuardedRun (profile : RaceProfile) (start : Config T L R) :
    List (Event T L R) → Config T L R → Prop where
  | nil : GuardedRun profile start [] start
  | snoc {xs s event t} : GuardedRun profile start xs s → sc.Tr s event t →
      RaceFree profile (xs ++ [event]) → GuardedRun profile start (xs ++ [event]) t

/-- The first racing extension emits UB. The attempted event is recorded, but
its successor state is not an ordinary observation of the guarded semantics. -/
def RaceUB (profile : RaceProfile) (start : Config T L R) (xs : List (Event T L R)) : Prop :=
  ∃ prior s event t, xs = prior ++ [event] ∧ GuardedRun profile start prior s ∧
    sc.Tr s event t ∧ hasRace profile xs = true

/-- Demonic race safety over all finite prefixes from a particular start. -/
def RaceSafe (profile : RaceProfile) (start : Config T L R) : Prop :=
  ∀ xs, ¬ RaceUB profile start xs

end Silmaril.Semantics.TrackA.Concurrency
