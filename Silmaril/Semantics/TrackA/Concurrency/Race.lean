module

public import Silmaril.Semantics.TrackA.Concurrency.Defs

/-! Race classification on finite SC event histories. Event indices distinguish
occurrences even when two steps emit the same label. -/

@[expose] public section

namespace Silmaril.Semantics.TrackA.Concurrency

inductive RaceProfile where
  /-- Mutex synchronization only. All memory accesses are treated as ordinary. -/
  | mutexOnly
  /-- SC atomic stores and loads have release/acquire semantics. Two atomic
  accesses are exempt from races. A plain/atomic pair can still race. -/
  | mixed
  deriving DecidableEq, Repr

variable {T L R : Type} [DecidableEq T] [DecidableEq L] [DecidableEq R]

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

/-- The SC read takes its value from the last write, including plain writes.
Equal values alone never establish a reads-from edge. -/
def atomicSync (xs : List (Event T L R)) (i j : Nat) (a b : Action L R) : Bool :=
  match a, b with
  | .write .scAtomic loc _, .read .scAtomic other _ =>
      decide (loc = other) && !(((xs.take j).drop (i + 1)).any fun event => event.action.writesTo loc)
  | _, _ => false

/-- Program order or synchronization, always oriented by occurrence index. -/
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

def classify (profile : RaceProfile) (xs : List (Event T L R)) : RaceClass :=
  if hasRace profile xs then .racy else .clean

/-- Generate a raw SC execution and report its classification. -/
def ClassifiedRun (profile : RaceProfile) (s : Config T L R) (xs : List (Event T L R))
    (t : Config T L R) (result : RaceClass) : Prop :=
  sc.MTr s xs t ∧ classify profile xs = result

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
