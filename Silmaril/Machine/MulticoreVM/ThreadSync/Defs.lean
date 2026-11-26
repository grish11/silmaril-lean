module

public import Silmaril.Machine.MulticoreVM.Defs

/-! # Keyed thread synchronization for a current-thread VM -/

@[expose] public section

namespace Silmaril.Machine.MulticoreVM.ThreadSync

universe u

/-- A parked thread holds the continuation it will use when woken. -/
inductive ThreadState (Key Local : Type u) where
  | runnable (localState : Local)
  | parked (key : Key) (resume : Local)

/-- A shared word for each key and an optional slot for each thread. -/
structure Config (Thread Key Value Local : Type u) where
  words : Key → Value
  threads : Thread → Option (ThreadState Key Local)

/-- A local program supplies its next action. A wait supplies separate continuations for
mismatch and eventual wake. A wake supplies a continuation given the number woken. -/
inductive Action (Key Value Local Output : Type u) where
  | localStep (next : Local) (output : Option Output)
  | store (key : Key) (value : Value) (next : Local)
  | wait (key : Key) (expected : Value) (onMismatch onWake : Local)
  | wake (key : Key) (limit : Nat) (next : Nat → Local)
  | yield (next : Local)

abbrev Program (Thread Key Value Local Output : Type u) :=
  Thread → Local → Option (Action Key Value Local Output)

inductive Event (Thread Key Value Output : Type u) where
  | localOutput (output : Output)
  | store (key : Key) (value : Value)
  | waitMismatch (key : Key) (expected actual : Value)
  | waitPark (key : Key) (expected : Value)
  | wake (key : Key) (limit : Nat) (woken : List Thread)
  | yield

variable {Thread Key Value Local Output : Type u}

/-- Install an allocated thread slot. -/
def Config.put [DecidableEq Thread] (cfg : Config Thread Key Value Local) (thread : Thread)
    (slot : ThreadState Key Local) : Config Thread Key Value Local :=
  { cfg with threads := fun t => if t = thread then some slot else cfg.threads t }

/-- Test the current parked key of a thread. -/
def Config.parkedAt [DecidableEq Key] (cfg : Config Thread Key Value Local)
    (key : Key) (thread : Thread) : Bool :=
  match cfg.threads thread with
  | some (.parked waiting _) => decide (waiting = key)
  | _ => false

/-- An explicit wake choice names distinct threads parked at the addressed key.
Any such list within the bound is allowed, including the empty list. -/
def WakeAllowed [DecidableEq Key] (cfg : Config Thread Key Value Local)
    (key : Key) (limit : Nat) (waiters : List Thread) : Prop :=
  waiters.length ≤ limit ∧ waiters.Nodup ∧ waiters.all (cfg.parkedAt key) = true

instance [DecidableEq Thread] [DecidableEq Key] (cfg : Config Thread Key Value Local)
    (key : Key) (limit : Nat) (waiters : List Thread) :
    Decidable (WakeAllowed cfg key limit waiters) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Restore the saved continuation of each selected parked thread. -/
def Config.resume [DecidableEq Thread] (cfg : Config Thread Key Value Local)
    (waiters : List Thread) : Config Thread Key Value Local :=
  { cfg with threads := fun t =>
    if t ∈ waiters then
      match cfg.threads t with
      | some (.parked _ saved) => some (.runnable saved)
      | slot => slot
    else cfg.threads t }

/-- The wake event carries the key and selected recipients. A nonempty wake also
emits a synchronization marker with the waker followed by those recipients. -/
def wakeFragment (thread : Thread) (key : Key) (limit : Nat) (waiters : List Thread) :
    Fragment Thread (Event Thread Key Value Output) :=
  .event (.wake key limit waiters) ::
    if waiters.isEmpty then [] else [.sync (thread :: waiters)]

variable [DecidableEq Thread] [DecidableEq Key] [DecidableEq Value]

/-- Take one step of the selected runnable thread. The auxiliary choice is the wake
list, which must be empty for every other action. Comparison and parking happen in
the same step. Stores change only the addressed word and do not unpark threads.
Every transition consumes the action by installing its supplied continuation. -/
def exec (program : Program Thread Key Value Local Output) (thread : Thread)
    (waiters : List Thread) (cfg : Config Thread Key Value Local) :
    Option (Config Thread Key Value Local × Fragment Thread (Event Thread Key Value Output)) := do
  let some (.runnable localState) := cfg.threads thread | none
  let action ← program thread localState
  match action, waiters with
  | .wake key limit next, _ =>
    if WakeAllowed cfg key limit waiters then
      return ((cfg.resume waiters).put thread (.runnable (next waiters.length)),
        wakeFragment thread key limit waiters)
    else none
  | .localStep next output, [] =>
    return (cfg.put thread (.runnable next), output.toList.map fun x => .event (.localOutput x))
  | .store key value next, [] =>
    return ({ cfg.put thread (.runnable next) with
      words := fun k => if k = key then value else cfg.words k }, [.event (.store key value)])
  | .wait key expected onMismatch onWake, [] =>
    let actual := cfg.words key
    if actual = expected then
      return (cfg.put thread (.parked key onWake), [.event (.waitPark key expected)])
    else
      return (cfg.put thread (.runnable onMismatch), [.event (.waitMismatch key expected actual)])
  | .yield next, [] =>
    return (cfg.put thread (.runnable next), [.event .yield])
  | _, _ => none

/-- The VM may choose any runnable thread with a next action at each transition.
A yield marks a voluntary dispatch point that an outer scheduler may use. -/
abbrev step (program : Program Thread Key Value Local Output) :
    Transition (Config Thread Key Value Local) Thread (List Thread) (Event Thread Key Value Output) :=
  ofExecutor (exec program)

/-- State for a single cooperative dispatcher. An unowned VM can dispatch any ready
thread, including the thread that just yielded. -/
structure DispatchState (Thread Key Value Local : Type u) where
  vm : Config Thread Key Value Local
  owner : Option Thread := none

/-- Keep dispatch ownership across ordinary steps. Release it at a yield, when
the owner parks, or when the owner has no next action. -/
def cooperativeExec (program : Program Thread Key Value Local Output) (thread : Thread)
    (waiters : List Thread) (state : DispatchState Thread Key Value Local) :
    Option (DispatchState Thread Key Value Local × Fragment Thread (Event Thread Key Value Output)) :=
  if state.owner.any (fun owner => decide (thread ≠ owner)) then none else do
    let (vm, fragment) ← exec program thread waiters state.vm
    let owner := match fragment, vm.threads thread with
      | [.event .yield], _ => none
      | _, some (.runnable localState) =>
        if (program thread localState).isSome then some thread else none
      | _, _ => none
    return (⟨vm, owner⟩, fragment)

/-- Cooperative scheduling as a current-thread transition. -/
abbrev cooperativeStep (program : Program Thread Key Value Local Output) :
    Transition (DispatchState Thread Key Value Local) Thread (List Thread)
      (Event Thread Key Value Output) :=
  ofExecutor (cooperativeExec program)

end Silmaril.Machine.MulticoreVM.ThreadSync
