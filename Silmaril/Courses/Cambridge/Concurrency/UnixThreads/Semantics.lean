module

public import Silmaril.Courses.Cambridge.L1
public import Mathlib.Logic.Function.Basic

/-! # A Unix-style L1 thread extension for Exercise 40

The exercise on p. 97 asks for a design. This one uses identified threads
with a shared L1 store and asynchronous FIFO channels for integers.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.Concurrency.UnixThreads

abbrev ThreadId := Nat
abbrev Channel := String

inductive Command where
  | done
  | run (body : L1.Expr) (next : Command)
  | fork (destination : L1.Loc) (child next : Command)
  | join (handle : L1.Loc) (next : Command)
  | send (channel : Channel) (source : L1.Loc) (next : Command)
  | receive (channel : Channel) (destination : L1.Loc) (next : Command)
  deriving DecidableEq, Repr

abbrev ThreadPool := Finmap (fun _ : ThreadId => Command)
abbrev Queues := Channel → List Int

structure Config where
  threads : ThreadPool
  nextId : ThreadId
  store : L1.Store
  queues : Queues

def Config.start (main : Command) (store : L1.Store) : Config :=
  ⟨(∅ : ThreadPool).insert 0 main, 1, store, fun _ => []⟩

def Config.resume (c : Config) (id : ThreadId) (next : Command) : Config :=
  { c with threads := c.threads.insert id next }

def Config.spawn (c : Config) (parent : ThreadId) (destination : L1.Loc)
    (child next : Command) : Config :=
  { c with
    threads := (c.threads.insert parent next).insert c.nextId child
    nextId := c.nextId + 1
    store := c.store.insert destination (Int.ofNat c.nextId) }

def Config.reap (c : Config) (parent child : ThreadId) (next : Command) : Config :=
  { c with threads := (c.threads.erase child).insert parent next }

def Config.enqueue (c : Config) (id : ThreadId) (channel : Channel) (value : Int)
    (next : Command) : Config :=
  { c.resume id next with queues := Function.update c.queues channel (c.queues channel ++ [value]) }

def Config.dequeue (c : Config) (id : ThreadId) (channel : Channel)
    (destination : L1.Loc) (value : Int) (rest : List Int) (next : Command) : Config :=
  { c.resume id next with
    store := c.store.insert destination value
    queues := Function.update c.queues channel rest }

/-- A step schedules one thread. A finished thread stays in the pool until
a join reaps it. The continually increasing ID counter is shared. -/
inductive Step : Config → ThreadId → Config → Prop where
  | runStep {c : Config} {id : ThreadId} {body body' : L1.Expr} {next : Command} {s' : L1.Store}
      (thread : c.threads.lookup id = some (.run body next))
      (inner : L1.Step ⟨body, c.store⟩ ⟨body', s'⟩) :
      Step c id ({ c with store := s' }.resume id (.run body' next))
  | runDone {c : Config} {id : ThreadId} {next : Command}
      (thread : c.threads.lookup id = some (.run .skip next)) :
      Step c id (c.resume id next)
  | fork {c : Config} {id : ThreadId} {destination : L1.Loc} {child next : Command}
      (thread : c.threads.lookup id = some (.fork destination child next))
      (allocated : destination ∈ c.store) (fresh : c.nextId ∉ c.threads) :
      Step c id (c.spawn id destination child next)
  | join {c : Config} {id child : ThreadId} {handle : L1.Loc} {next : Command}
      (thread : c.threads.lookup id = some (.join handle next))
      (target : L1.Store.lookup c.store handle = some (Int.ofNat child))
      (finished : c.threads.lookup child = some .done) :
      Step c id (c.reap id child next)
  | send {c : Config} {id : ThreadId} {channel : Channel} {source : L1.Loc} {value : Int}
      {next : Command} (thread : c.threads.lookup id = some (.send channel source next))
      (found : L1.Store.lookup c.store source = some value) :
      Step c id (c.enqueue id channel value next)
  | receive {c : Config} {id : ThreadId} {channel : Channel} {destination : L1.Loc} {value : Int}
      {rest : List Int} {next : Command}
      (thread : c.threads.lookup id = some (.receive channel destination next))
      (allocated : destination ∈ c.store) (queued : c.queues channel = value :: rest) :
      Step c id (c.dequeue id channel destination value rest next)

def lts : Cslib.LTS Config ThreadId := ⟨Step⟩

inductive HasType (Γ : L1.TypeEnv) : Command → Prop where
  | done : HasType Γ .done
  | run {body : L1.Expr} {next : Command} :
      L1.HasType Γ body .unit → HasType Γ next → HasType Γ (.run body next)
  | fork {destination : L1.Loc} {child next : Command} :
      destination ∈ Γ → HasType Γ child → HasType Γ next → HasType Γ (.fork destination child next)
  | join {handle : L1.Loc} {next : Command} :
      handle ∈ Γ → HasType Γ next → HasType Γ (.join handle next)
  | send {channel : Channel} {source : L1.Loc} {next : Command} :
      source ∈ Γ → HasType Γ next → HasType Γ (.send channel source next)
  | receive {channel : Channel} {destination : L1.Loc} {next : Command} :
      destination ∈ Γ → HasType Γ next → HasType Γ (.receive channel destination next)

end Silmaril.Courses.Cambridge.Concurrency.UnixThreads
