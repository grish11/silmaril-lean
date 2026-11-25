module

public import Silmaril.Courses.Cambridge.Concurrency.Mutex.Syntax
public import Silmaril.Courses.Cambridge.Concurrency.Reduction
public import Mathlib.Logic.Function.Basic

/-! # Direct global semantics with mutexes

Sewell, pp. 92 and 96. The global state combines the L1 store with a total
map from mutex names to Booleans. Lock acquisition checks and sets the bit
in a single step. Unlock clears the bit and can step in any mutex state.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.Concurrency.Mutex

abbrev MutexState := MutexName → Bool

def MutexState.initial : MutexState := fun _ => false

def MutexState.set (mutexes : MutexState) (name : MutexName) (held : Bool) : MutexState :=
  Function.update mutexes name held

@[simp] theorem MutexState.set_same (mutexes : MutexState) (name : MutexName) (held : Bool) :
    (mutexes.set name held) name = held := by
  simp only [set, Function.update_self]

@[simp] theorem MutexState.set_other (mutexes : MutexState) {name other : MutexName}
    (different : other ≠ name) (held : Bool) :
    (mutexes.set name held) other = mutexes other := by
  simp only [set, Function.update_of_ne different]

structure SharedState where
  store : Store
  mutexes : MutexState

def SharedState.write (state : SharedState) (loc : Loc) (n : Int) : SharedState :=
  { state with store := state.store.insert loc n }

def SharedState.setMutex (state : SharedState) (name : MutexName) (held : Bool) : SharedState :=
  { state with mutexes := state.mutexes.set name held }

structure Config where
  expr : Expr
  shared : SharedState

inductive Step : Config → Config → Prop where
  | add (left right : Int) (s : SharedState) :
      Step ⟨.binary (.int left) .add (.int right), s⟩ ⟨.int (left + right), s⟩
  | ge (left right : Int) (s : SharedState) :
      Step ⟨.binary (.int left) .ge (.int right), s⟩ ⟨.bool (left ≥ right), s⟩
  | binaryLeft {left left' right : Expr} {op : Op} {s s' : SharedState} :
      Step ⟨left, s⟩ ⟨left', s'⟩ →
      Step ⟨.binary left op right, s⟩ ⟨.binary left' op right, s'⟩
  | binaryRight {left right right' : Expr} {op : Op} {s s' : SharedState} :
      IsValue left → Step ⟨right, s⟩ ⟨right', s'⟩ →
      Step ⟨.binary left op right, s⟩ ⟨.binary left op right', s'⟩
  | deref {loc : Loc} {s : SharedState} {n : Int} (present : L1.Store.lookup s.store loc = some n) :
      Step ⟨.deref loc, s⟩ ⟨.int n, s⟩
  | assignValue {loc : Loc} {s : SharedState} {n : Int} (present : loc ∈ s.store) :
      Step ⟨.assign loc (.int n), s⟩ ⟨.skip, s.write loc n⟩
  | assignStep {loc : Loc} {e e' : Expr} {s s' : SharedState} :
      Step ⟨e, s⟩ ⟨e', s'⟩ → Step ⟨.assign loc e, s⟩ ⟨.assign loc e', s'⟩
  | seqSkip {e : Expr} {s : SharedState} :
      Step ⟨.seq .skip e, s⟩ ⟨e, s⟩
  | seqStep {left left' right : Expr} {s s' : SharedState} :
      Step ⟨left, s⟩ ⟨left', s'⟩ → Step ⟨.seq left right, s⟩ ⟨.seq left' right, s'⟩
  | ifTrue {yes no : Expr} {s : SharedState} :
      Step ⟨.cond (.bool true) yes no, s⟩ ⟨yes, s⟩
  | ifFalse {yes no : Expr} {s : SharedState} :
      Step ⟨.cond (.bool false) yes no, s⟩ ⟨no, s⟩
  | ifStep {test test' yes no : Expr} {s s' : SharedState} :
      Step ⟨test, s⟩ ⟨test', s'⟩ → Step ⟨.cond test yes no, s⟩ ⟨.cond test' yes no, s'⟩
  | while {test body : Expr} {s : SharedState} :
      Step ⟨.loop test body, s⟩
        ⟨.cond test (.seq body (.loop test body)) .skip, s⟩
  | parallelLeft {left left' right : Expr} {s s' : SharedState} :
      Step ⟨left, s⟩ ⟨left', s'⟩ → Step ⟨.parallel left right, s⟩ ⟨.parallel left' right, s'⟩
  | parallelRight {left right right' : Expr} {s s' : SharedState} :
      Step ⟨right, s⟩ ⟨right', s'⟩ → Step ⟨.parallel left right, s⟩ ⟨.parallel left right', s'⟩
  | lock {name : MutexName} {s : SharedState} (available : s.mutexes name = false) :
      Step ⟨.lock name, s⟩ ⟨.skip, s.setMutex name true⟩
  | unlock (name : MutexName) (s : SharedState) :
      Step ⟨.unlock name, s⟩ ⟨.skip, s.setMutex name false⟩

abbrev Steps : Config → Config → Prop := Relation.ReflTransGen Step

def Terminal (c : Config) : Prop := ∀ next, ¬ Step c next

def Config.ofInterleaving (mutexes : MutexState) (c : Concurrency.Config) : Config :=
  ⟨Expr.ofInterleaving c.expr, ⟨c.store, mutexes⟩⟩

private theorem IsValue.ofInterleaving {e : Concurrency.Expr} (value : Concurrency.IsValue e) :
    IsValue (Expr.ofInterleaving e) := by
  cases value with
  | int n => exact .int n
  | bool b => exact .bool b
  | skip => exact .skip

theorem Step.ofInterleaving (mutexes : MutexState) {before after : Concurrency.Config}
    (step : Concurrency.Step before after) :
    Step (Config.ofInterleaving mutexes before) (Config.ofInterleaving mutexes after) := by
  induction step with
  | add left right => exact .add left right _
  | ge left right => exact .ge left right _
  | binaryLeft _ ih => exact .binaryLeft ih
  | binaryRight value _ ih => exact .binaryRight (IsValue.ofInterleaving value) ih
  | deref present => exact .deref present
  | assignValue present => exact .assignValue present
  | assignStep _ ih => exact .assignStep ih
  | seqSkip => exact .seqSkip
  | seqStep _ ih => exact .seqStep ih
  | ifTrue => exact .ifTrue
  | ifFalse => exact .ifFalse
  | ifStep _ ih => exact .ifStep ih
  | «while» => exact .while
  | parallelLeft _ ih => exact .parallelLeft ih
  | parallelRight _ ih => exact .parallelRight ih

/-- A lock on an already held mutex has to wait. -/
theorem lock_terminal {s : SharedState} {name : MutexName} (held : s.mutexes name = true) :
    Terminal ⟨.lock name, s⟩ := by
  intro next step
  cases step with
  | lock available => simp [held] at available

end Silmaril.Courses.Cambridge.Concurrency.Mutex
