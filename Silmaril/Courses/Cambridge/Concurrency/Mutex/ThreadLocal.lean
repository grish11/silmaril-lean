module

public import Silmaril.Courses.Cambridge.Concurrency.Mutex.Global

/-! # Labelled thread-local semantics

Sewell, pp. 94–96. A thread-local step proposes an action using the
expression alone. The configuration rules check and apply that action
against the shared store and mutex state.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.Concurrency.Mutex

inductive Action where
  | tau
  | write (loc : Loc) (n : Int)
  | read (loc : Loc) (n : Int)
  | lock (name : MutexName)
  | unlock (name : MutexName)
  deriving DecidableEq, Repr

inductive ThreadStep : Expr → Action → Expr → Prop where
  | add (left right : Int) :
      ThreadStep (.binary (.int left) .add (.int right)) .tau (.int (left + right))
  | ge (left right : Int) :
      ThreadStep (.binary (.int left) .ge (.int right)) .tau (.bool (left ≥ right))
  | binaryLeft {left left' right : Expr} {op : Op} {action : Action} :
      ThreadStep left action left' →
      ThreadStep (.binary left op right) action (.binary left' op right)
  | binaryRight {left right right' : Expr} {op : Op} {action : Action} :
      IsValue left → ThreadStep right action right' →
      ThreadStep (.binary left op right) action (.binary left op right')
  | deref (loc : Loc) (n : Int) : ThreadStep (.deref loc) (.read loc n) (.int n)
  | assignValue (loc : Loc) (n : Int) : ThreadStep (.assign loc (.int n)) (.write loc n) .skip
  | assignStep {loc : Loc} {e e' : Expr} {action : Action} :
      ThreadStep e action e' → ThreadStep (.assign loc e) action (.assign loc e')
  | seqSkip (e : Expr) : ThreadStep (.seq .skip e) .tau e
  | seqStep {left left' right : Expr} {action : Action} :
      ThreadStep left action left' → ThreadStep (.seq left right) action (.seq left' right)
  | ifTrue (yes no : Expr) : ThreadStep (.cond (.bool true) yes no) .tau yes
  | ifFalse (yes no : Expr) : ThreadStep (.cond (.bool false) yes no) .tau no
  | ifStep {test test' yes no : Expr} {action : Action} :
      ThreadStep test action test' → ThreadStep (.cond test yes no) action (.cond test' yes no)
  | while (test body : Expr) :
      ThreadStep (.loop test body) .tau (.cond test (.seq body (.loop test body)) .skip)
  | parallelLeft {left left' right : Expr} {action : Action} :
      ThreadStep left action left' → ThreadStep (.parallel left right) action (.parallel left' right)
  | parallelRight {left right right' : Expr} {action : Action} :
      ThreadStep right action right' → ThreadStep (.parallel left right) action (.parallel left right')
  | lock (name : MutexName) : ThreadStep (.lock name) (.lock name) .skip
  | unlock (name : MutexName) : ThreadStep (.unlock name) (.unlock name) .skip

/-- The labelled transition system of expressions, before applying state premises. -/
def threadLTS : Cslib.LTS Expr Action := ⟨ThreadStep⟩

/-- State premises and effects of the five configuration rules on p. 96. -/
inductive Effect : Action → SharedState → SharedState → Prop where
  | tau (s : SharedState) : Effect .tau s s
  | write {loc : Loc} {n : Int} {s : SharedState} (present : loc ∈ s.store) :
      Effect (.write loc n) s (s.write loc n)
  | read {loc : Loc} {n : Int} {s : SharedState} (present : L1.Store.lookup s.store loc = some n) :
      Effect (.read loc n) s s
  | lock {name : MutexName} {s : SharedState} (available : s.mutexes name = false) :
      Effect (.lock name) s (s.setMutex name true)
  | unlock (name : MutexName) (s : SharedState) :
      Effect (.unlock name) s (s.setMutex name false)

/-- Global reduction induced by the labelled and configuration rules. -/
def LabelledStep (before after : Config) : Prop :=
  ∃ action, ThreadStep before.expr action after.expr ∧ Effect action before.shared after.shared

end Silmaril.Courses.Cambridge.Concurrency.Mutex
