module

public import Silmaril.Courses.Cambridge.Concurrency.Mutex.Preservation
public import Silmaril.Courses.Cambridge.Concurrency.Mutex.ThreadLocal

/-! # Ordered two-phase locking in Cambridge L1

Sewell (12 February 2026), pp. 93 and 97. The definitions use the local
labelled traces of an expression and the direct global configuration steps.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.Concurrency.Mutex.OrderedTwoPhase

structure Layout where
  mutexOf : Loc ≃ MutexName
  order : LinearOrder MutexName

/-- A condition on each event and the actions strictly before it. -/
def EveryEvent (guard : List Action → Action → Prop) (trace : List Action) : Prop :=
  ∀ history action suffix, trace = history ++ action :: suffix → guard history action

@[simp] theorem EveryEvent.nil (guard : List Action → Action → Prop) : EveryEvent guard [] := by
  intro history action suffix split
  cases history <;> simp at split

@[simp] theorem EveryEvent.cons {guard : List Action → Action → Prop}
    {first : Action} {rest : List Action} :
    EveryEvent guard (first :: rest) ↔
      guard [] first ∧ EveryEvent (fun history action => guard (first :: history) action) rest := by
  constructor
  · intro h
    exact ⟨h [] first rest rfl, fun history action suffix split =>
      h (first :: history) action suffix (congrArg (first :: ·) split)⟩
  · rintro ⟨head, tail⟩ history action suffix split
    cases history with
    | nil =>
        simp only [List.nil_append, List.cons.injEq] at split
        exact split.1 ▸ head
    | cons name history =>
        simp only [List.cons_append, List.cons.injEq] at split
        obtain ⟨rfl, equal⟩ := split
        exact tail history action suffix equal

theorem EveryEvent.prefix {guard : List Action → Action → Prop} {short long : List Action}
    (h : EveryEvent guard long) (history : short <+: long) : EveryEvent guard short := by
  obtain ⟨extra, rfl⟩ := history
  intro before action after split
  exact h before action (after ++ extra) (by simp [split, List.append_assoc])

/-- The last event for each mutex determines its held bit in the local trace. -/
def heldAfter (trace : List Action) : MutexState :=
  trace.foldl (fun held action =>
    match action with
    | .lock name => held.set name true
    | .unlock name => held.set name false
    | _ => held) MutexState.initial

def accessGuard (layout : Layout) (history : List Action) : Action → Prop
  | .read loc _ | .write loc _ => heldAfter history (layout.mutexOf loc) = true
  | _ => True

def bracketGuard (history : List Action) : Action → Prop
  | .lock name => heldAfter history name = false
  | .unlock name => heldAfter history name = true
  | _ => True

def phaseGuard (history : List Action) : Action → Prop
  | .lock _ => ∀ action ∈ history, match action with
      | .unlock _ => False
      | _ => True
  | _ => True

def orderGuard (layout : Layout) (history : List Action) : Action → Prop
  | .lock name => ∀ action ∈ history, match action with
      | .lock earlier => layout.order.lt earlier name
      | _ => True
  | _ => True

structure PrefixConditions (layout : Layout) (trace : List Action) : Prop where
  access : EveryEvent (accessGuard layout) trace
  bracketing : EveryEvent bracketGuard trace
  phase : EveryEvent phaseGuard trace
  order : EveryEvent (orderGuard layout) trace

theorem PrefixConditions.prefix {layout : Layout} {short long : List Action}
    (h : PrefixConditions layout long) (history : short <+: long) : PrefixConditions layout short :=
  ⟨h.access.prefix history, h.bracketing.prefix history, h.phase.prefix history, h.order.prefix history⟩

def Released (trace : List Action) : Prop := ∀ name, heldAfter trace name = false

def LocalTerminal (e : Expr) : Prop := ∀ action next, ¬ ThreadStep e action next

/-- Every finite prefix meets the four safety conditions. At a terminal local
expression every acquisition has a matching release. Infinite traces are
covered by their finite prefixes. -/
def Obeys (layout : Layout) (e : Expr) : Prop :=
  ∀ {trace after}, threadLTS.MTr e trace after →
    PrefixConditions layout trace ∧ (LocalTerminal after → Released trace)

theorem Obeys.infinite_prefix {layout : Layout} {states : Nat → Expr} {actions : Nat → Action}
    (obeys : Obeys layout (states 0))
    (steps : ∀ n, ThreadStep (states n) (actions n) (states (n + 1))) (length : Nat) :
    PrefixConditions layout ((List.range length).map actions) := by
  have traces (n : Nat) : threadLTS.MTr (states 0) ((List.range n).map actions) (states n) := by
    induction n with
    | zero => exact .refl
    | succ n ih =>
        simpa only [List.range_succ, List.map_append, List.map_singleton] using
          Cslib.LTS.MTr.stepR threadLTS ih (steps n)
  exact (obeys (traces length)).1

/-- Fix the bracketing of the notes' multiway parallel composition. -/
def parallel : List Expr → Expr
  | [] => .skip
  | [e] => e
  | e :: next :: rest => .parallel e (parallel (next :: rest))

def sequential : List Expr → Expr
  | [] => .skip
  | [e] => e
  | e :: next :: rest => .seq e (sequential (next :: rest))

def start (e : Expr) (store : Store) : Config := ⟨e, ⟨store, MutexState.initial⟩⟩

/-- A serial prefix can reproduce the terminal parallel run's shared state. -/
def Serializable (initialStore : Store → Prop) (threads : List Expr) : Prop :=
  ∀ store, initialStore store → ∀ after,
    Steps (start (parallel threads) store) after → Terminal after →
      ∃ order : List Expr, order.Perm threads ∧ ∃ e,
        Steps (start (sequential order) store) ⟨e, after.shared⟩

/-- At a terminal global configuration no local lock proposal is pending. -/
def DeadlockFree (initialStore : Store → Prop) (threads : List Expr) : Prop :=
  ∀ store, initialStore store → ∀ after,
    Steps (start (parallel threads) store) after → Terminal after →
      ∀ name e, ¬ ThreadStep after.expr (.lock name) e

def Claim (initialStore : TypeEnv → Store → Prop) : Prop :=
  ∀ (layout : Layout) (Γ : TypeEnv) (threads : List Expr),
    (∀ e ∈ threads, HasType Γ e .unit ∧ Obeys layout e) →
    Serializable (initialStore Γ) threads ∧ DeadlockFree (initialStore Γ) threads

/-- Conjecture 28 with the printed quantification over every initial store. -/
def Conjecture28 : Prop := Claim (fun _ _ => True)

/-- The variant restricted to stores covering the shared location context. -/
def CoveredConjecture28 : Prop := Claim L1.StoreCovers

end Silmaril.Courses.Cambridge.Concurrency.Mutex.OrderedTwoPhase
