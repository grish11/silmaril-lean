module

public import Silmaril.Semantics.TrackA.Concurrency.Race

/-! An interface observes occurrences of an existing finite SC execution. -/

@[expose] public section

namespace Silmaril.Semantics.TrackA.Concurrency

variable {T L R : Type}

/-- Visibility of memory resources and mutexes. Observed labels are unchanged. -/
structure Interface (L R : Type) where
  lock : L → Bool
  resource : R → Bool

def Interface.exposes (view : Interface L R) : Action L R → Bool
  | .read _ loc _ | .write _ loc _ => view.resource loc
  | .acquire lock | .release lock => view.lock lock

def Interface.inter (outer inner : Interface L R) : Interface L R where
  lock k := outer.lock k && inner.lock k
  resource r := outer.resource r && inner.resource r

def Interface.observe (view : Interface L R) (xs : List (Event T L R)) : List (Event T L R) :=
  xs.filter fun e => view.exposes e.action

/-- An order-preserving embedding of observed positions into source positions.
The label equality preserves threads, conflicts, access modes and mutex names. -/
structure Projection (xs ys : List (Event T L R)) where
  index : Fin ys.length → Fin xs.length
  mono : StrictMono index
  event_eq : ∀ i : Fin ys.length, ys[i.val] = xs[(index i).val]

/-- Source occurrences visible through the interface, in source order. -/
def Interface.positions (view : Interface L R) (xs : List (Event T L R)) : List (Fin xs.length) :=
  (List.finRange xs.length).filter fun k => view.exposes xs[k.val].action

theorem Interface.observe_eq_map (view : Interface L R) (xs : List (Event T L R)) :
    view.observe xs = (view.positions xs).map fun k => xs[k.val] := by
  have all : (List.finRange xs.length).map (fun k => xs[k.val]) = xs := by
    simp only [List.finRange, List.map_ofFn, Function.comp_def, List.ofFn_getElem]
  conv => lhs; rw [Interface.observe, ← all]
  exact List.filter_map

/-- Recover the source position of each event in a filtered observation. -/
def Interface.projection (view : Interface L R) (xs : List (Event T L R)) :
    Projection xs (view.observe xs) where
  index i := (view.positions xs)[i.val]'(by simpa [view.observe_eq_map xs] using i.isLt)
  mono := by
    intro i j lt
    exact (List.pairwise_lt_finRange xs.length).filter _ |>.rel_getElem_of_lt _ _ lt
  event_eq i := by simp [view.observe_eq_map xs]

namespace Projection

variable {xs ys zs : List (Event T L R)}

def Retains (p : Projection xs ys) (k : Fin xs.length) : Prop :=
  ∃ i, p.index i = k

/-- Compose occurrence maps when an observation is restricted further. -/
def comp (p : Projection xs ys) (q : Projection ys zs) : Projection xs zs where
  index i := p.index (q.index i)
  mono := p.mono.comp q.mono
  event_eq i := (q.event_eq i).trans (p.event_eq (q.index i))

variable [DecidableEq R]

/-- Any write strictly between the two occurrence indices, including a plain
write or a write of the same value. -/
def HasOverwrite (xs : List (Event T L R)) (i j : Fin xs.length) (loc : R) : Prop :=
  ∃ k : Fin xs.length, i < k ∧ k < j ∧ xs[k.val].action.writesTo loc = true

/-- For each retained candidate atomic reads-from pair, a source overwrite
between its endpoints has at least one retained witness. -/
def CoversOverwrites (p : Projection xs ys) : Prop :=
  ∀ (i j : Fin ys.length) loc writeValue readValue,
    ys[i.val].action = .write .scAtomic loc writeValue →
    ys[j.val].action = .read .scAtomic loc readValue →
    HasOverwrite xs (p.index i) (p.index j) loc → HasOverwrite ys i j loc

variable [DecidableEq T] [DecidableEq L]

/-- Both endpoints of each cross-thread direct edge remain visible. A hidden
occurrence can therefore only be reached or left by a program-order edge. -/
def KeepsCrossThreadEdges (p : Projection xs ys) (profile : RaceProfile) : Prop :=
  ∀ a b : Fin xs.length, xs[a.val].thread ≠ xs[b.val].thread →
    direct profile xs a b = true → p.Retains a ∧ p.Retains b

/-- Coverage of potential race endpoints, including conflicts ordered by HB. -/
def CoversConflicts (p : Projection xs ys) : Prop :=
  ∀ a b : Fin xs.length, a < b → conflicts xs[a.val] xs[b.val] = true →
    p.Retains a ∧ p.Retains b

end Projection

/-- A concrete sufficient visibility condition. Retain every mutex occurrence
and, in the mixed profile, expose every resource used by an atomic access.
Exposure of that resource also retains its intervening plain writes. -/
def Interface.CoversSynchronization (view : Interface L R) (profile : RaceProfile)
    (xs : List (Event T L R)) : Prop :=
  (∀ k : Fin xs.length, ∀ lock, (xs[k.val].action = .acquire lock ∨
    xs[k.val].action = .release lock) → view.lock lock = true) ∧
  (profile = .mixed → ∀ k : Fin xs.length, ∀ loc value,
    (xs[k.val].action = .read .scAtomic loc value ∨
      xs[k.val].action = .write .scAtomic loc value) → view.resource loc = true)

/-- A raw execution supplies a visible trace and keeps its original endpoints. -/
def Interface.ObservedRun [DecidableEq T] [DecidableEq L] [DecidableEq R]
    (view : Interface L R) (start : Config T L R) (ys : List (Event T L R))
    (finish : Config T L R) : Prop :=
  ∃ xs, sc.MTr start xs finish ∧ view.observe xs = ys

end Silmaril.Semantics.TrackA.Concurrency
