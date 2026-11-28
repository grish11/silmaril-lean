module

public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.Order.Closure
public import Mathlib.Order.WithBot
public import Silmaril.Semantics.TrackA.Interaction.Defs

/-! # Explicit and catastrophic UB

The type parameter consists of ordinary observations. It may include errors,
stuckness, deadlock, and divergence. The extra `none` event reports explicit
UB at the boundary where the order is applied.
-/

@[expose] public section

namespace Silmaril.Semantics.TrackA.Interaction.UB

universe u v w

/-- An explicit behavior set has an independent UB marker. -/
abbrev Explicit (T : Type u) := Set (Option T)

/-- At this boundary only a return of `none` is explicit UB. The underlying
tree trace still records its prefix. An ordinary result can itself be an
error, for example when `A = Except Error Value`. -/
def classify {S : Signature} {A : Type*} : Trace S (Option A) → Option (Trace S A)
  | .finite _ (.returned none) => none
  | .finite es (.returned (some a)) => some (.finite es (.returned a))
  | .finite es (.stuck q) => some (.finite es (.stuck q))
  | .finite es (.deadlock kind) => some (.finite es (.deadlock kind))
  | .finite es .diverge => some (.finite es .diverge)
  | .infinite es => some (.infinite es)

/-- Collect explicit UB observations at the whole-run boundary. This
forgets just the prefix of UB runs, which are collapsed to a single marker. -/
def atBoundary {S : Signature} {A : Type*} (runs : Set (Trace S (Option A))) :
    Explicit (Trace S A) :=
  classify '' runs

/-- Global catastrophe: any UB in a set permits all outcomes. This is applied
per row of a trace transformer. -/
def saturate {T : Type u} (s : Explicit T) : Explicit T := {t | t ∈ s ∨ none ∈ s}

def closure (T : Type u) : ClosureOperator (Explicit T) :=
  ClosureOperator.ofPred saturate (fun s => none ∈ s → s = Set.univ)
    (fun _ _ h => Or.inl h)
    (fun _ h => Set.eq_univ_of_forall fun _ => Or.inr (h.elim id id))
    (fun _ _ hs closed _ h => h.elim (fun mem => hs mem) fun hu => closed (hs hu) ▸ Set.mem_univ _)

/-- Saturated behavior sets retain the distinction between safe universal
behavior and a set with UB. The latter is the unique greatest element. -/
abbrev Catastrophic (T : Type u) := (closure T).Closeds

def collapse {T : Type u} : Explicit T → Catastrophic T := (closure T).toCloseds

def insertion (T : Type u) :
    GaloisInsertion (collapse : Explicit T → Catastrophic T) Subtype.val :=
  (closure T).gi

instance {T : Type u} : CompleteLattice (Catastrophic T) :=
  (insertion T).liftCompleteLattice

def pure {T : Type u} (t : T) : Catastrophic T := collapse {some t}

/-- The ordinary outputs of a catastrophic behavior set. Inspect the
UB marker separately to distinguish safe universal behavior from catastrophe. -/
def ordinary {T : Type u} (s : Catastrophic T) : Set T := {t | some t ∈ s.val}

/-- Exact sequencing for explicit UB. An input UB propagates. An ordinary
intermediate trace selects the corresponding continuation. -/
def bindExplicit {T : Type u} {U : Type v} (s : Explicit T) (k : T → Explicit U) :
    Explicit U :=
  {out | (out = none ∧ none ∈ s) ∨ ∃ t, some t ∈ s ∧ out ∈ k t}

/-- Saturate after exact sequencing. -/
def bind {T : Type u} {U : Type v} (s : Catastrophic T) (k : T → Catastrophic U) :
    Catastrophic U :=
  collapse (bindExplicit s.val (fun t => (k t).val))

/-- The nonempty fragment consists of safe nonempty sets of ordinary traces,
together with the catastrophic top. -/
abbrev Nonempty (T : Type u) := {s : Catastrophic T // s.val.Nonempty}

namespace Nonempty

def pure {T : Type u} (t : T) : Nonempty T := ⟨UB.pure t, ⟨some t, Or.inl rfl⟩⟩

def ub (T : Type u) : Nonempty T :=
  ⟨collapse {none}, ⟨none, Or.inl rfl⟩⟩

def bind {T : Type u} {U : Type v} (s : Nonempty T) (k : T → Nonempty U) : Nonempty U :=
  ⟨UB.bind s.val (fun t => (k t).val), by
    rcases s.property with ⟨_ | t, input⟩
    · exact ⟨none, Or.inl (Or.inl ⟨rfl, input⟩)⟩
    · obtain ⟨out, output⟩ := (k t).property
      exact ⟨out, Or.inl (Or.inr ⟨t, input, output⟩)⟩⟩

end Nonempty

/-- Interpret a newly adjoined bottom as the empty behavior set. -/
def addBottom {T : Type u} : WithBot (Nonempty T) → Catastrophic T :=
  WithBot.recBotCoe ⊥ Subtype.val

/-- A transformer from each input trace to nonempty ordinary outputs or UB. -/
abbrev Arrow (T : Type u) (U : Type v) := T → Nonempty U

def Arrow.id (T : Type u) : Arrow T T := Nonempty.pure

/-- Diagrammatic sequencing. `f` runs first. -/
def Arrow.then {T : Type u} {U : Type v} {V : Type w} (f : Arrow T U) (g : Arrow U V) :
    Arrow T V :=
  fun t => (f t).bind g

end Silmaril.Semantics.TrackA.Interaction.UB
