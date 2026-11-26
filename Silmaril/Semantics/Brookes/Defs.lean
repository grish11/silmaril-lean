module

/-! # Finite shared-store transition traces

Brookes's finite trace model and its return-bearing formulation by
Dvir, Kammar, Lahav and Plotkin. The store type is a parameter.
-/

@[expose] public section

namespace Silmaril.Semantics.Brookes

universe u v w

/-- A program segment's required input store and guaranteed output store. -/
abbrev Transition (Store : Type u) := Store × Store

/-- A word of program segments. Successive segments may have different stores
on either side of their boundary, where the environment can intervene.
The empty list is available for contexts; accepted behaviors are nonempty. -/
abbrev Trace (Store : Type u) := List (Transition Store)

variable {Store : Type u} {A : Type v} {B : Type w}

/-- The two directed trace deductions, in arbitrary left and right contexts. -/
inductive Rewrite : Trace Store → Trace Store → Prop where
  | stutter (pre post : Trace Store) (s : Store) :
      Rewrite (pre ++ post) (pre ++ (s, s) :: post)
  | mumble (pre post : Trace Store) (s t u : Store) :
      Rewrite (pre ++ (s, t) :: (t, u) :: post) (pre ++ (s, u) :: post)

/-- Finitely many deductions, including zero. -/
inductive Reduces : Trace Store → Trace Store → Prop where
  | refl (trace : Trace Store) : Reduces trace trace
  | tail {source middle target : Trace Store} :
      Reduces source middle → Rewrite middle target → Reduces source target

theorem Reduces.trans {first middle last : Trace Store}
    (h₁ : Reduces first middle) (h₂ : Reduces middle last) : Reduces first last := by
  induction h₂ with
  | refl => exact h₁
  | tail _ step ih => exact ih.tail step

/-- Saturation keeps the result fixed across all deductions. -/
def close (seed : Trace Store → A → Prop) (trace : Trace Store) (value : A) : Prop :=
  ∃ source, seed source value ∧ Reduces source trace

/-- Sets of nonempty complete traces with a terminal value. -/
structure Behavior (Store : Type u) (Result : Type v) where
  accepts : Trace Store → Result → Prop
  nonempty : ∀ ⦃trace value⦄, accepts trace value → trace ≠ []
  stable : ∀ ⦃source target value⦄, accepts source value → Reduces source target →
    accepts target value

/-- Order-preserving interleaving of two words, with one side taking each step. -/
inductive Shuffle {Step : Type u} : List Step → List Step → List Step → Prop where
  | nil : Shuffle [] [] []
  | left {xs ys zs : List Step} (step : Step) :
      Shuffle xs ys zs → Shuffle (step :: xs) ys (step :: zs)
  | right {xs ys zs : List Step} (step : Step) :
      Shuffle xs ys zs → Shuffle xs (step :: ys) (step :: zs)

/-- A word can run on one store with no external interference. -/
inductive Runs : Store → Trace Store → Store → Prop where
  | nil (s : Store) : Runs s [] s
  | cons {s t u : Store} {trace : Trace Store} :
      Runs t trace u → Runs s ((s, t) :: trace) u

namespace Behavior

private theorem nonempty_of_reduces {source target : Trace Store}
    (hne : source ≠ []) (h : Reduces source target) : target ≠ [] := by
  cases h with
  | refl => exact hne
  | tail _ step => cases step <;> simp

/-- Generate a behavior from its nonempty seeds. -/
def generate (seed : Trace Store → A → Prop) : Behavior Store A where
  accepts := close (fun trace value => trace ≠ [] ∧ seed trace value)
  nonempty := by
    rintro _ _ ⟨_, ⟨hne, _⟩, h⟩
    exact nonempty_of_reduces hne h
  stable := by
    rintro _ _ _ ⟨origin, hseed, h⟩ step
    exact ⟨origin, hseed, h.trans step⟩

/-- A single atomic store transition with a result, saturated as a behavior. -/
def atomic (step : Store → Store → A → Prop) : Behavior Store A :=
  generate fun trace value => ∃ s t, trace = [(s, t)] ∧ step s t value

/-- Returning uses one identity transition at an arbitrary store. -/
def ret (value : A) : Behavior Store A :=
  atomic fun s t result => s = t ∧ result = value

/-- Concatenate into the continuation selected by the terminal value.
The environment may intervene at the join. -/
def bind (first : Behavior Store A) (next : A → Behavior Store B) : Behavior Store B :=
  generate fun trace result =>
    ∃ left right value, first.accepts left value ∧ (next value).accepts right result ∧
      trace = left ++ right

/-- Keep the complete transition word and existentially forget the value. -/
def forget (behavior : Behavior Store A) : Behavior Store Unit where
  accepts := fun trace _ => ∃ value, behavior.accepts trace value
  nonempty := by
    rintro _ _ ⟨_, h⟩
    exact behavior.nonempty h
  stable := by
    rintro _ _ _ ⟨value, h⟩ step
    exact ⟨value, behavior.stable h step⟩

/-- An initial-to-final observation with no external interference. -/
def completes (behavior : Behavior Store A) (s t : Store) (value : A) : Prop :=
  behavior.accepts [(s, t)] value

end Behavior

/-- Commands have no result information beyond successful completion. -/
abbrev Command (Store : Type u) := Behavior Store Unit

namespace Command

/-- The identity command. -/
def skip : Command Store := Behavior.ret ()

/-- Sequential composition on one shared store. -/
def seq (first second : Command Store) : Command Store :=
  first.bind fun _ => second

/-- Interleave and then saturate. A gap in the shuffled word still admits
environmental interference. -/
def parallel (first second : Command Store) : Command Store :=
  Behavior.generate fun trace _ =>
    ∃ left right, first.accepts left () ∧ second.accepts right () ∧ Shuffle left right trace

end Command
end Silmaril.Semantics.Brookes
