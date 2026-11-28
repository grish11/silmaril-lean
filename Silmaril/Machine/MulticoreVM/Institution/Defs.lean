module

public import Silmaril.Logic.Institution.Basic
public import Silmaril.Machine.MulticoreVM.Defs
public import Mathlib.CategoryTheory.Category.Preorder

/-! # Finite trace tests for multicore VMs

See `docs/projects/multicore-vm-institution.md` for the observation profiles and the
Goguen–Burstall satisfaction condition. -/

@[expose] public section

namespace Silmaril.Machine.MulticoreVM.Institution

open CategoryTheory
open Silmaril.Semantics.ConcurrentTrace (Letter Word Trace mapWord mapTrace)

universe u

/-- Finite propositional tests with one atom for each candidate observation. -/
inductive Sentence (Observation : Type u) where
  | truth
  | possible (observation : Observation)
  | neg (sentence : Sentence Observation)
  | conj (left right : Sentence Observation)
  | disj (left right : Sentence Observation)

/-- A behavior model is a set of admitted observations, ordered by inclusion. -/
abbrev Model (Observation : Type u) := Set Observation

namespace Sentence

variable {O P : Type u}

/-- Translate the observation in every atom. -/
def map (f : O → P) : Sentence O → Sentence P
  | .truth => .truth
  | .possible obs => .possible (f obs)
  | .neg φ => .neg (φ.map f)
  | .conj φ ψ => .conj (φ.map f) (ψ.map f)
  | .disj φ ψ => .disj (φ.map f) (ψ.map f)

/-- An atom holds if some behavior realizes it. Negating the atom forbids it. -/
def Holds (M : Model O) : Sentence O → Prop
  | .truth => True
  | .possible obs => obs ∈ M
  | .neg φ => ¬ Holds M φ
  | .conj φ ψ => Holds M φ ∧ Holds M ψ
  | .disj φ ψ => Holds M φ ∨ Holds M ψ

end Sentence

/-- Behavioral reduct by preimage along the map of candidate observations. -/
def reduct {O P : Type u} (f : O → P) (M : Model P) : Model O := f ⁻¹' M

/-- The carriers visible to the observation profiles. State and scheduler choice are
operational parameters of the VM interpretation. -/
structure Sig : Type (u + 1) where
  ThreadId : Type u
  CoreId : Type u
  Event : Type u

/-- Injective thread renaming preserves the independence relation used for concurrent traces.
Core and event maps may identify labels. -/
structure Sig.Hom (A B : Sig.{u}) where
  thread : A.ThreadId ↪ B.ThreadId
  core : A.CoreId → B.CoreId
  event : A.Event → B.Event

instance : Category.{u} Sig.{u} where
  Hom := Sig.Hom
  id A := ⟨Function.Embedding.refl A.ThreadId, id, id⟩
  comp f g := ⟨f.thread.trans g.thread, g.core ∘ f.core, g.event ∘ f.event⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- The named chronological word records thread events and synchronization participants. -/
abbrev Sig.NamedWord (A : Sig.{u}) := Word A.ThreadId A.Event

/-- The concurrent trace is a named word modulo the existing thread-independence swaps. -/
abbrev Sig.ConcurrentTrace (A : Sig.{u}) := Trace A.ThreadId A.Event

/-- The chronological core-and-thread word tags each letter with its emitting core. -/
abbrev Sig.CoreWord (A : Sig.{u}) := List (A.CoreId × Letter A.ThreadId A.Event)

namespace Sig.Hom

variable {A B : Sig.{u}}

/-- Rename a named chronological word, including the participant lists. -/
def mapNamed (f : A ⟶ B) (word : A.NamedWord) : B.NamedWord :=
  mapWord f.thread f.event word

/-- Rename a concurrent trace using the existing quotient map. -/
def mapConcurrent (f : A ⟶ B) (trace : A.ConcurrentTrace) : B.ConcurrentTrace :=
  mapTrace f.thread f.thread.injective f.event trace

/-- Rename the core tag and the letter independently, preserving word order. -/
def mapCore (f : A ⟶ B) (word : A.CoreWord) : B.CoreWord :=
  word.map fun (core, letter) => (f.core core, letter.map f.thread f.event)

end Sig.Hom

/-- Interpret a VM from one initial state by observing the words of all its successful finite
schedules. This existentially hides the final state, scheduler choices and schedule length. -/
def ofVM {State Thread Choice Event O : Type u} (observe : Word Thread Event → O)
    (step : Transition State Thread Choice Event) (initial : State) : Model O :=
  { obs | ∃ schedule word final, Scheduled step schedule initial word final ∧ observe word = obs }

variable {A : Sig.{u}} {State Choice : Type u}

/-- Keep the exact chronological word of the VM. -/
def namedModel (step : Transition State A.ThreadId Choice A.Event) (initial : State) :
    Model A.NamedWord :=
  ofVM id step initial

/-- Observe the concurrent trace class of each actual scheduled word of the VM. -/
def concurrentModel (step : Transition State A.ThreadId Choice A.Event) (initial : State) :
    Model A.ConcurrentTrace :=
  ofVM Semantics.ConcurrentTrace.ofWord step initial

end Silmaril.Machine.MulticoreVM.Institution
