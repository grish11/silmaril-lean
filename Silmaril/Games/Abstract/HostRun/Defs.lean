module

public import Silmaril.Games.Abstract.Function.Defs

/-!
# Running an abstract function against a relational host

An abstract function (`AFun`) lists its finished call behaviours. Import
calls are recorded with their answers, and nothing is assumed about who
answers. Its **pending calls** (`Pending`) are the import calls it makes after
a finite answered prefix; they are the `fin s .run` prefix observations of
`Silmaril.Games.Abstract.Outcome` and `toPending` of
`Silmaril.Wasm.Abstract.BodyTrace`.

A **host** is a relation `HostRel E`: at each import call it may answer with a
value (`HostAns.answer`), diverge (`HostAns.diverge`), or have no outcome at
all. Hosts are not assumed deterministic or total.

`hostObs R f p` is what running `f` against `R` can show. There are three
observations:

* `done cs e`: a finished behaviour whose every answer `R` allows. Its end `e`
  is a return with the final state, a trap, or divergence *inside* `f`.
* `hostDiv cs m`: after the answered prefix `cs`, `f` calls `m`, and the host
  may diverge there. This is divergence *while waiting* at a pending import;
  filtering finished behaviours alone cannot show it.
* `blocked cs m`: after `cs`, `f` calls `m`, and the host has no outcome for
  it. The run is stuck. This is not divergence and not a trap.

`DetP f p` is determinism given the answers: any two runs, finished or pending,
agree up to the first import answer on which they differ, final state
included. For a functional host it makes the observation unique
(`Silmaril.Games.Abstract.HostRun.Thms`).
-/

@[expose] public section

namespace Silmaril.Games.Abstract

open Silmaril.Games

universe u

/-- A host outcome at an import call: an answer, or divergence. -/
inductive HostAns (X : Type u) : Type u
  | answer (x : X)
  | diverge

/-- A relational host: the outcomes it allows at each import call. -/
abbrev HostRel (E : Sig.{u}) : Type u := (m : E.Op) → HostAns (E.Ar m) → Prop

/-- Pending calls: after the answered calls, the import being called. -/
abbrev Pending (E : Sig.{u}) (S A : Type u) : Type u := S → A → Set (List (Call E) × E.Op)

/-- What running against a host can show. -/
inductive HObs (E : Sig.{u}) (S B : Type u) : Type u
  /-- A finished behaviour with allowed answers. -/
  | done (cs : List (Call E)) (e : End S B)
  /-- Divergence of the host while answering the pending call `m`. -/
  | hostDiv (cs : List (Call E)) (m : E.Op)
  /-- No host outcome for the pending call `m`: stuck. -/
  | blocked (cs : List (Call E)) (m : E.Op)

namespace HostRel

variable {E : Sig.{u}}

/-- Every answer in the list is allowed. -/
def Consistent (R : HostRel E) (cs : List (Call E)) : Prop := ∀ c ∈ cs, R c.1 (.answer c.2)

/-- At most one outcome per call. -/
def Functional (R : HostRel E) : Prop := ∀ m o o', R m o → R m o' → o = o'

/-- The host of a function answering every call. -/
def ofHost (h : Host E) : HostRel E := fun m o => o = .answer (h m)

end HostRel

/-- **Running against a relational host.** -/
def hostObs {E : Sig.{u}} {S A B : Type u} (R : HostRel E) (f : AFun E S A B) (p : Pending E S A) :
    S → A → Set (HObs E S B) := fun s a =>
  {o | (∃ cs e, o = .done cs e ∧ (cs, e) ∈ f s a ∧ R.Consistent cs) ∨
    (∃ cs m, o = .hostDiv cs m ∧ (cs, m) ∈ p s a ∧ R.Consistent cs ∧ R m .diverge) ∨
    (∃ cs m, o = .blocked cs m ∧ (cs, m) ∈ p s a ∧ R.Consistent cs ∧ ∀ ans, ¬ R m ans)}

/-- A run, finished (`inl`) or pending at a call (`inr`). -/
abbrev PRun (E : Sig.{u}) (S B : Type u) : Type u := List (Call E) × (End S B ⊕ E.Op)

/-- The run of an observation. -/
def HObs.run {E : Sig.{u}} {S B : Type u} : HObs E S B → PRun E S B
  | .done cs e => (cs, .inl e)
  | .hostDiv cs m => (cs, .inr m)
  | .blocked cs m => (cs, .inr m)

/-- Two runs agree as long as the answers agree: same calls; while the
answers are equal, the same continuation; the same end or pending call; and a
pending call is the next call of a longer run. -/
def PAgree {E : Sig.{u}} {S B : Type u} : List (Call E) → End S B ⊕ E.Op → List (Call E) →
    End S B ⊕ E.Op → Prop
  | [], .inl e₁, [], .inl e₂ => e₁ = e₂
  | [], .inr m₁, [], .inr m₂ => m₁ = m₂
  | [], .inr m, c :: _, _ => m = c.1
  | c :: _, _, [], .inr m => c.1 = m
  | ⟨m₁, n₁⟩ :: c₁, x₁, ⟨m₂, n₂⟩ :: c₂, x₂ => m₁ = m₂ ∧ (HEq n₁ n₂ → PAgree c₁ x₁ c₂ x₂)
  | _, _, _, _ => False

/-- The runs of a function: finished behaviours and pending calls. -/
def runs {E : Sig.{u}} {S A B : Type u} (f : AFun E S A B) (p : Pending E S A) (s : S) (a : A) :
    Set (PRun E S B) :=
  {x | (∃ cs e, x = (cs, .inl e) ∧ (cs, e) ∈ f s a) ∨ ∃ cs m, x = (cs, .inr m) ∧ (cs, m) ∈ p s a}

/-- **Determinism given the answers**, finished and pending runs together. -/
def DetP {E : Sig.{u}} {S A B : Type u} (f : AFun E S A B) (p : Pending E S A) : Prop :=
  ∀ s a x y, x ∈ runs f p s a → y ∈ runs f p s a → PAgree x.1 x.2 y.1 y.2

end Silmaril.Games.Abstract
