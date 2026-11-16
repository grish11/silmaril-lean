module

public import Silmaril.Wasm.Component.DWiringChatter2.Defs

/-!
# Infinite plays of `ext`, routed: definitions

`DStrategy.ext e D N = D.comp (extTop e N)`. An infinite play of a composite
is the visible limit of an infinite interaction, in which each component
either moves forever (and plays one of its infinite plays) or stops (in one of
its finite plays). This module names these readings, so that the infinite
plays of `ext e D N` can be stated without chains of interactions and without
`ThroughAbove`.

* `prefixes s`: the prefixes of a finite play `s`, read as a trace that stops.
* `IsRun δ I`: `I` is an infinite play of `δ`, or the prefixes of one of its
  finite plays.
* `Interleaved I K J`: the traces `I` and `K` interact with visible trace `J`:
  members of the three can always be extended together to an interacting
  triple. Each of them is then the limit of the interacting triples.
-/

@[expose] public section

namespace Silmaril.Wasm.Component

open Silmaril.Games

universe u v w

/-- The prefixes of a finite trace: a trace that stops at `s`. -/
def prefixes {α : Type u} (s : List α) : Set (List α) := {t | t <+: s}

/-- **A run of `δ`**: one of its infinite plays, or the prefixes of one of its
finite plays (the component stops there). -/
def IsRun {E F : Sig.{u}} (δ : DStrategy E F) (I : Set (List (Move E F))) : Prop :=
  I ∈ δ.inf ∨ ∃ s ∈ δ.toStrategy, I = prefixes s

/-- **`I` and `K` interact with visible trace `J`**: any members of `I`, `K`
and `J` extend, within them, to members `s`, `c`, `p` with `Zip s c p`. -/
def Interleaved {α : Type u} {β : Type v} {γ : Type w} (I : Set (List (α ⊕ β)))
    (K : Set (List (β ⊕ γ))) (J : Set (List (α ⊕ γ))) : Prop :=
  ∀ s ∈ I, ∀ c ∈ K, ∀ p ∈ J, ∃ s' ∈ I, ∃ c' ∈ K, ∃ p' ∈ J,
    s <+: s' ∧ c <+: c' ∧ p <+: p' ∧ Zip s' c' p'

end Silmaril.Wasm.Component
