module

public import Silmaril.Games.Strategy.Defs

/-! # Accepted sets of trace models

A program *accepts* an input when, in some execution, it makes an observable move that carries
that input: a call of an `accept` import, or a `true` answer of an `accept` export. Over a trace
model (a set of finite traces, such as the plays of a strategy) acceptance is the
**existential reading**: an input is accepted when *some* trace, against *some* environment,
observes it. A strategy is receptive (every Opponent move is possible after every play), so
quantifying over its plays quantifies over every environment's moves; its plays are finite, so
acceptance is a safety ("may") property, insensitive to divergence.

* `observed obs T`: the values that the partial observation `obs : M → Option α` reads from some
  move of some trace of `T`.
* `obsTraces obs T`: the observable traces, `T` read through `obs` (`List.filterMap`).
  `ObsEquiv obs T T'` (equal observable traces) is the trace equivalence that
  acceptance respects (`observed_eq_of_obsEquiv`); equality and mutual refinement of
  strategies are finer.
* `Strategy.accepted σ obs`: `observed obs σ.plays`.

New definitions (no source). The trace models are Silmaril's game semantics
(`Silmaril.Games.Strategy`, after Koenig and Shao, LICS 2020).
-/

@[expose] public section

namespace Silmaril.Games.Accept

universe u v w

variable {M : Type u} {N : Type v} {α : Type w}

/-- The values observed by `obs` at some move of some trace of `T`. -/
def observed (obs : M → Option α) (T : Set (List M)) : Set α :=
  {a | ∃ s ∈ T, ∃ m ∈ s, obs m = some a}

/-- The observable traces of `T`: each trace read through `obs`. -/
def obsTraces (obs : M → Option α) (T : Set (List M)) : Set (List α) :=
  List.filterMap obs '' T

/-- Observable-trace equivalence of two trace models, possibly over different move types. -/
def ObsEquiv (obs : M → Option α) (obs' : N → Option α) (T : Set (List M)) (T' : Set (List N)) :
    Prop :=
  obsTraces obs T = obsTraces obs' T'

/-- Observable-trace inclusion: every observable trace of `T` is one of `T'`. -/
def ObsRefines (obs : M → Option α) (obs' : N → Option α) (T : Set (List M))
    (T' : Set (List N)) : Prop :=
  obsTraces obs T ⊆ obsTraces obs' T'

end Silmaril.Games.Accept

namespace Silmaril.Games.Strategy

universe u w

variable {E F : Sig.{u}} {α : Type w}

/-- The values a strategy accepts through the observation `obs`: those observed at a move of
some play. -/
def accepted (σ : Strategy E F) (obs : Move E F → Option α) : Set α :=
  Accept.observed obs σ.plays

end Silmaril.Games.Strategy
