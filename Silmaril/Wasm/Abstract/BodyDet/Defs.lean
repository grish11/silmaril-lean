module

public import Silmaril.Wasm.Abstract.BodyStrat.Defs

/-!
# Deterministic observation triples

An observation triple `t : ObsTriple E S A B` (finished behaviours, pending
calls, productive runs) is *deterministic given answers*, `TripleDet t`, when

* (a) `fin`: the finished behaviours are deterministic given the history
  (`AFun.Det`): two of them agree until the environment answers differently;
* (b) `pend`: after a given call log there is at most one pending call;
* (c) `excl`: a call log is never both the log of a finished behaviour (of
  any end: return, trap or silent divergence) and followed by a pending call;
* (d) `inf`: every finite prefix of a productive run is pending, with the
  call the run makes next.

Clauses (b) and (c) only compare one call log. For a **saturated** triple
(`StratObs.Saturated`: every call prefix forced by a finished behaviour,
pending call or productive run is pending) the cross-log forms follow: a
pending call agrees with the next call of every finished behaviour extending
its log, and a productive run agrees with every finished behaviour, pending
call and productive run until the answers differ
(`Silmaril.Wasm.Abstract.BodyDet.Thms`).

`PDet σ` says a strategy has at most one Proponent move after each play.

**Scope.** This is determinism *given the environment's answers*: the
answers are inputs, and the function's own moves are functions of them. It
covers interaction-tree bodies (`BodyM`). Nondeterministic semantic profiles
(several possible results for one history, as in the core's relaxed or NaN
profiles) are not deterministic in this sense; they need a nondeterministic
strategy variant, which is not covered here.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract.BodyDet

open Silmaril.Games Silmaril.Games.Abstract

universe u

/-- A triple deterministic given answers. -/
structure TripleDet {E : Sig.{u}} {S A B : Type u} (t : ObsTriple E S A B) : Prop where
  /-- (a) Finished behaviours agree until the answers differ. -/
  fin : AFun.Det t.1
  /-- (b) At most one pending call after each call log. -/
  pend : ∀ s a c m m', (c, m) ∈ t.2.1 s a → (c, m') ∈ t.2.1 s a → m = m'
  /-- (c) No call log both ends a finished behaviour and has a pending call. -/
  excl : ∀ s a c e m, (c, e) ∈ t.1 s a → (c, m) ∈ t.2.1 s a → False
  /-- (d) Every prefix of a productive run is pending with the run's next call. -/
  inf : ∀ s a ω, ω ∈ t.2.2 s a → ∀ k, (streamTake ω k, (ω k).1) ∈ t.2.1 s a

/-- A strategy with at most one Proponent move after each play. -/
def PDet {E F : Sig.{u}} (σ : Strategy E F) : Prop :=
  ∀ p o o', p ++ [o] ∈ σ → p ++ [o'] ∈ σ → o.IsP → o'.IsP → o = o'

end Silmaril.Wasm.Abstract.BodyDet
