module

public import Silmaril.Wasm.Abstract.HostCall.Defs
public import Silmaril.Games.Abstract.StratObs.Defs

/-!
# The closed Core semantics of invocations, host inside: definitions

`Silmaril.Wasm.Abstract.HostStrat` observes an invocation against a host with its exact
host-event log (`CoreObsL`), and `StratHost.linkT` links such an open triple with the host,
interaction hidden. This module defines the closed semantics directly, from Core runs with the
host inside (`Steps`, `Diverges`), with no host log at all:

* `closedEnd P host s q e`: the end `e` of the Core run of the invocation `invoke s q.1 q.2`.
  Values `ws` with the final store `s₂` when the run reaches `⟨s₂, {}, vals ws⟩`; a trap when it
  reaches `⟨s₂, {}, [.trap]⟩` for some `s₂` (`End.trap` carries no store); `div` when the run
  diverges (`Diverges P host`, host steps included: host-free divergence, a host call the host
  diverges on, and infinitely many answered host calls). An uncaught exception is no end: these
  are the finished Core configurations of `CoreObsL`;
* `closedEndXP`: the same with the uncaught exception `⟨s₂, {}, throwing t⟩` as the end
  `.ret (.inr t) s₂`: the finished configurations of `CoreObsLXP`;
* `closedCore P host Ok`, `closedCoreXP P host Ok`: the closed triples over `Sig.empty` on the
  questions `Ok`, with these ends, no pending calls and no streams.

A Core run stuck at a host call that the host has no outcome for has no end and does not
diverge: the closed semantics has no behaviour for it.

Theorems in `Silmaril.Wasm.Abstract.LinkCore.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Execution.Core

variable {H : Type}

/-- **The ends of the closed Core run of an invocation**, host inside: values in the empty frame,
a trap, or divergence. -/
def closedEnd (P : Numerics.Profile) (host : HostSemantics H) (s : Store H) (q : Nat × List Val) :
    End (Store H) (List Val ⊕ Nat) → Prop
  | .ret (.inl ws) s₂ => Steps P host (invoke s q.1 q.2) ⟨s₂, {}, vals ws⟩
  | .ret (.inr _) _ => False
  | .trap => ∃ s₂, Steps P host (invoke s q.1 q.2) ⟨s₂, {}, [.trap]⟩
  | .div => Diverges P host (invoke s q.1 q.2)

/-- **The ends of the closed Core run with exceptions**: `closedEnd`, and an uncaught exception
`throwing t` in the empty frame. -/
def closedEndXP (P : Numerics.Profile) (host : HostSemantics H) (s : Store H)
    (q : Nat × List Val) : End (Store H) (List Val ⊕ Nat) → Prop
  | .ret (.inl ws) s₂ => Steps P host (invoke s q.1 q.2) ⟨s₂, {}, vals ws⟩
  | .ret (.inr t) s₂ => Steps P host (invoke s q.1 q.2) ⟨s₂, {}, throwing t⟩
  | .trap => ∃ s₂, Steps P host (invoke s q.1 q.2) ⟨s₂, {}, [.trap]⟩
  | .div => Diverges P host (invoke s q.1 q.2)

/-- **The closed Core triple** on the questions `Ok`: no imports, no pending calls, no streams. -/
def closedCore (P : Numerics.Profile) (host : HostSemantics H)
    (Ok : Store H → Nat × List Val → Prop) :
    ObsTriple Sig.empty (Store H) (Nat × List Val) (List Val ⊕ Nat) :=
  (fun s q => {x | Ok s q ∧ closedEnd P host s q x.2}, fun _ _ => ∅, fun _ _ => ∅)

/-- **The closed Core triple with exceptions** on the questions `Ok`. -/
def closedCoreXP (P : Numerics.Profile) (host : HostSemantics H)
    (Ok : Store H → Nat × List Val → Prop) :
    ObsTriple Sig.empty (Store H) (Nat × List Val) (List Val ⊕ Nat) :=
  (fun s q => {x | Ok s q ∧ closedEndXP P host s q x.2}, fun _ _ => ∅, fun _ _ => ∅)

end Silmaril.Wasm.Abstract
