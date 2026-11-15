module

public import Silmaril.Games.Abstract.HostRun.Defs
import Silmaril.Proofs.Games.Abstract.HostRun.Basic

/-!
# Running against a relational host: theorems

* `hostObs_unique`: **trace-indexed determinism**. A function deterministic
  given the answers (`DetP`, finished and pending runs together) has at most
  one observation against a functional host. This includes the final state of
  a return, and it distinguishes a finished run, divergence of the host at a
  pending call, and a host with no outcome there.
* `hostObs_ofHost`: against a host *function* (every call answered, never
  diverging) the observations are exactly the finished behaviours of
  `AFun.under`. That is the only case where filtering finished behaviours is
  the whole story.

No totality or determinism of the host is assumed elsewhere. `hostObs` is
defined for every relation: a host may allow several answers, divergence, or
nothing.

`DetP` is determinism given the answers to *every* event of `E`. If `E` mixes
public imports with internal choice events (numeric nondeterminism,
`memory.grow`), then `hostObs_unique` needs a functional relation on all of
them. Hiding the internal events first does not preserve `DetP`.
-/

public section

namespace Silmaril.Games.Abstract

open Silmaril.Games

universe u

variable {E : Sig.{u}} {S A B : Type u}

/-- **Trace-indexed determinism**: one observation at most. -/
theorem hostObs_unique {R : HostRel E} (hR : R.Functional) {f : AFun E S A B} {p : Pending E S A}
    (hD : DetP f p) {s : S} {a : A} {o o' : HObs E S B} (h : o ∈ hostObs R f p s a)
    (h' : o' ∈ hostObs R f p s a) : o = o' :=
  Silmaril.Proofs.Games.Abstract.HostRun.hostObs_unique hR hD h h'

/-- Against a host function the observations are the finished behaviours of
`AFun.under`. -/
theorem hostObs_ofHost (h : Host E) (f : AFun E S A B) (p : Pending E S A) (s : S) (a : A)
    (o : HObs E S B) :
    o ∈ hostObs (HostRel.ofHost h) f p s a ↔ ∃ x ∈ AFun.under h f s a, o = .done x.1 x.2 :=
  Silmaril.Proofs.Games.Abstract.HostRun.hostObs_ofHost h f p s a o

end Silmaril.Games.Abstract
