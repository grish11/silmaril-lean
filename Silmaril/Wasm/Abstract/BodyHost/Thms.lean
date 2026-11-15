module

public import Silmaril.Wasm.Abstract.BodyTrace.Thms
public import Silmaril.Games.Abstract.HostRun.Thms
import Silmaril.Proofs.Wasm.Abstract.BodyHost.Det

/-!
# Interaction-tree bodies against a relational host: theorems

This is the link from `BodyM` bodies (`Silmaril.Wasm.Abstract.BodyTrace`) to
the host observations of `Silmaril.Games.Abstract.HostRun`. A body's inputs to
`hostObs` are its finished behaviours `toAFun f` and its pending calls
`toPending f`.

* `body_detP`: **a body is deterministic given the answers** (`DetP`), over
  finished paths and pending calls together. Two runs of one tree agree until
  the first import answer on which they differ, final state included.
* `body_hostObs_unique`: so against a functional host a body has at most one
  observation. That observation is one of: finished; the host diverging at a
  pending import; the host having no outcome there.

A host may be any relation; only `body_hostObs_unique` assumes it
functional. Nothing here relates bodies to Core 3.0 host calls; that is the
simulation stage.

**Scope of `DetP`.** It is a property of *raw* bodies only. A body is
deterministic given the answers to **all** of its events, including events
that model internal choices: a nondeterministic numeric result such as a NaN
payload, or the outcome of `memory.grow`. It says nothing once such events are
hidden or quantified away. It also says nothing about a Region `Run` or Core
3.0 under a nondeterministic numerics profile. Core with a relational host may
be nondeterministic even when every body is `DetP`.

Public imports and internal choices are different. A use of `hostObs` should
treat only the public import events as host calls. Internal choice events
should be resolved or quantified separately, under the numerics profile in
force. Uniqueness of a Core observation needs that profile to be deterministic
(the Core lemmas assume `profile o` or a closed native profile). It does not
follow from `body_detP` alone.
-/

public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Abstract.Body
  Silmaril.Wasm.Abstract.BodyTrace

universe u

/-- **Bodies are deterministic given the answers**, finished and pending runs
together. -/
theorem body_detP {E : Sig.{u}} {S T A B : Type (u + 1)} (f : Hom E S T A B) :
    DetP (toAFun f) (toPending f) :=
  Silmaril.Proofs.Wasm.Abstract.BodyHost.detP f

/-- **A body against a functional host has at most one observation.** -/
theorem body_hostObs_unique {E : Sig.{u}} {S T A B : Type (u + 1)} (f : Hom E S T A B)
    {R : HostRel (liftSig E)} (hR : R.Functional) {s : S} {a : A} {o o' : HObs (liftSig E) S B}
    (h : o ∈ hostObs R (toAFun f) (toPending f) s a)
    (h' : o' ∈ hostObs R (toAFun f) (toPending f) s a) : o = o' :=
  hostObs_unique hR (body_detP f) h h'

end Silmaril.Wasm.Abstract
