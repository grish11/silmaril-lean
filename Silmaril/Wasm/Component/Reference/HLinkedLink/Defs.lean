module

public import Silmaril.Wasm.Component.Reference.HLinkedSessionObj.Defs
public import Silmaril.Wasm.Component.Reference.LinkedGLink.Defs
public import Silmaril.Games.Abstract.SessionExt.Defs
public import Silmaril.Games.Abstract.SessionLink.Defs
public import Silmaril.Games.Abstract.SessionLinkAssoc.Defs

/-!
# Linked components with host imports through the generic session link: definitions

**Scope.** `HLinked2` (`HLinkedSession.Defs`) at the core instances `Ie` of the exporter and `Ii`
of the importer, every profile `P`. The session objects of `HLinkedSessionObj.Defs` are built
from the specification (`SessSpec`, `RoundDivC`, `RoundInfC`). This topic builds the same
behaviours from the generic link `SessionLink.linkS` of a server and a client, with the host
imports passed through as visible calls.

## The client: the importer's own triple

`HLinked2.clientH P l Ii := SimpleI.impTripleS P l.imp l.wireH Ii` (`LinkedGLink`), the importer
alone, its lower calls at the session interface `sigS = sig1 (Nat × Payload) Payload`. Its wiring
`l.wireH = l.wire ++ l.hostWire` sends a wired import `n` to the exporter's export `wire[n]` and
the host import `wire.length + i` to the question index `N + i`, `N = l.exp.exports.length`
(`hostWire`): one index space for the exporter's exports and the host imports.

## The server: host passthrough beside the exporter

`HLinked2.serverO P l Ie := SessionExt.routeS l.route l.hostPass (l.expTripleH P Ie)` on the host
interface `sigN l.host.length`, over the store `PUnit × Store Nat`:

* `hostPass := SessionRoute.callS id (fun _ n => ExpSpec.sumAns n)`: the one-call session that
  asks the host call `m` itself and returns its answer (a refusal `none` is the trap `.inr ()`);
* `expTripleH P l Ie`: the exporter's session triple `(Simple.expSpec l.exp Ie).sessTripleS P`
  (`LinkedGSession`), which makes no calls, read on the host interface (its logs are empty);
* `route`: the question `(N + i, p)` with `i < host.length` asks the host call `(i, p)` (`.inl`),
  every other question goes to the exporter (`.inr`). `SessionExt.routeS` is
  `SessionRoute.mapS route (fun _ => foldS) (StratSession.pairS hostPass expTripleH)`.

`HLinked2.linkO P l Ie Ii := linkS (serverO P l Ie) (clientH P l Ii)`, over the store
`(PUnit × Store Nat) × Store Nat`; `storeEquiv` reorders it to the store `(u, π)` (importer,
exporter) of `HLinked2.compTripleO`.

## The open triple before restriction

`HLinked2.compTripleOR P l Ie Ii` is the saturated triple whose legal restriction is
`HLinked2.compTripleO` (`compInfO`: the host chatter `RoundInfC` of typed questions); `compTripleO`
inlines it.

## The realizable restriction

`HLinked2.realize h t` turns a triple `t` over the stores `(u, π)` on the host interface
`sigN h.length` into one over `(u, π, R)` (`R`: the calls refused since the last answer), as
`HLinked2.compFin`/`compInf` do with the open behaviours: a behaviour whose host calls are a
`VisRun` from `R` to `R'` ends at `R'`; a behaviour returning the trap after a last refused call
`m` forced at `R'` (`Forced`) is kept with that call hidden; a stream is kept when all its prefixes
are `VisRun`s. Then it is saturated (`StratObs.sat`).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
open Silmaril.Games.Abstract.SessionLink (linkS)
open Silmaril.Wasm.Component
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Game (ScalarInstance)
open Silmaril.Wasm.Execution.Core (Store)

namespace HLinked2

variable (P : Profile) (l : HLinked2)

/-! ## The open triple before restriction -/

/-- **The productive streams of the open triple**: the host chatter of a typed question. -/
def compInfO (Ie Ii : ScalarInstance) :
    PInf (sigN l.host.length) (Store Nat × Store Nat) (Nat × Payload) := fun s q =>
  match l.toL2.typedQ q with
  | none => ∅
  | some (j, vs) => {ω | RoundInfC P l Ie Ii s.1 s.2 j vs ω}

/-- **The open triple on the host interface**, before the legal restriction: the saturation of
`compFinO` and `compInfO`. -/
def compTripleOR (Ie Ii : ScalarInstance) :
    ObsTriple (sigN l.host.length) (Store Nat × Store Nat) (Nat × Payload) (Payload ⊕ PUnit.{1}) :=
  sat (compFinO P l Ie Ii, fun _ _ => ∅, compInfO P l Ie Ii)

/-! ## The client -/

/-- The question indices of the host imports: `N + i` for host import `i`, after the `N` exports
of the exporter. -/
def hostWire : List Nat := List.ofFn fun i : Fin l.host.length => l.exp.exports.length + i.val

/-- **The wiring of all imports of the importer**: the wired imports to the exporter's exports,
the host imports to the indices `hostWire`. -/
def wireH : List Nat := l.wire ++ l.hostWire

/-- **The client**: the importer's own session triple, every import call a question on `sigS`. -/
def clientH (Ii : ScalarInstance) :
    ObsTriple sigS (Store Nat) (Nat × Payload) (Payload ⊕ PUnit.{1}) :=
  SimpleI.impTripleS P l.imp l.wireH Ii

/-! ## The server -/

/-- **The routing of the client's questions**: `(N + i, p)` asks host call `(i, p)`, any other
question goes to the exporter. -/
def route (q : Nat × Payload) : (sigN l.host.length).Op ⊕ (Nat × Payload) :=
  if h : l.exp.exports.length ≤ q.1 ∧ q.1 - l.exp.exports.length < l.host.length then
    .inl (⟨q.1 - l.exp.exports.length, h.2⟩, q.2)
  else .inr q

/-- **The host passthrough**: ask the host call itself, return its answer (`none` as a trap). -/
def hostPass :
    ObsTriple (sigN l.host.length) PUnit.{1} (sigN l.host.length).Op (Payload ⊕ PUnit.{1}) :=
  SessionRoute.callS id fun _ n => ExpSpec.sumAns n

/-- **The exporter's session triple on the host interface**: it makes no calls. -/
def expTripleH (Ie : ScalarInstance) :
    ObsTriple (sigN l.host.length) (Store Nat) (Nat × Payload) (Payload ⊕ PUnit.{1}) :=
  (fun s q => {x | x.1 = [] ∧ ([], x.2) ∈ ((Simple.expSpec l.exp Ie).sessTripleS P).1 s q},
    fun _ _ => ∅, fun _ _ => ∅)

/-- **The server**: the host passthrough beside the exporter, questions routed by `route`. -/
def serverO (Ie : ScalarInstance) :
    ObsTriple (sigN l.host.length) (PUnit.{1} × Store Nat) (Nat × Payload) (Payload ⊕ PUnit.{1}) :=
  SessionExt.routeS l.route l.hostPass (l.expTripleH P Ie)

/-- **The generic link**: the server serving the client. -/
def linkO (Ie Ii : ScalarInstance) :
    ObsTriple (sigN l.host.length) ((PUnit.{1} × Store Nat) × Store Nat) (Nat × Payload)
      (Payload ⊕ PUnit.{1}) :=
  linkS (l.serverO P Ie) (l.clientH P Ii)

/-- The stores of the link, `((), π)` and `u`, as the stores `(u, π)` of the open triple. -/
def storeEquiv : (PUnit.{1} × Store Nat) × Store Nat ≃ Store Nat × Store Nat :=
  (Equiv.prodCongr (Equiv.punitProd (Store Nat)) (Equiv.refl (Store Nat))).trans
    (Equiv.prodComm (Store Nat) (Store Nat))

/-! ## The realizable restriction -/

/-- A store `(u, π)` with the refusals `R`. -/
def attachR {h : Iface} {B : Type} (R : List (sigN h.length).Op) :
    End (Store Nat × Store Nat) B → End (Store Nat × Store Nat × List (sigN h.length).Op) B
  | .ret b s => .ret b (s.1, s.2, R)
  | .trap => .trap
  | .div => .div

/-- **The realizable restriction** of a triple over the stores `(u, π)`: behaviours whose host
calls are a `VisRun`, those returning the trap after a last refused call forced at the end of a
`VisRun` with that call hidden, and streams all of whose prefixes are `VisRun`s; saturated. -/
def realize (h : Iface)
    (t : ObsTriple (sigN h.length) (Store Nat × Store Nat) (Nat × Payload) (Payload ⊕ PUnit.{1})) :
    ObsTriple (sigN h.length) (Store Nat × Store Nat × List (sigN h.length).Op) (Nat × Payload)
      (Payload ⊕ PUnit.{1}) :=
  sat (fun s q => {x |
      (∃ (R' : List (sigN h.length).Op) (e : End (Store Nat × Store Nat) (Payload ⊕ PUnit.{1})),
        (x.1, e) ∈ t.1 (s.1, s.2.1) q ∧ VisRun h s.2.2 x.1 R' ∧ x.2 = attachR R' e) ∨
      (∃ (m : (sigN h.length).Op) (R' : List (sigN h.length).Op) (σ : Store Nat × Store Nat),
        (x.1 ++ [⟨m, none⟩], .ret (.inr PUnit.unit) σ) ∈ t.1 (s.1, s.2.1) q ∧
        VisRun h s.2.2 x.1 R' ∧ Forced h R' m ∧ x.2 = .ret (.inr PUnit.unit) (σ.1, σ.2, R'))},
    fun _ _ => ∅,
    fun s q => {ω | ω ∈ t.2.2 (s.1, s.2.1) q ∧
      ∀ n, ∃ R' : List (sigN h.length).Op, VisRun h s.2.2 (streamTake ω n) R'})

end HLinked2

end Silmaril.Wasm.Component.Reference
