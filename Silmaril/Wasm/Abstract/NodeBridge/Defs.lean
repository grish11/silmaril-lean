module

public import Silmaril.Wasm.Abstract.InstSessionD.Defs
public import Silmaril.Wasm.Abstract.HostSessionXP.Defs

/-!
# Core 3.0 instances seen through the Core host interface: definitions

A scalar Core 3.0 instance `I : ScalarInstance` has two readings as a session source.

* **Value level, open** (`Silmaril.Wasm.Abstract.InstSession`): `instTripleS I P`, on the import
  signature `I.E = ifaceSig I.imports`. An import call is a function index with typed arguments,
  answered by an `Answer` (typed values, a trap, or an uncaught exception). The environment
  never sees nor changes the instance store. This is the node session of `core3SemD P`.
* **Core host interface, against a fixed host** (`Silmaril.Wasm.Abstract.HostStrat`,
  `HostSessionXP`): `coreTripleSXP P host Ok`, on `wasmHostSig Nat`. A host call
  `(hh, s, us)` carries the store `s` at the callout, and is answered `(s', r)` with a new store.
  Its logs are the host-consistent ones.

This module relates them.

## The universal store-preserving host

`StorePreserving host`: every answer of `host` leaves the store unchanged. `instHost I` is the
**universal store-preserving typed host of `I`**: it answers a callout `hh us` with typed arguments
(`I.importOp? hh us = some e`) by any answer `v` of the import type, as the Core result
`v.toResult`, leaving the store unchanged. It never diverges, and it has no outcome for an
ill-typed callout. Every store-preserving, store-oblivious host that answers well-typed values is
a sub-relation of it. Closing the Core triple against `instHost I` restricts nothing that a
component environment can do, so the Core triple at `instHost I` is again open.

## The view

`CallView I x ev`: the instance import call `x = ⟨e, v⟩` is the view of the Core host event
`ev = ⟨(hh, s, us), (s', r)⟩`: the callout `hh us` is the typed import question `e`, the answer
keeps the store (`s' = s`), and `r = v.toResult`. It is a partial function from host events to
import calls (`importOp?` is a function and `toResult` is injective); the store `s` of the event
is forgotten.

* `qOf I a`: the Core question `(I.addr a.1, args)` of the export question `a`.
* `resOf`/`cAns`: the bijection between the session answers `(List Val ⊕ Nat) ⊕ PUnit` of the
  Core triples and Core results (values, exception, trap).
* `viewEnd I a`: the end of a Core activation of `qOf I a` read as an end of `instTripleS I P`
  at `a`: a return keeps its store, its result read by `Answer.ofResult?` (`none` for ill-typed
  values) and tagged by `sAns a`.
* `viewTriple I t`: the image of a Core session triple `t` under the view, as a triple on
  `I.E`: finished behaviours, pending calls and productive streams whose events and ends have a
  view.

## The open Core triple

`coreTripleSXP P host Ok` keeps as pending calls only the callouts that `host` leaves unanswered
(`blocked`) or diverges on (`hostDiv`); an answered callout is a call prefix of the behaviours
that follow it. `instTripleS I P` keeps every reached callout as a pending call. `coreTripleSO P
host` is `coreTripleSXP P host` on all questions with **every reached callout** as a pending call
(`CoreCallout`); its finished behaviours and productive streams are those of `coreTripleSXP`.

Theorems in `Silmaril.Wasm.Abstract.NodeBridge.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract.NodeBridge

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm.Game Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract.InstSession (Res sAns)

/-! ## Store-preserving hosts -/

/-- **A store-preserving host**: every answer leaves the store as it was at the callout. -/
def StorePreserving {H : Type} (host : HostSemantics H) : Prop :=
  ∀ (hh : H) (s : Store H) (us : List Val) (s' : Store H) (r : Result),
    host hh s us (.returned s' r) → s' = s

variable (I : ScalarInstance)

/-- **The universal store-preserving typed host of `I`**: a callout with typed arguments is
answered by any answer of its import type, the store unchanged. -/
def instHost : HostSemantics Nat := fun hh s us out =>
  ∃ e, I.importOp? hh us = some e ∧
    ∃ v : Answer (I.imports.get e.1), out = .returned s (Answer.toResult v)

/-! ## The view of host events -/

/-- **The view of a host event**: the import call `x` is the event `ev` with its store
forgotten; the answer keeps the store. -/
def CallView (x : Call I.E) (ev : Call (wasmHostSig Nat)) : Prop :=
  I.importOp? ev.1.1 ev.1.2.2 = some x.1 ∧ ev.2.1 = ev.1.2.1 ∧
    ev.2.2 = Answer.toResult (ft := I.imports.get x.1.1) x.2

/-- The Core question of an export question: its function address and its arguments. -/
def qOf (a : I.F.Op) : Nat × List Val := (I.addr a.1, a.2.1)

/-- A session answer of the Core triples as a Core result. -/
def resOf : (List Val ⊕ Nat) ⊕ PUnit.{1} → Result
  | .inl (.inl ws) => .values ws
  | .inl (.inr t) => .throw t
  | .inr _ => .trap

/-- A Core result as a session answer of the Core triples. -/
def cAns : Result → (List Val ⊕ Nat) ⊕ PUnit.{1}
  | .values ws => .inl (.inl ws)
  | .throw t => .inl (.inr t)
  | .trap => .inr PUnit.unit

/-- **The view of an end** of a Core activation of `qOf I a`: a return keeps its store, its
result read as an answer of the export `a` (`none` when its values are ill-typed). -/
noncomputable def viewEnd (a : I.F.Op) :
    End (Store Nat) ((List Val ⊕ Nat) ⊕ PUnit.{1}) →
      Option (End (Store Nat) (Res I.exports ⊕ PUnit.{1}))
  | .ret b s' => (Answer.ofResult? (I.exports.get a.1) (resOf b)).map fun v => .ret (sAns a v) s'
  | .trap => some .trap
  | .div => some .div

/-- **The view of a Core session triple** on the import signature of `I`: the behaviours, pending
calls and productive streams of `qOf I a` whose host events and ends have a view. -/
noncomputable def viewTriple
    (t : ObsTriple (wasmHostSig Nat) (Store Nat) (Nat × List Val) ((List Val ⊕ Nat) ⊕ PUnit.{1})) :
    ObsTriple I.E (Store Nat) I.F.Op (Res I.exports ⊕ PUnit.{1}) :=
  (fun s a => {x | ∃ y ∈ t.1 s (qOf I a),
      List.Forall₂ (CallView I) x.1 y.1 ∧ viewEnd I a y.2 = some x.2},
    fun s a => {x | ∃ y ∈ t.2.1 s (qOf I a),
      List.Forall₂ (CallView I) x.1 y.1 ∧ I.importOp? y.2.1 y.2.2.2 = some x.2},
    fun s a => {ω | ∃ ω' ∈ t.2.2 s (qOf I a), ∀ k, CallView I (ω k) (ω' k)})

/-! ## The open Core triple -/

/-- **A reached callout**: a labelled Core run of the invocation with the host events `x.1`
reaches the host call `x.2 = (hh, s', us)`, at the store `s'`, whatever the host does there. -/
def CoreCallout {H : Type} (P : Numerics.Profile) (host : HostSemantics H) (s : Store H)
    (q : Nat × List Val) (x : List (Call (wasmHostSig H)) × (wasmHostSig H).Op) : Prop :=
  ∃ (c : Config H) (E : SingleThreaded.Ctx) (a' : Nat), EvRun P host (invoke s q.1 q.2) x.1 c ∧
    SingleThreaded.decompose? c.store c.code = some (E, a', x.2.1, x.2.2.2) ∧ c.store = x.2.2.1

/-- **The open store-retaining Core triple with exceptions**: `coreTripleSXP` on all questions,
with every reached callout as a pending call. -/
def coreTripleSO {H : Type} (P : Numerics.Profile) (host : HostSemantics H) :
    ObsTriple (wasmHostSig H) (Store H) (Nat × List Val) ((List Val ⊕ Nat) ⊕ PUnit.{1}) :=
  ((coreTripleSXP P host fun _ _ => True).1, fun s q => {x | CoreCallout P host s q x},
    (coreTripleSXP P host fun _ _ => True).2.2)

end Silmaril.Wasm.Abstract.NodeBridge
