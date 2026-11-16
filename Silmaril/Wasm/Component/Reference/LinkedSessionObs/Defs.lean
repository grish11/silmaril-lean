module

public import Silmaril.Wasm.Component.Reference.LinkedSessionDivInv.Defs
public import Silmaril.Wasm.Component.Reference.SessionObs.Defs
public import Silmaril.Wasm.Component.Reference.SessionStrat.Defs

/-!
# Linked components as session play objects: definitions

**Scope.** `Linked2` only: the import-free exporter A (`l.exp`, a `Simple`) answering every
import of the importer B (`l.imp`, a `SimpleI`) through the canonical ABI. The theorems
(`LinkedSessionObs.Thms`) assume `Linked2.Adequate` (exporter `Good` and `Inst`; importer `Good`,
`Inst`, `Arity` and `FloatFree`; `WireTy`, `NamesOk`, `WireNodup`; `SplitOk`), and the
deterministic profiles `profile o` where store determinism is needed. This module mirrors
`SessionStrat.Defs` and `SessionObs.Defs` (the `Simple` case) for linked components.

## The triple `Linked2.compTripleS P l Ie Ii`

Defined from the specification of linked sessions (`Linked2.SessSpec`, #705, and #730's
`Linked2.RoundDiv`), not from `Comp.den`. For the instances `Ie` of A's and `Ii` of B's core
modules:

* **the state** is the pair `(π, u)` of A's Core store `π` and B's Core store `u`;
* **questions** `Nat × Payload`, those of the untyped export interface `sigU`. A typed call
  (`Linked2.typedQ`: an index in range, a `vals` payload of the export's parameter types) runs one
  round of `Linked2.SessSpec`; every other question traps at once, both stores unchanged, as the
  IR does (`Linked2.den_filter_iff`);
* **answers**: one `SessSpec` round of the call `(j, vs)` from `u` and `π`, with outcome `o` and
  end stores `u'`, `π'`, is `.ret (outAns o) (π', u')`: results `.inl (.vals ws)`, or a trap
  `.inr ()` keeping **both** stores (A's writes before a trap inside B's import call persist, as
  do B's own);
* **divergence** `.div`: the round never answers (`Linked2.RoundDiv`: B diverges host-free, A
  diverges inside an import call, or chatter), the round of #730's `sessDivs`;
* **no imports**: the lower interface is `sigN 0`, with no pending calls and no productive
  streams. Chatter is a divergence of one round, not a productive stream: its import calls are
  hidden.

`Linked2.compSession P l := threadS (Linked2.compTripleS P l Ie Ii) (Ie.store, Ii.store)`, for the
(unique) instances; a component without instances traps on every question.

## Productive executions on the reference machine

`Linked2.RefSessProd P prof l impl h₀ a out`: after instantiating `l.toRef` under `linkHost impl`
from `h₀`, an explicit stream of reference configurations (`SessExec`, `SessionObs.Defs`) running
the export calls `a 0, a 1, …` with the outcomes `out 0, out 1, …` (results, or `none` for a trap
followed by `resumeCfg`). Defined from reference runs only, not from `compSession` nor as a limit
of prefixes.

`Linked2.RefSessEquivFull P prof l l'`: #726's `RefSessEquiv` (terminating outcomes), the same
quiescent divergences (#730's `RefSessQuiet`) and the same productive executions, all on
reference-machine runs and under every host.

**Not covered.**

* Host observations exist only in parents that pass host imports to B (`linkedHRef`-style); within
  `Linked2` every import of B is wired to A, `l.toRef` has no host imports and `linkHost impl` is
  never called. Those observations are not modelled here.
* n-ary and nested components wait on the H2 owner's `DStrategy.pair`/`atSizes`.
* The parser from bytes to these components, and F6, are pending.
* A trapped call resumes from `resumeCfg` (a modelling choice); REF itself locks the store down.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
open Silmaril.Wasm.Component
open Silmaril.Wasm.Numerics (Profile)

local notation "IVal" => Silmaril.Wasm.Component.Val

namespace Linked2

section Triple

open Silmaril.Wasm.Game
open Silmaril.Wasm.Execution.Core (Store)

/-- **The finished behaviours of one linked session call** at A's store `π` and B's store `u`
(the state `(π, u)`): an untyped question traps at once, both stores unchanged; a typed call
`(j, vs)` is one round of `SessSpec` with outcome `o`, answering `outAns o` (results, or a trap
keeping both stores), or a round that never answers (`RoundDiv`). No import calls. -/
def compFin (P : Profile) (l : Linked2) (Ie Ii : ScalarInstance) :
    AFun (sigN 0) (Store Nat × Store Nat) (Nat × Payload) (Payload ⊕ PUnit.{1}) := fun s q =>
  match l.typedQ q with
  | none => {([], .ret (.inr PUnit.unit) s)}
  | some (j, vs) =>
    {x | x.1 = [] ∧
      ((∃ (o : Option (List IVal)) (π' u' : Store Nat),
          SessSpec P l Ie Ii s.2 s.1 [(j, vs)] [o] u' π' ∧ x.2 = .ret (outAns o) (π', u')) ∨
        (RoundDiv P l Ie Ii s.2 s.1 j vs ∧ x.2 = .div))}

/-- **The store-retaining session triple of a linked component** over the instances `Ie` (A) and
`Ii` (B): no pending calls and no productive streams (no imports). -/
def compTripleS (P : Profile) (l : Linked2) (Ie Ii : ScalarInstance) :
    ObsTriple (sigN 0) (Store Nat × Store Nat) (Nat × Payload) (Payload ⊕ PUnit.{1}) :=
  (compFin P l Ie Ii, fun _ _ => ∅, fun _ _ => ∅)

open Classical in
/-- **The canonical session object of a linked component**: the session threading of its triple
from the stores `(Ie.store, Ii.store)` of its instances (unique, `Linked2.compSession_eq`). A
component without instances traps on every question. -/
noncomputable def compSession (P : Profile) (l : Linked2) : DStrategy (sigN 0) sessSig :=
  if h : ∃ Ie Ii : ScalarInstance, l.exp.mod.IsInst Ie ∧ l.imp.mod.IsInst Ii then
    StratSession.threadS (compTripleS P l h.choose h.choose_spec.choose)
      (h.choose.store, h.choose_spec.choose.store)
  else StratSession.threadS trapTripleS PUnit.unit

end Triple

/-! ## Productive executions on the reference machine -/

/-- **A productive execution of a linked component**: after instantiating `l.toRef` under
`linkHost impl` from `h₀`, an explicit coherent stream of reference configurations running the
export calls `a 0, a 1, …` of the importer with the outcomes `out 0, out 1, …` (results, or
`none` for a trap followed by `resumeCfg`). -/
def RefSessProd (P : Profile) (prof : ProfileKind) (l : Linked2) {σ : Type}
    (impl : Silmaril.Wasm.Component.Canon.HostImpl (core3P P) σ) (h₀ : σ)
    (a : ℕ → Fin l.imp.exports.length × List IVal) (out : ℕ → Option (List IVal)) : Prop :=
  ∃ m₀ inst es, ∃ fs : ℕ → Runtime.FuncId,
    InstResult.instance m₀ inst es ∈
      instBehaviours prof (linkHost impl) (initConfig h₀) l.toRef [] ∧
    (∀ k, es.lookup l.imp.exports[(a k).1].name = some (fs k)) ∧
    SessProd prof (linkHost impl) m₀ (fun k => (fs k, (a k).2.map toRefVal))
      (fun k => (out k).map (List.map toRefVal))

/-- A stream of export calls read at a linked component with the same number of exports. -/
def castStream {l l' : Linked2} (h : l.imp.exports.length = l'.imp.exports.length)
    (a : ℕ → Fin l.imp.exports.length × List IVal) : ℕ → Fin l'.imp.exports.length × List IVal :=
  fun k => (Fin.cast h (a k).1, (a k).2)

/-- **The full resumable-session equivalence of linked components**, on reference-machine runs
only and under every host: the same export types and terminating session outcomes
(`RefSessEquiv`), the same quiescent divergences after every typed session, and the same
productive executions of every typed stream of calls. -/
structure RefSessEquivFull (P : Profile) (prof : ProfileKind) (l l' : Linked2) : Prop
    extends RefSessEquiv P prof l l' where
  quiet : ∀ (calls : List (Fin l.imp.exports.length × List IVal))
      (outs : List (Option (List IVal))) (j : Fin l.imp.exports.length) (vs : List IVal),
    SimpleI.TypedCalls l.imp calls → ValTy.checkList l.imp.exports[j].ty.params vs = true →
    ∀ {σ : Type} (impl : Silmaril.Wasm.Component.Canon.HostImpl (core3P P) σ) (h₀ : σ),
      (RefSessQuiet P prof l impl h₀ calls outs j vs ↔
        RefSessQuiet P prof l' impl h₀ (castCalls len calls) outs (Fin.cast len j) vs)
  prod : ∀ (a : ℕ → Fin l.imp.exports.length × List IVal) (out : ℕ → Option (List IVal)),
    (∀ k, ValTy.checkList l.imp.exports[(a k).1].ty.params (a k).2 = true) →
    ∀ {σ : Type} (impl : Silmaril.Wasm.Component.Canon.HostImpl (core3P P) σ) (h₀ : σ),
      (RefSessProd P prof l impl h₀ a out ↔ RefSessProd P prof l' impl h₀ (castStream len a) out)

end Linked2

end Silmaril.Wasm.Component.Reference
