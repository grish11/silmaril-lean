module

public import Silmaril.Wasm.Component.Reference.LinkedSessionIR.Defs
public import Silmaril.Wasm.Component.Reference.LinkSound.Defs

/-!
# The reference side of linked sessions: definitions

**Scope.** `Linked2` only: the import-free exporter `exp` (A) answering every import of the
importer `imp` (B) through the canonical ABI (`Link.Defs`). The reference component is
`l.toRef`, and its sessions are the resumable sessions of `SessionAdequacy` (`SessCalls`,
`sessBehaviours`). A call resumes after a trap from `resumeCfg`: the Core store, with every write
of the trapped call (including writes A made before trapping inside B's import call), persists.
This is a modelling choice, not REF; REF locks the store down after a trap.

## The specification of a linked session

`Linked2.SessSpec P l Ie Ii u π calls outs u' π'`: the export calls `calls` of the linked
component, one after another, with outcomes `outs` (`some ws` for results, `none` for a trap).
The importer's instance `Ii` starts at its store `u` and the exporter's instance `Ie` at `π`.
Each call is one round of B (`SessRound`, well formed: `SessRound.Ok`):

* B's core instance answers the core export question of the round after its core import calls,
  as a play of `Ii` from its current store to the store it ends in (`Ii.Path`, from `.idle u` to
  `.idle u₁`). A trap of B itself (a Core trap, or results the lift rejects) is such a play: the
  instance answers the question with a trap and keeps the store it reached, the `TrapAt`
  reading of `Simple`;
* B's component import calls of the round (`ImpRel`) are answered by A's specification as an
  `ExpRunT` segment from A's current store `π` to `π₁`. Returned calls (`RetAt`) and trapped
  calls (`TrapAt`, answered `none`) both thread A's store. An import call answered `none` is
  passed to B's core instance as a trap, so B's round then traps too (`trapImport_path`);
* the outcome of the round is its lifted answer (`SessRound.ans = o.map .vals`).

The next round starts from `u₁` and `π₁`: both stores are threaded across the whole session,
after A's traps and after B's traps alike.

## Observations

* `Linked2.sessObs P prof l impl h₀ calls`: the resumable-session outcomes on the reference
  machine (`sessBehaviours` of `l.toRef`) of calling the importer's exports `calls` (by index, on
  IR values), under `linkHost impl` from host state `h₀`. `l.toRef` imports nothing, so `impl` is
  never called;
* `Linked2.sessMoves l calls outs`: the IR play of a session, each call answered by its results
  or by a trap (`none`), later calls continuing after traps.

## Hypotheses

`Linked2.Adequate l` bundles the hypotheses of `Linked2.sound`, now applied to sessions:

* exporter (`Simple`): `Good` and `Inst`;
* importer (`SimpleI`): `Good`, `Inst`, `Arity` and `FloatFree`;
* wiring: `WireTy`, `NamesOk`, `WireNodup`;
* store split: `SplitOk`.

Not covered: divergence and host observations. Within `Linked2` every import of B is wired to A,
so `l.toRef` has no host imports; a parent that also passes host imports to B (`linkedHRef`) lets
B call the host where `SimpleI` allows it. Those observations, and divergence, are a later step
and are not assumed vacuous. The parser from bytes to these components and F6 are pending.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Wasm.Component
open Silmaril.Wasm.Numerics (Profile)

local notation "IVal" => Silmaril.Wasm.Component.Val

namespace Linked2

/-- **The adequacy hypotheses of a linked component** (those of `Linked2.sound`): the exporter
and the importer are in the instantiation fragment, the importer is float-free and within the
flat arities, the wiring is well typed and injective, the export names avoid the generated type
names, and both core modules are in the split fragment. -/
structure Adequate (l : Linked2) : Prop where
  expGood : l.exp.Good
  expInst : l.exp.Inst
  impGood : l.imp.Good
  impInst : l.imp.Inst
  impArity : l.imp.Arity
  impFloatFree : l.imp.FloatFree
  wireTy : l.WireTy
  namesOk : l.NamesOk
  wireNodup : l.WireNodup
  splitOk : l.SplitOk

section Spec

open Silmaril.Wasm.Game
open Silmaril.Wasm.Execution.Core (Store)

/-- **The specification of a linked session**: from the importer's store `u` and the exporter's
store `π`, the export calls `calls` answer `outs` and end at `u'` and `π'`. Each call is a round
of the importer's core instance from its current store, whose component import calls are an
`ExpRunT` segment of the exporter from its current store (returned and trapped calls threading
it), and whose lifted answer is the outcome. -/
inductive SessSpec (P : Profile) (l : Linked2) (Ie Ii : ScalarInstance) :
    Store Nat → Store Nat → List (Fin l.imp.exports.length × List IVal) →
    List (Option (List IVal)) → Store Nat → Store Nat → Prop
  | nil (u π : Store Nat) : SessSpec P l Ie Ii u π [] [] u π
  | round {u π u₁ π₁ u' π' : Store Nat} {cs : List (Fin l.imp.exports.length × List IVal)}
      {outs : List (Option (List IVal))} {o : Option (List IVal)} (d : SessRound l Ii) :
      d.Ok → Ii.Path P (.idle u) d.instMoves (.idle u₁) → ExpRunT P l Ie π d.dss.flatten π₁ →
      d.ans = o.map .vals → SessSpec P l Ie Ii u₁ π₁ cs outs u' π' →
      SessSpec P l Ie Ii u π ((d.j, d.vs) :: cs) (o :: outs) u' π'

end Spec

/-- **The IR play of a linked session**: each call `(j, vs)` answered by its results, or by a
trap (`none`). -/
def sessMoves (l : Linked2) :
    List (Fin l.imp.exports.length × List IVal) → List (Option (List IVal)) →
    List (Silmaril.Games.Move l.toComp.imports.sig (sigN l.toComp.exports.length))
  | (j, vs) :: cs, o :: os =>
    .inr (.ask (⟨j, by simp [exports_length_toComp]⟩, .vals vs)) ::
      .inr (.ans (m := (⟨j, by simp [exports_length_toComp]⟩, .vals vs)) (o.map .vals)) ::
      sessMoves l cs os
  | _, _ => []

/-- **The session observations of a linked component**: the outcomes of calling the importer's
exports `calls` (by index, on IR values) as a resumable session of `l.toRef` on the reference
machine, under `linkHost impl` from host state `h₀`. -/
noncomputable def sessObs (prof : ProfileKind) {P : Profile} (l : Linked2) {σ : Type}
    (impl : Silmaril.Wasm.Component.Canon.HostImpl (core3P P) σ) (h₀ : σ)
    (calls : List (Fin l.imp.exports.length × List IVal)) :
    Set (List (Option (List Silmaril.Wasm.Component.Value.Val))) :=
  sessBehaviours prof (linkHost impl) h₀ l.toRef
    (calls.map fun q => (l.imp.exports[q.1].name, q.2.map toRefVal))

end Linked2

end Silmaril.Wasm.Component.Reference
