module

public import Silmaril.Wasm.Component.Reference.LinkedGInf.Defs
public import Silmaril.Wasm.Component.Reference.SessionStrat.Defs

/-!
# Exporters, linked components and chains as session play objects: definitions

**Scope.** An exporter `ExpSpec` at a profile `P`, in particular a linked component
`g.toExp Ii` (`LinkedG`, at the importer's core instance `Ii`) and so one more importer on a
chain (`⟨n.spec Ib Is, b, w⟩`). For the theorems, the deterministic profiles `profile o`. This
mirrors `Linked2.compTripleS` and `Linked2.compSession` (#746, `LinkedSessionObs.Defs`), stated
once over the exporter interface.

## The triple `ExpSpec.sessTripleS P e`

Defined from the specification of the exporter (`ExpSpec.Step`, `ExpSpec.DivStep`), not from
`Comp.den`:

* **the state** is the exporter's specification state `e.St` (for `g.toExp Ii`: the importer's
  Core store with the exporter's state, `(u, π)`, the state of `LinkedG.toExp`);
* **questions** `Nat × Payload`, those of `sigU`. A typed question (`ExpSpec.TypedQ`: an export
  in range, a `vals` payload of its parameter types) runs one `Step`; every other question traps
  at once, the state unchanged (the canonical side's choice, as in `Linked2.compFin`);
* **answers**: a step `Step P s ⟨q, R⟩ s'` is `.ret (sumAns R) s'`: a payload `.inl p`, or a trap
  `.inr ()` keeping the state `s'` (a trap does not end the session);
* **divergence** `.div`: a `DivStep` (for a linked component: `LinkedG.RoundDiv`);
* **no imports**: the lower interface is `sigN 0`, with no pending calls and no productive
  streams.

`ExpSpec.session P e := threadS (e.sessTripleS P) e.init`.

## Linked components

`LinkedG.compTripleS P g Ii := (g.toExp Ii).sessTripleS P`, and `LinkedG.compSession P g` the
session of `g.toExp Ii` for the (unique) instance `Ii` of the importer's core module; a link
whose importer has no instance traps on every question.

## Comparing two exporters

`ExpSpec.SameQ e e'`: the same typed questions. `ExpSpec.RunEq P e e'`: the same typed sessions
from the initial states. `ExpSpec.DivEq P e e'`: the same divergences of typed questions after
typed sessions.

**Not covered here.** The relation of the session object to the IR denotation on ill-typed
questions (the exporter interface says nothing about them). They trap at once in the IR of a
linked component too (`LinkedG.den_filter_iff`, `LinkedGFilter`), so the finite IR plays are the
in-range plays of `LinkedG.compSession` (`LinkedG.pubPlays_compSession`, `LinkedGFilter`).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
open Silmaril.Wasm.Component
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Game (ScalarInstance)

namespace ExpSpec

/-- The session answer of an IR answer: a payload, or `none` for a trap (the inverse of
`optAns`). -/
def sumAns : Option Payload → Payload ⊕ PUnit.{1}
  | some p => .inl p
  | none => .inr PUnit.unit

/-- **The finished behaviours of one session call of an exporter** at the state `s`: an untyped
question traps at once, the state unchanged; a typed question is one `Step` (its answer, or a
trap keeping the next state) or a `DivStep`. No import calls. -/
def sessFin (P : Profile) (e : ExpSpec) :
    AFun (sigN 0) e.St (Nat × Payload) (Payload ⊕ PUnit.{1}) := fun s q =>
  {x | x.1 = [] ∧ ((¬ e.TypedQ q ∧ x.2 = .ret (.inr PUnit.unit) s) ∨
    (e.TypedQ q ∧ ((∃ (R : Option Payload) (s' : e.St), e.Step P s ⟨q, R⟩ s' ∧
        x.2 = .ret (sumAns R) s') ∨ (e.DivStep P s q ∧ x.2 = .div))))}

/-- **The store-retaining session triple of an exporter**: no pending calls and no productive
streams (no imports). -/
def sessTripleS (P : Profile) (e : ExpSpec) :
    ObsTriple (sigN 0) e.St (Nat × Payload) (Payload ⊕ PUnit.{1}) :=
  (e.sessFin P, fun _ _ => ∅, fun _ _ => ∅)

/-- **The session object of an exporter**: the session threading of its triple from its
initial state. -/
def session (P : Profile) (e : ExpSpec) : DStrategy (sigN 0) sessSig :=
  StratSession.threadS (e.sessTripleS P) e.init

/-- The same typed questions. -/
def SameQ (e e' : ExpSpec) : Prop := ∀ q, e.TypedQ q ↔ e'.TypedQ q

/-- **The same typed sessions** from the initial states. -/
def RunEq (P : Profile) (e e' : ExpSpec) : Prop :=
  ∀ L : List URound, (∀ r ∈ L, e.Typed r) →
    ((∃ s, e.Run P e.init L s) ↔ ∃ s', e'.Run P e'.init L s')

/-- **The same divergences** of typed questions after typed sessions from the initial states. -/
def DivEq (P : Profile) (e e' : ExpSpec) : Prop :=
  ∀ (L : List URound) (q : sigU.Op), (∀ r ∈ L, e.Typed r) → e.TypedQ q →
    ((∃ s, e.Run P e.init L s ∧ e.DivStep P s q) ↔ ∃ s', e'.Run P e'.init L s' ∧ e'.DivStep P s' q)

end ExpSpec

namespace LinkedG

/-- **The store-retaining session triple of a linked component** at the importer's core
instance `Ii`: the triple of `g.toExp Ii`, over the importer's store and the exporter's
state. -/
def compTripleS (P : Profile) (g : LinkedG) (Ii : ScalarInstance) :
    ObsTriple (sigN 0) (Silmaril.Wasm.Execution.Core.Store Nat × g.exp.St) (Nat × Payload)
      (Payload ⊕ PUnit.{1}) :=
  (g.toExp Ii).sessTripleS P

open Classical in
/-- **The canonical session object of a linked component**: the session threading of its triple
from the importer's instance store and the exporter's initial state, for the (unique) instance of
the importer's core module (`LinkedG.compSession_eq`). A link whose importer has no instance
traps on every question. -/
noncomputable def compSession (P : Profile) (g : LinkedG) : DStrategy (sigN 0) sessSig :=
  if h : ∃ Ii : ScalarInstance, g.imp.mod.IsInst Ii then
    StratSession.threadS (compTripleS P g h.choose) (h.choose.store, g.exp.init)
  else StratSession.threadS trapTripleS PUnit.unit

end LinkedG

end Silmaril.Wasm.Component.Reference
