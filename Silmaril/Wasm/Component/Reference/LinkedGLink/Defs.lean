module

public import Silmaril.Wasm.Component.Reference.LinkedGSession.Defs
public import Silmaril.Games.Abstract.SessionLinkAssoc.Defs
public import Silmaril.Games.Abstract.SessionTrap.Defs
public import Silmaril.Games.Abstract.ModuleInf.Defs
public import Silmaril.Wasm.Component.OutOfRangeSession.Defs

/-!
# The importer of a linked component as a session client: definitions

**Scope.** A simple importer `b : SimpleI` at its core instance `Ii`, at a profile `P`, with its
component imports wired by `wire` to the exports of some exporter (`LinkedG`). This topic reads
the importer alone as a store-retaining session triple (`StratSession`) whose lower interface is
the session interface of the exporter, `sigS = sig1 (Nat × Payload) Payload`, so that it can be
linked with the exporter's triple `ExpSpec.sessTripleS` by the generic `SessionLink.linkS`.

## The importer's triple `SimpleI.impTripleS P b wire Ii`

`ObsTriple sigS (Store Nat) (Nat × Payload) (Payload ⊕ PUnit)`, over the importer's Core store.

* **Lower calls.** A component import call of `b` (import `k` on the payload `p`, answered
  `R : Option Payload`) is the wired call `wireCall`: the question `(wire[k], p)` to the
  exporter, answered `ExpSpec.sumAns R` (a payload `.inl`, or the trap `.inr ()`). An import
  `k` with no wire is sent to export `0` (`List.getD`); under `LinkedG.WireTy` every import is
  wired.
* **The start of a round** (`SimpleI.Lowered`, the shape of `LinkedG.SessRound.Ok` and
  `LinkedG.DivRound.Ok`): export `j` of `b` on the component values `vs`, lowered to the flat
  values `xs`, the core question `f` of the importer's instance, and core import calls `cs`
  related to component import calls `dss` by `ImpRel` (an import whose arguments do not lift
  answers the core call with a trap without a component call).
* **Finished behaviours** (`impFin`): an ill-typed question (`SimpleI.TypedQ` fails) traps at
  once, the store unchanged, with no lower call. Otherwise a round of the importer's core
  instance from the idle store `u`: it ends idle at `u₁` with the core answer `w`, answering the
  lifted answer `sumAns ((answerPayload w).bind (Adapter.up (.lift ty)))` and keeping `u₁` (a
  trap keeps its store); or it runs host-free forever (`Linked2.DivB`) after its calls: `.div`.
  The log is the wired calls of `dss`, in order.
* **Pending calls** (`impPend`): after the calls of a round prefix, the instance calls out on
  core import `e` with arguments that lift to `ws` at the import's type: the pending wired call
  `(wire[e], .vals ws)`.
* **Productive streams** (`impInf`): after a round prefix, infinitely many core import calls
  `c k`, each related to exactly one component call `y k`; the stream is the wired calls of the
  prefix followed by those of `y`.

There are no plain traps (`End.trap`): every trap keeps the importer's store.

`IsTrapS` (from `OutOfRangeSession`) is the trap predicate of `sigS`: the answer `.inr ()`.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm.Component
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Game (ScalarInstance)
open Silmaril.Wasm.Execution.Core (Store)

local notation "IVal" => Silmaril.Wasm.Component.Val

namespace SimpleI

section Calls

variable (b : SimpleI)

/-- **A typed question of the importer**: an export in range, on values of its parameter
types. -/
def TypedQ (q : Nat × Payload) : Prop :=
  ∃ (j : Fin b.exports.length) (vs : List IVal), q = (j.val, .vals vs) ∧
    ValTy.checkList b.exports[j].ty.params vs = true

/-- A component import call of `b`, with its answer. -/
abbrev ICall : Type := Σ _ : (sigN b.imports.length).Op, Option Payload

/-- **The wired call** of a component import call: import `k` on `p` answered `R` is the
question `(wire[k], p)` to the exporter, answered `sumAns R`. -/
def wireCall (wire : List Nat) (z : b.ICall) : Call sigS :=
  ⟨(wire.getD z.1.1.val 0, z.1.2), ExpSpec.sumAns z.2⟩

/-- The wired calls of a list of component import calls. -/
def wireLog (wire : List Nat) (ds : List b.ICall) : List (Call sigS) :=
  ds.map (b.wireCall wire)

/-- **The start of a round** of the importer's core instance `Ii` (`LinkedG.SessRound.Ok`):
export `j` on `vs`, lowered to the core question `f`, after the core import calls `cs` related
to the component import calls `dss`. -/
def Lowered (Ii : ScalarInstance) (j : Fin b.exports.length) (vs : List IVal) (f : Ii.F.Op)
    (cs : List (Σ e : Ii.E.Op, Ii.E.Ar e)) (dss : List (List b.ICall)) : Prop :=
  ∃ xs : List Flat, checkLower b.exports[j].ty.params vs = some xs ∧
    f.1.val = b.exports[j].core ∧ f.2.1 = xs.map Silmaril.Wasm.SingleThreaded.ofFlat ∧
    List.Forall₂ (ImpRel b Ii) cs dss

/-- The lifted answer of export `j` to the core answer `w` (`LinkedG.SessRound.ans`). -/
def liftAns {Ii : ScalarInstance} (j : Fin b.exports.length) {f : Ii.F.Op} (w : Ii.F.Ar f) :
    Option Payload :=
  (answerPayload w).bind (Adapter.up (.lift b.exports[j].ty))

end Calls

variable (P : Profile) (b : SimpleI) (wire : List Nat) (Ii : ScalarInstance)

/-- **The finished behaviours of one round of the importer** at the store `u` (see the module
documentation): an ill-typed question traps at once; otherwise a returning round (its lifted
answer, a trap keeping the final store) or host-free divergence, after the wired calls. -/
def impFin : AFun sigS (Store Nat) (Nat × Payload) (Payload ⊕ PUnit.{1}) := fun u q =>
  {x | (¬ b.TypedQ q ∧ x = ([], .ret (.inr PUnit.unit) u)) ∨
    ∃ (j : Fin b.exports.length) (vs : List IVal) (f : Ii.F.Op)
      (cs : List (Σ e : Ii.E.Op, Ii.E.Ar e)) (dss : List (List b.ICall)),
      q = (j.val, .vals vs) ∧ b.Lowered Ii j vs f cs dss ∧ x.1 = b.wireLog wire dss.flatten ∧
      ((∃ (w : Ii.F.Ar f) (u₁ : Store Nat),
          Ii.Path P (.idle u) (.inr (.ask f) :: callMoves cs ++ [.inr (.ans f w)]) (.idle u₁) ∧
          x.2 = .ret (ExpSpec.sumAns (b.liftAns j w)) u₁) ∨
        (∃ (s : Store Nat) (t : Silmaril.Wasm.SingleThreaded.Thread),
          Ii.Path P (.idle u) (.inr (.ask f) :: callMoves cs) (.running f s t) ∧
          Linked2.DivB P s t ∧ x.2 = .div))}

/-- **The pending calls of one round of the importer**: after a round prefix, a call out on core
import `e` whose arguments lift to `ws`, pending as the wired call `(wire[e], .vals ws)`. -/
def impPend : Pending sigS (Store Nat) (Nat × Payload) := fun u q =>
  {x | ∃ (j : Fin b.exports.length) (vs : List IVal) (f : Ii.F.Op)
      (cs : List (Σ e : Ii.E.Op, Ii.E.Ar e)) (dss : List (List b.ICall)) (s : Store Nat)
      (t : Silmaril.Wasm.SingleThreaded.Thread) (e : Ii.E.Op) (s' : Store Nat)
      (t' : Silmaril.Wasm.SingleThreaded.Thread) (nm : String) (ft : FuncTy) (ws : List IVal),
      q = (j.val, .vals vs) ∧ b.Lowered Ii j vs f cs dss ∧
      Ii.Path P (.idle u) (.inr (.ask f) :: callMoves cs) (.running f s t) ∧
      Ii.Path P (.running f s t) [.inl (.ask e)] (.waiting f s' t' e) ∧
      b.imports[e.1.val]? = some (nm, ft) ∧
      liftArgs ft.params (e.2.1.filterMap Silmaril.Wasm.SingleThreaded.toFlat?) = some ws ∧
      x = (b.wireLog wire dss.flatten, (wire.getD e.1.val 0, .vals ws))}

/-- **The productive streams of one round of the importer**: after a round prefix, infinitely
many core import calls `c k`, each related to one component import call `y k`. -/
def impInf : PInf sigS (Store Nat) (Nat × Payload) := fun u q =>
  {ω | ∃ (j : Fin b.exports.length) (vs : List IVal) (f : Ii.F.Op)
      (cs : List (Σ e : Ii.E.Op, Ii.E.Ar e)) (dss : List (List b.ICall)) (s : Store Nat)
      (t : Silmaril.Wasm.SingleThreaded.Thread) (r : ℕ → Ii.HState)
      (c : ℕ → Σ e : Ii.E.Op, Ii.E.Ar e) (y : ℕ → b.ICall),
      q = (j.val, .vals vs) ∧ b.Lowered Ii j vs f cs dss ∧
      Ii.Path P (.idle u) (.inr (.ask f) :: callMoves cs) (.running f s t) ∧
      r 0 = .running f s t ∧
      (∀ k, Ii.Path P (r k) (callMoves [c k]) (r (k + 1)) ∧ ImpRel b Ii (c k) [y k]) ∧
      ω = Shape.streamAppend (b.wireLog wire dss.flatten) (fun k => b.wireCall wire (y k))}

/-- **The importer's own session triple**: its lower calls are its wired import calls, at the
exporter's session interface `sigS`; its store is the importer's Core store. -/
def impTripleS : ObsTriple sigS (Store Nat) (Nat × Payload) (Payload ⊕ PUnit.{1}) :=
  (b.impFin P wire Ii, b.impPend P wire Ii, b.impInf P wire Ii)

end SimpleI

end Silmaril.Wasm.Component.Reference
