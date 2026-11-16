module

public import Silmaril.Wasm.Component.Reference.SessionAdequacy.Defs
public import Silmaril.Games.Abstract.StratSession.Defs

/-!
# Simple components as session play objects: definitions

`SessionAdequacy` (#676) defines the resumable reference session of a simple component and
proves its finite adequacy against `Comp.den`. This module puts that session into the
canonical session object of `Silmaril.Games.Abstract.StratSession`: a store-retaining triple,
threaded by `StratSession.threadS`.

**The settled session extension of REF.** REF locks the store down after a trap
(`Machine.trapCfg`); the session used here is #676's resumable extension: no poisoning, and
after a trapped call the next top-level call is a fresh invocation from the *actual* Core store
the trap left (`resumeCfg`). This is the decided reading, matching the Wasm session reading of
`StratSession` (a trap aborts the call, not the instance).

## The triple `compTripleS P c I`

Defined from the specification of sessions (`SessionAdequacy.Defs`: `RetAt`, `TrapAt`, the
steps of `SessSpec`), which #676 proves equal to the reference sessions
(`Simple.sess_specToRef`, `Simple.sess_refToSpec`); not from `Comp.den`. For the instance `I`
of the component's module:

* **questions** `Nat × Payload`, the questions of the untyped export interface `sigU`, so
  that components with different export counts have sessions of one type. A typed export call
  (`Simple.sessQ`: an index in range, a `vals` payload of the export's parameter types) runs;
  every other question (an index out of range, a `flat` payload, ill-typed values) traps at once
  without a store change, as the IR does;
* **the state** is the Core store (`Store Nat`) of the instance;
* **answers**: `.ret (.inl (.vals ws)) s'` for a returned call (`RetAt`) with its results and
  final store; `.ret (.inr ()) s'` for a trapped call (`TrapAt`), with the store the trap left;
  the session continues from `s'` in both cases;
* **divergence** `.div`: a typed call whose lowered Core activation runs forever host-free
  (`DivAt`). This is the divergence clause of the canonical-ABI specification (`specAt`,
  `exportSpec`), on Core runs. It is not defined from reference-machine runs: the library
  relates the reference machine's `CallDiverges` to Core divergence in one direction only
  (reference divergence gives Core divergence, `CallRun.diverges_spec` and its sequential
  forms), so a reference-run definition could not be compared with the IR side;
* **no imports**: the lower interface is `sigN 0`, with no pending calls and no productive
  streams.

`compSession P c := threadS (compTripleS P c I) I.store` for the (unique) instance `I`: the
canonical play object of the component. Its interface `sig1 (Nat × Payload) Payload` answers a
question by a payload `.inl` or a trap `.inr ()`; `sessMove` reads its moves at `sigU`.

## Equivalences

`RefSessEquivD P prof c c'`: #676's `RefSessEquiv` (terminating session outcomes, on the
reference machine) and the same diverging session calls (`sessDivs`: after a specification
session with given outcomes, the next typed call diverges). Divergence is compared through its
definition on Core runs, never inferred from finite plays.

Scope and non-claims (theorems in `SessionStrat.Thms`):

* `Simple` components (for the injection, `Simple.Adequate` ones, #669/#676 scope) at the
  deterministic profiles `profile o` where store determinism is needed;
* not contextual full abstraction: the observer is a host calling exports in sequence;
* the parser from bytes to `Comp` is not involved; its correctness is a separate obligation;
* the native store-retaining closing correspondence (closing a session object against its
  host) belongs to the `StratSession` owner, not to this module.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
open Silmaril.Wasm.Component
open Silmaril.Wasm.Numerics (Profile)

local notation "IVal" => Silmaril.Wasm.Component.Val

/-! ## Questions and moves -/

/-- **The typed export call** of a session question, if it is one: an index in range and a
`vals` payload of the export's parameter types. -/
def Simple.sessQ (c : Simple) : Nat × Payload → Option (Fin c.exports.length × List IVal)
  | (j, .vals vs) =>
    if h : j < c.exports.length then
      if ValTy.checkList c.exports[j].ty.params vs then some (⟨j, h⟩, vs) else none
    else none
  | (_, .flat _) => none

/-- The interface of a component session: questions of `sigU`, answers a payload or a trap. -/
abbrev sessSig : Sig.{0} := sig1 (Nat × Payload) Payload

/-- A session answer at `sigU`: a payload, or `none` for a trap. -/
def optAns : Payload ⊕ PUnit.{1} → Option Payload
  | .inl p => some p
  | .inr _ => none

/-- The session answer of a call outcome: results `some ws`, or a trap `none`. -/
def outAns : Option (List IVal) → Payload ⊕ PUnit.{1}
  | some ws => .inl (.vals ws)
  | none => .inr PUnit.unit

/-- A move of the session interface read at `sigU`. -/
def sessMove : Move (sigN 0) sessSig → Move (sigN 0) sigU
  | .inl e => .inl e
  | .inr (.ask q) => .inr (.ask q)
  | .inr (.ans q x) => .inr (.ans (m := q) (optAns x))

/-- Every question asked in the play has an index below `n`. -/
def AskedIn (n : Nat) (p : List (Move (sigN 0) sessSig)) : Prop :=
  ∀ q : Nat × Payload, Sum.inr (Ev.ask q) ∈ p → q.1 < n

/-! ## The store-retaining triple -/

section Triple

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded

/-- **A diverging call** of export `x` on `vs` from the store `s`: the lowered arguments run
host-free forever (the divergence clause of the canonical-ABI specification). -/
structure DivAt (P : Profile) (I : Silmaril.Wasm.Game.ScalarInstance) (x : SimpleExport)
    (vs : List IVal) (s : Store Nat) : Prop where
  typed : ValTy.checkList x.ty.params vs = true
  run : ∃ g : ℕ → Store Nat × Thread,
    g 0 = (s, Thread.invokeFlat (I.addrs.getD x.core 0) (lowerArgs x.ty.params vs)) ∧
    ∀ k, Silmaril.Wasm.Game.InternalP P (g k) (g (k + 1))

/-- **The finished behaviours of one session call** at the store `s`: an untyped question traps
at once, the store unchanged; a typed call returns its results (`RetAt`), traps keeping the
store it reached (`TrapAt`), or diverges (`DivAt`). No import calls. -/
def compFin (P : Profile) (c : Simple) (I : Silmaril.Wasm.Game.ScalarInstance) :
    AFun (sigN 0) (Store Nat) (Nat × Payload) (Payload ⊕ PUnit.{1}) := fun s q =>
  match c.sessQ q with
  | none => {([], .ret (.inr PUnit.unit) s)}
  | some (j, vs) =>
    {x | x.1 = [] ∧
      ((∃ ws s', RetAt P c I c.exports[j] vs s ws s' ∧ x.2 = .ret (.inl (.vals ws)) s') ∨
        (∃ s', TrapAt P c I c.exports[j] vs s s' ∧ x.2 = .ret (.inr PUnit.unit) s') ∨
        (DivAt P I c.exports[j] vs s ∧ x.2 = .div))}

/-- **The store-retaining session triple of a simple component** over the instance `I`: no
pending calls and no productive streams (no imports). -/
def compTripleS (P : Profile) (c : Simple) (I : Silmaril.Wasm.Game.ScalarInstance) :
    ObsTriple (sigN 0) (Store Nat) (Nat × Payload) (Payload ⊕ PUnit.{1}) :=
  (compFin P c I, fun _ _ => ∅, fun _ _ => ∅)

/-- The session trapping every question (for modules without an instance). -/
def trapTripleS : ObsTriple (sigN 0) PUnit.{1} (Nat × Payload) (Payload ⊕ PUnit.{1}) :=
  (fun s _ => {([], .ret (.inr PUnit.unit) s)}, fun _ _ => ∅, fun _ _ => ∅)

open Classical in
/-- **The canonical session object of a simple component**: the session threading of its
triple from the store of its instance (unique, `compSession_eq`). A module without an instance
traps on every question. -/
noncomputable def compSession (P : Profile) (c : Simple) : DStrategy (sigN 0) sessSig :=
  if h : ∃ I, c.mod.IsInst I then StratSession.threadS (compTripleS P c h.choose) h.choose.store
  else StratSession.threadS trapTripleS PUnit.unit

/-! ## Diverging session calls -/

/-- **The diverging session calls of the specification**: the outcomes `outs` of a session of
the calls `calls` from the instance's store after which the typed call of export `j` on `vs`
diverges. -/
def sessDivs (P : Profile) (c : Simple) (calls : List (Fin c.exports.length × List IVal))
    (j : Fin c.exports.length) (vs : List IVal) : Set (List (Option (List IVal))) :=
  {outs | ∃ (I : Silmaril.Wasm.Game.ScalarInstance) (s : Store Nat), c.mod.IsInst I ∧
    SessSpec P c I I.store (specCalls c calls) outs s ∧ DivAt P I c.exports[j] vs s}

end Triple

/-- **The resumable-session equivalence with divergence**: `RefSessEquiv` (the terminating
session outcomes on the reference machine) and, for every typed session and typed next call,
the same diverging session calls (`sessDivs`, on Core runs). -/
structure RefSessEquivD (P : Profile) (prof : ProfileKind) (c c' : Simple) : Prop
    extends RefSessEquiv P prof c c' where
  div : ∀ (calls : List (Fin c.exports.length × List IVal)) (j : Fin c.exports.length)
      (vs : List IVal), TypedCalls c calls → ValTy.checkList c.exports[j].ty.params vs = true →
    sessDivs P c calls j vs = sessDivs P c' (castCalls len calls) (Fin.cast len j) vs

end Silmaril.Wasm.Component.Reference
