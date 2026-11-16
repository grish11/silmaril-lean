module

public import Silmaril.Wasm.Component.Reference.SessionStrat.Defs
public import Silmaril.Wasm.Component.Reference.SessionAdequacy.Thms
public import Silmaril.Games.Abstract.StratSession.Thms
import Silmaril.Proofs.Wasm.Component.Reference.SessionStrat.Main

/-!
# Simple components as session play objects: theorems

**The triple** (`compTripleS P c I`, from the specification of sessions, not from `Comp.den`)
has no plain traps (`noPlainTrap_compTripleS`): every trap keeps its store and the session
continues. At the deterministic profiles `profile o` it is store-deterministic
(`storeDet_compTripleS`, from the uniqueness of host-free normal forms). The session object does
not depend on the choice of the instance (`compSession_eq`).

**Finite agreement** (`Simple.pubPlays_compSession`, every profile `P`): the plays of the IR
denotation `c.toComp.den (modSem P)` at `sigU` are exactly the plays of `compSession P c` whose
questions are in range, read at `sigU` (`sessMove`). The session object answers questions out of
range (a trap, the store unchanged); the IR interface `sigN n` cannot ask them. Proved through
#676's correspondence between IR plays and specification sessions (`sess_complete`,
`sess_sound` and their round-level forms).

**The injection** (`Simple.compSession_inj`, at `profile o`, every component choice profile):
for adequate simple components,

`RefSessEquivD (profile o) prof c c' ↔ SameTypes c c' ∧ compSession (profile o) c = compSession (profile o) c'`,

an equality of `DStrategy`s, including divergence and infinite plays. It goes through
`StratSession.threadS_eq_iff` (store determinism and no plain traps): equal sessions are
bisimilar stores, and the bisimulation relating the stores reached by the same rounds is built
from the transfer of completed rounds (`RefSessEquiv`) and of divergent rounds (the `div`
clause). `RefSessEquiv` alone compares terminating outcomes only, which is why the
`div` clause is added; `RefSessEquivD.toRefSessEquiv` is the projection, and on the finite
plays the session objects agree with `Simple.sessAdequacy` (`compSession_eq_pubPlays`).

**Infinite plays** (`mem_inf_compSession`, `Simple.sessInf_iff`, at `profile o`): the infinite
plays of the session object are the plays of coherent infinite sequences of terminating session
rounds (no imports, so no productive streams); for typed calls, the infinite play of calls
`a k` answered by `out k` is an infinite play iff every finite prefix is a resumable reference
session behaviour (`sessObs`).

Settled decision and non-claims:

* the session extension of REF is the decided one: no poisoning, and after a trap a fresh
  invocation from the actual Core store the trap left (#676's `resumeCfg`); REF itself locks
  the store down;
* `Simple` scope: adequate simple components (#669/#676), deterministic profiles for the
  injection and the infinite plays;
* divergence is the canonical-ABI specification's divergence on Core runs (`DivAt`); it equals
  reference-machine divergence (`Reference.SessionDiv`), so `RefSessEquivD`'s `div` clause is
  equivalently stated on reference-machine runs (`RefSessEquivD.iff_refDivs`);
* not contextual full abstraction: the observer is a host calling exports in sequence;
* the passage from bytes to `Comp` is separate;
* the native store-retaining closing correspondence belongs to the `StratSession` owner.

Proofs: `Silmaril.Proofs.Wasm.Component.Reference.SessionStrat.{Rounds,Main}`.
-/

public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Games.Abstract.StratThread (StoreDet InfRounds)
open Silmaril.Games.Abstract.StratSession (NoPlainTrap threadS sroundsPlay)
open Silmaril.Wasm.Component
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

local notation "IVal" => Silmaril.Wasm.Component.Val

variable {P : Profile} {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance}

/-! ## The triple -/

/-- **Every trap keeps its store**: the triple has no plain traps. -/
theorem noPlainTrap_compTripleS : NoPlainTrap (compTripleS P c I) :=
  Silmaril.Proofs.Wasm.Component.Reference.SessionStrat.noPlainTrap_compTripleS

/-- **Store determinism** at the deterministic profiles. -/
theorem storeDet_compTripleS (o : GrowOracle) : StoreDet (compTripleS (profile o) c I) :=
  Silmaril.Proofs.Wasm.Component.Reference.SessionStrat.storeDet_compTripleS o

/-- The session object is the threading of the triple of the instance of the module. -/
theorem compSession_eq (hI : c.mod.IsInst I) : compSession P c = threadS (compTripleS P c I) I.store :=
  Silmaril.Proofs.Wasm.Component.Reference.SessionStrat.compSession_eq hI

/-! ## Finite agreement -/

/-- **The IR plays are the in-range plays of the session object** (every profile). -/
theorem Simple.pubPlays_compSession (P : Profile) (c : Simple) (hc : c.Good)
    (hi : ∃ I, c.mod.IsInst I) :
    pubPlays (c.toComp.den (modSem P)) =
      {q | ∃ p ∈ (compSession P c).toStrategy, AskedIn c.exports.length p ∧ p.map sessMove = q} :=
  Silmaril.Proofs.Wasm.Component.Reference.SessionStrat.pubPlays_compSession P c hc hi

/-- Components with the same export count and equal session objects have the same IR plays. -/
theorem compSession_eq_pubPlays {c c' : Simple} (hc : c.Adequate) (hc' : c'.Adequate)
    (len : c.exports.length = c'.exports.length) (h : compSession P c = compSession P c') :
    pubPlays (c.toComp.den (modSem P)) = pubPlays (c'.toComp.den (modSem P)) := by
  rw [Simple.pubPlays_compSession P c hc.good hc.inst.inst,
    Simple.pubPlays_compSession P c' hc'.good hc'.inst.inst, h, len]

/-! ## The injection -/

/-- **The injection of adequate simple components into session objects** (deterministic
profiles, every component choice profile): the resumable-session equivalence with divergence is
equality of export types and of session objects, as `DStrategy`s (finite plays, divergence and
infinite plays). -/
theorem Simple.compSession_inj (o : GrowOracle) (prof : ProfileKind) {c c' : Simple}
    (hc : c.Adequate) (hc' : c'.Adequate) :
    RefSessEquivD (profile o) prof c c' ↔
      SameTypes c c' ∧ compSession (profile o) c = compSession (profile o) c' :=
  Silmaril.Proofs.Wasm.Component.Reference.SessionStrat.compSession_inj o prof hc hc'

/-! ## Infinite plays -/

/-- **The infinite plays of the session object**: the plays of coherent infinite sequences of
terminating session rounds. -/
theorem mem_inf_compSession (o : GrowOracle) (hI : c.mod.IsInst I)
    {J : Set (List (Move (sigN 0) sessSig))} :
    J ∈ (compSession (profile o) c).inf ↔
      ∃ a r s, InfRounds (compTripleS (profile o) c I) I.store a r s ∧ J = sroundsPlay a r :=
  Silmaril.Proofs.Wasm.Component.Reference.SessionStrat.mem_inf_compSession o hI

/-- **Infinite typed sessions are reference sessions with infinitely many terminating calls**:
the infinite play of the typed calls `a` answered by `out` is an infinite play of the session
object iff every finite prefix is a resumable reference session behaviour. -/
theorem Simple.sessInf_iff (o : GrowOracle) (prof : ProfileKind) (hc : c.Adequate)
    (a : ℕ → Fin c.exports.length × List IVal) (out : ℕ → Option (List IVal))
    (ht : ∀ k, ValTy.checkList c.exports[(a k).1].ty.params (a k).2 = true) :
    sroundsPlay (fun k => (((a k).1 : Nat), Payload.vals (a k).2))
        (fun k => ([], outAns (out k))) ∈ (compSession (profile o) c).inf ↔
      ∀ k, refOuts (streamTake out k) ∈ sessObs (profile o) prof c (streamTake a k) :=
  Silmaril.Proofs.Wasm.Component.Reference.SessionStrat.sessInf_iff o prof hc a out ht

end Silmaril.Wasm.Component.Reference
