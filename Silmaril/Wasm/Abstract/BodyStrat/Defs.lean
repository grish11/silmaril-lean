module

public import Silmaril.Wasm.Abstract.BodyTrace.Defs
public import Silmaril.Games.Abstract.StratObs.Defs

/-!
# Bodies into the canonical play object

An interaction-tree body `f : Hom E S T A B` is observed by the triple of its
finished behaviours (`BodyTrace.toAFun`), its pending calls
(`BodyTrace.toPending`) and its infinite productive runs (`BodyTrace.toInf`),
over the lifted import signature `liftSig E`. `toDStratBody` sends a body to
the divergence-observing strategy of that triple
(`Silmaril.Games.Abstract.StratObs.toDStrat`).

`Silmaril.Wasm.Abstract.BodyStrat.Thms` shows that the triple of a body is
saturated, and that two bodies have the same play object exactly when they
are equal up to trap payloads (`BodyTrace.erasedRun`).
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract.BodyStrat

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Abstract.Body
  Silmaril.Wasm.Abstract.BodyTrace

universe u

/-- The observation triple of a body: finished behaviours, pending calls and
infinite productive runs. -/
def toTriple {E : Sig.{u}} {S T A B : Type (u + 1)} (f : Hom E S T A B) :
    ObsTriple (liftSig E) S A B :=
  (toAFun f, toPending f, toInf f)

/-- **The play object of a body.** -/
def toDStratBody {E : Sig.{u}} {S T A B : Type (u + 1)} (f : Hom E S T A B) :
    DStrategy (liftSig E) (funSig S A B) :=
  StratObs.toDStrat (toTriple f)

end Silmaril.Wasm.Abstract.BodyStrat
