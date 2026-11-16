module

public import Silmaril.Wasm.Abstract.BodyStrat.Defs
public import Silmaril.Wasm.Abstract.BodyTrace.Thms
public import Silmaril.Games.Abstract.StratObs.Thms
public import Silmaril.Wasm.Abstract.FunctorP.Thms
import Silmaril.Proofs.Wasm.Abstract.BodyStrat.Basic

/-!
# Bodies into the canonical play object: theorems

* `toTriple_saturated`: the triple of a body is saturated. Every call prefix
  forced by a finished path, a pending call or an infinite productive run is
  already a pending call: the tree is at a `vis` node at that position.
* `toDStratBody_eq_iff_toTriple`: hence (`StratObs.toDStrat_injective`) two
  bodies have the same play object exactly when they have the same triple.
* `toDStratBody_eq_iff`: **the play object is faithful up to trap payloads**,
  `toDStratBody f = toDStratBody g ↔ erasedRun f = erasedRun g`. The infinite
  runs add nothing for bodies: they are determined by the pending calls
  (`BodyTrace.toInf_eq_of_faithful`), and `BodyTrace.faithful_iff` relates the
  other two components to `erasedRun`.
* `toDStratBody_denL_iff`: at the code level, with `FunctorP.opEquivP_iff`,
  two code lists have the same play object exactly when they are
  operationally equivalent (`FunctorP.OpEquivP`).

**Which game equivalence is `OpEquivP`.** The quotient is *equality of play objects*:
`DStrategy` equality, i.e. the same finite plays, the same divergent (quiescent) plays and the same
infinite plays. The moves are the existing game moves with their polarity:

* an Opponent question `.inr (.ask (s, a))`;
* a Proponent import call `.inl (.ask m)`, then an Opponent answer `.inl (.ans m n)`;
* a Proponent answer `.inr (.ans (s, a) r)`. Here `r = .inl (b, s')` returns `b` in the final state
  `s'`; at sources with exceptions, `b : List Val ⊕ Nat` and `.inr t` is the uncaught exception
  `t`. `r = .inr ()` is a trap, with the payload erased.

A play ending at a running position may be **divergent**: `DStrategy.div` holds exactly the
divergent behaviours (`StratObs.mem_div`). **Infinite** plays are `DStrategy.inf` (`StratObs.mem_inf`).
Body triples are admissible (`toTriple_admissible`), so no pending interaction is erased. For
checked code, equal play objects is exactly `OpEquivP` (`toDStratBody_denL_iff`), and exactly
equal runs with trap payloads erased (`toDStratBody_eq_iff`).

No coarser game equivalence is claimed: not trace or testing equivalence forgetting divergence or
infinite plays, and not contextual equivalence or full abstraction. The bodies are deterministic
given answers, but this file proves no determinism of the play object.

Proofs are in `Silmaril.Proofs.Wasm.Abstract.BodyStrat.Basic`.
-/

public section

namespace Silmaril.Wasm.Abstract.BodyStrat

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Abstract.Body
  Silmaril.Wasm.Abstract.BodyTrace

universe u

variable {E : Sig.{u}} {S T A B : Type (u + 1)}

/-- **The triple of a body is saturated.** -/
theorem toTriple_saturated (f : Hom E S T A B) : StratObs.Saturated (toTriple f) :=
  Silmaril.Proofs.Wasm.Abstract.BodyStrat.toTriple_saturated f

/-- **The triple of a body is admissible.** -/
theorem toTriple_admissible (f : Hom E S T A B) : StratObs.Admissible (toTriple f) :=
  toTriple_saturated f

/-- Bodies have the same play object exactly when they have the same triple. -/
theorem toDStratBody_eq_iff_toTriple {f g : Hom E S T A B} :
    toDStratBody f = toDStratBody g ↔ toTriple f = toTriple g :=
  ⟨StratObs.toDStrat_injective (toTriple_saturated f) (toTriple_saturated g),
    congrArg StratObs.toDStrat⟩

/-- **The play object of a body is faithful up to trap payloads.** -/
theorem toDStratBody_eq_iff {f g : Hom E S T A B} :
    toDStratBody f = toDStratBody g ↔ erasedRun f = erasedRun g := by
  rw [toDStratBody_eq_iff_toTriple, ← faithful_iff]
  refine ⟨fun h => ⟨congrArg (·.1) h, congrArg (·.2.1) h⟩, fun h => ?_⟩
  have hi := toInf_eq_of_toPending h.2
  simp only [toTriple, h.1, h.2, hi]

end Silmaril.Wasm.Abstract.BodyStrat

namespace Silmaril.Wasm.Abstract.BodyStrat

open Silmaril.Wasm.Binaryen Silmaril.Wasm.Abstract.ExposePStruct Silmaril.Wasm.Abstract.FunctorP

/-- **Code-level faithfulness**: two code lists have the same play object
exactly when they are operationally equivalent. -/
theorem toDStratBody_denL_iff {H : Type} (es es' : List BExpr) :
    toDStratBody (denL (H := H) es) = toDStratBody (denL es') ↔ OpEquivP H es es' :=
  toDStratBody_eq_iff.trans (opEquivP_iff es es')

end Silmaril.Wasm.Abstract.BodyStrat
