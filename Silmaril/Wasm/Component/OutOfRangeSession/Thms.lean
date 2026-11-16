module

public import Silmaril.Wasm.Component.OutOfRangeSession.Defs
public import Silmaril.Wasm.Component.OutOfRange.Thms
public import Silmaril.Games.Abstract.SessionTrap.Thms
import Silmaril.Proofs.Wasm.Component.OutOfRangeSession.Relabel

/-!
# Session nodes propagate traps

`Silmaril.Wasm.Component.OutOfRange` shows that the wiring creates divergence (trap chatter)
exactly for strategies that do not propagate traps. This module shows that session nodes whose
rounds abort on a trap from below do propagate them, on `sigU`.

* **Sessions** (`Silmaril.Games.Abstract.SessionTrap`): if every round of the store-retaining
  triple `t` aborts at a call answered `.inr ()` (`TrapAbortsRound IsTrapS t`: such a call is the
  last of its behaviour, which ends with a trap; no pending call or productive stream continues
  past it), then `threadS t s` answers `.inr ()` right after receiving `.inr ()`
  (`threadS_trapAbortsBelow`).
* **Relabelled to `sigU`** (`ofSession_trapAborting`): through `toU` above and `ofU` below, the
  trap answer `.inr ()` is `none`, so `ofSession σ` answers `none` right after receiving `none`
  (`TrapAborting`), hence propagates traps (`TrapPropagating`).
* **Consequences**: such a node adds no wiring divergence below `widenH`
  (`div_atSizes_ofSession`) and none at the `maskH` layer of a component
  (`div_ext_maskH_ofSession`).

**The native Wasm session triple.** For `sessionTripleXP`, whose lower interface is the host
calls `wasmHostSig H`, the corresponding hypothesis is
`TrapAbortsRound IsHostTrap sessionTripleXP` (`IsHostTrap m n := n.2 = Result.trap`), the game
form of Core Wasm's rule that a trapping callee traps its caller (`EvalLXPS.callTrap`,
`indTrap`, `refTrap`, and `tailAnsS` for tail calls). It is proved in
`Silmaril.Wasm.Abstract.HostTrapS` (`sessionTripleXP_trapAbortsRound`,
`threadS_sessionTripleXP_trapAbortsBelow`). A Wasm core node of a component would moreover need
a session triple over `sigS` rather than over `wasmHostSig H`; the component semantics
`DCoreSem` is abstract, so that bridge is a hypothesis of the component-level results.
-/

public section

namespace Silmaril.Wasm.Component

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
  Silmaril.Games.Abstract.StratSession Silmaril.Games.Abstract.SessionTrap

/-- **A session strategy answering a trap after a trap from below does so on `sigU`.** -/
theorem ofSession_trapAborting {σ : DStrategy sigS sigS} (hσ : TrapAbortsBelow IsTrapS σ) :
    TrapAborting (ofSession σ) :=
  Silmaril.Proofs.Wasm.Component.OutOfRangeSession.relabel_trapAborting hσ

variable {S : Type} {t : ObsTriple sigS S (Nat × Payload) (Payload ⊕ PUnit.{1})}

/-- **A session node whose rounds abort on a trap propagates traps on `sigU`.** -/
theorem threadS_trapAborting (ht : TrapAbortsRound IsTrapS t) (s : S) :
    TrapAborting (ofSession (threadS t s)) :=
  ofSession_trapAborting (threadS_trapAbortsBelow ht s)

theorem threadS_trapPropagating (ht : TrapAbortsRound IsTrapS t) (s : S) :
    TrapPropagating (ofSession (threadS t s)) :=
  (threadS_trapAborting ht s).trapPropagating

/-- **No wiring divergence for a session node** below `widenH n`. -/
theorem div_atSizes_ofSession {n k : Nat} (ht : TrapAbortsRound IsTrapS t) (s : S) :
    (DStrategy.atSizes n k (ofSession (threadS t s))).div = {p | ∃ a b u v, Zip u v a ∧
      Zip a b p ∧ u ∈ Strategy.ofHandler (widenH n) ∧ b ∈ Strategy.ofHandler (narrowH k) ∧
        v ∈ (ofSession (threadS t s)).div} :=
  no_wiring_divergence (threadS_trapPropagating ht s)

/-- **No divergence at the `maskH` layer above a session node.** -/
theorem div_ext_maskH_ofSession (e : Nat) (ht : TrapAbortsRound IsTrapS t) (s : S) :
    (DStrategy.ext e (DStrategy.ofHandler (maskH e)) (ofSession (threadS t s))).div =
      {p | ∃ a b, Zip a b p ∧ a ∈ Strategy.ofHandler (maskH e) ∧ ∃ c g, Zip c g b ∧
        (c ∈ (Strategy.id sigU).pair (ofSession (threadS t s)).toStrategy ∧
          (Split.halves false c).2 ∈ (ofSession (threadS t s)).div) ∧
            g ∈ Strategy.ofHandler (splitH e)} :=
  DStrategy.div_ext_maskH e (threadS_trapPropagating ht s)

end Silmaril.Wasm.Component
