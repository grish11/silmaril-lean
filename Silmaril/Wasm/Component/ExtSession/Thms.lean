module

public import Silmaril.Wasm.Component.ExtSession.Defs
public import Silmaril.Games.Abstract.SessionExt.Thms
import Silmaril.Proofs.Wasm.Component.ExtSession.Plays

/-!
# The component environment extension on sessions: theorems

**On the session interface** (`extS_splitR_threadS`): `SessionExt.extS (splitR e)` is
`DStrategy.ext e` with `sigU` replaced by its session view `sigS` and `splitH e` by the routing
handler `routeH (splitR e)`. For an environment session `threadS u s'` and a node session
`threadS t s` running over it (no plain traps, deterministic returns),

  `extS (splitR e) (threadS u s') (threadS t s) =`
    `threadS (linkS u (routeS (splitR e) idS t)) (s', ((), s))`,

all three components (finite plays, divergence, infinite plays): copycat is `idS`, the node runs
beside it, questions below `e` go to copycat and the others to the node, shifted by `e`, and the
environment's session serves both (`SessionExt.extS_threadS`).

**On `sigU`, finite plays** (`toStrategy_ext_eq`, `toStrategy_ext_threadS`): relabel the session
answers to Wasm answers with `toU` (above, `DStrategy.comp_ansH` makes this
`DStrategy.mapAns (fun _ => toOpt)`) and the node's import answers with `ofU` (below). Then the
finite plays of `DStrategy.ext e` are the relabelled finite plays of `extS (splitR e)`, for any
environment and node; for sessions, those of the linked session:

  `(ext e ((threadS u s').comp toU) (ofU.comp ((threadS t s).comp toU))).toStrategy =`
    `((threadS (linkS u (routeS (splitR e) idS t)) (s', ((), s))).comp toU).toStrategy`.

The proof uses the handler laws of finite plays: `toU` below the pairing is duplicated, cancels
`ofU` (`toU_comp_ofU`), moves above the pairing, and commutes with the routing
(`sumMap_comp_splitH`).

**Not yet covered:** the divergence and infinite-play components of the `sigU` statement. They
need a law for a relabelling handler below a divergence-observing pairing (the
`DStrategy` analogue of `Strategy.ofHandler_comp_pair`), or equivalently that relabelling the
middle interface of a composite is invisible. The session-interface statement above has all three
components.

Proofs are in `Silmaril.Proofs.Wasm.Component.ExtSession`.
-/

public section

namespace Silmaril.Wasm.Component

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
  Silmaril.Games.Abstract.StratSession Silmaril.Games.Abstract.SessionLink
  Silmaril.Games.Abstract.SessionCat Silmaril.Games.Abstract.SessionExt

/-- **The relabelling handlers cancel.** -/
theorem toU_comp_ofU : toU.comp ofU = Handler.id sigS :=
  Silmaril.Proofs.Wasm.Component.ExtSession.toU_comp_ofU

/-- **Relabelling commutes with the routing.** -/
theorem sumMap_comp_splitH (e : Nat) :
    (Handler.sumMap toU toU).comp (splitH e) = (routeH (splitR e)).comp toU :=
  Silmaril.Proofs.Wasm.Component.ExtSession.sumMap_comp_splitH e

variable {X : Sig.{0}} {S S' : Type} {u : ObsTriple X S' (Nat × Payload) (Payload ⊕ PUnit)}
  {t : ObsTriple sigS S (Nat × Payload) (Payload ⊕ PUnit)}

/-- **The extension of a session environment by a session node, on the session interface.** -/
theorem extS_splitR_threadS (e : Nat) (hnu : NoPlainTrap u) (hdu : RetDet u)
    (hnt : NoPlainTrap t) (hdt : RetDet t) (s' : S') (s : S) :
    extS (splitR e) (threadS u s') (threadS t s) =
      threadS (linkS u (routeS (splitR e) idS t)) (s', (PUnit.unit, s)) :=
  extS_threadS (splitR e) hnu hdu hnt hdt s' s

/-- **The finite plays of `DStrategy.ext e`** with relabelled answers are the relabelled finite
plays of `extS (splitR e)`. -/
theorem toStrategy_ext_eq (e : Nat) (D₀ : DStrategy X sigS) (N₀ : DStrategy sigS sigS) :
    (DStrategy.ext e (D₀.comp (DStrategy.ofHandler toU))
        ((DStrategy.ofHandler ofU).comp (N₀.comp (DStrategy.ofHandler toU)))).toStrategy =
      ((extS (splitR e) D₀ N₀).comp (DStrategy.ofHandler toU)).toStrategy :=
  Silmaril.Proofs.Wasm.Component.ExtSession.toStrategy_ext_eq e D₀ N₀

/-- **The finite plays of `DStrategy.ext e` on sessions** are the relabelled finite plays of the
linked session. -/
theorem toStrategy_ext_threadS (e : Nat) (hnu : NoPlainTrap u) (hdu : RetDet u)
    (hnt : NoPlainTrap t) (hdt : RetDet t) (s' : S') (s : S) :
    (DStrategy.ext e ((threadS u s').comp (DStrategy.ofHandler toU))
        ((DStrategy.ofHandler ofU).comp
          ((threadS t s).comp (DStrategy.ofHandler toU)))).toStrategy =
      ((threadS (linkS u (routeS (splitR e) idS t)) (s', (PUnit.unit, s))).comp
        (DStrategy.ofHandler toU)).toStrategy := by
  rw [toStrategy_ext_eq, extS_splitR_threadS e hnu hdu hnt hdt]

end Silmaril.Wasm.Component
