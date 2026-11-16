module

public import Silmaril.Wasm.Component.ExtSession.Thms
import Silmaril.Proofs.Wasm.Component.ExtSessionFull.Ext

/-!
# The component environment extension on sessions over `sigU`: all components

`Silmaril.Wasm.Component.ExtSession` proves the extension statement on the session interface
`sigS` in all three components, and on the Wasm interface `sigU` for finite plays only. This
module completes the `sigU` statement for divergence and infinite plays.

**Relabelled extension** (`ext_eq`): relabel the session answers to Wasm answers with `toU`
(above) and the node's import answers with `ofU` (below). Then for any environment `D₀` and node
`N₀`,

  `ext e (D₀.comp toU) (ofU.comp (N₀.comp toU)) = (extS (splitR e) D₀ N₀).comp toU`

as divergence-observing strategies: finite plays, divergence and infinite plays. The proof uses
the handler laws of `Silmaril.Games.AnsPull` for relabelling handlers: `ofU` below the pairing
distributes over it, `toU` and `ofU` cancel both ways (so relabelling the hidden middle interface
changes nothing), `toU` above both sides of the pairing is `toU` side by side above it, and the
side-by-side `toU` below `splitH e` is the routing handler below `toU` (`sumMap_comp_splitH`).
`toStrategy_ext_eq` is the finite-play component of `ext_eq`.

**Sessions** (`ext_threadS`): for an environment session `threadS u s'` and a node session
`threadS t s` running over it (no plain traps, deterministic returns), the extension over `sigU`
is the relabelled linked session

  `ext e ((threadS u s').comp toU) (ofU.comp ((threadS t s).comp toU)) =`
    `(threadS (linkS u (routeS (splitR e) idS t)) (s', ((), s))).comp toU`,

combining `ext_eq` with `extS_splitR_threadS`. `toStrategy_ext_threadS` is its finite-play
component.

Proofs are in `Silmaril.Proofs.Wasm.Component.ExtSessionFull`.
-/

public section

namespace Silmaril.Wasm.Component

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
  Silmaril.Games.Abstract.StratSession Silmaril.Games.Abstract.SessionLink
  Silmaril.Games.Abstract.SessionCat Silmaril.Games.Abstract.SessionExt

/-- **`DStrategy.ext e` with relabelled answers is the relabelled `extS (splitR e)`**, in all
three components. -/
theorem ext_eq {X : Sig.{0}} (e : Nat) (D₀ : Games.DStrategy X sigS)
    (N₀ : Games.DStrategy sigS sigS) :
    DStrategy.ext e (D₀.comp (Games.DStrategy.ofHandler toU))
        ((Games.DStrategy.ofHandler ofU).comp (N₀.comp (Games.DStrategy.ofHandler toU))) =
      (extS (splitR e) D₀ N₀).comp (Games.DStrategy.ofHandler toU) :=
  Silmaril.Proofs.Wasm.Component.ExtSessionFull.ext_eq e D₀ N₀

/-- **The extension of a session environment by a session node over `sigU`** is the relabelled
linked session, in all three components. -/
theorem ext_threadS {X : Sig.{0}} {S S' : Type}
    {u : ObsTriple X S' (Nat × Payload) (Payload ⊕ PUnit)}
    {t : ObsTriple sigS S (Nat × Payload) (Payload ⊕ PUnit)} (e : Nat) (hnu : NoPlainTrap u)
    (hdu : RetDet u) (hnt : NoPlainTrap t) (hdt : RetDet t) (s' : S') (s : S) :
    DStrategy.ext e ((threadS u s').comp (Games.DStrategy.ofHandler toU))
        ((Games.DStrategy.ofHandler ofU).comp
          ((threadS t s).comp (Games.DStrategy.ofHandler toU))) =
      (threadS (linkS u (routeS (splitR e) idS t)) (s', (PUnit.unit, s))).comp
        (Games.DStrategy.ofHandler toU) := by
  rw [ext_eq, extS_splitR_threadS e hnu hdu hnt hdt]

end Silmaril.Wasm.Component
