module

public import Silmaril.Wasm.Game.Machine.Defs
import Silmaril.Proofs.Wasm.Game.Adequacy.Termination

/-!
# Termination excludes divergence: theorems

A small header for `Silmaril.Proofs.Wasm.Game.Adequacy.Termination`, for users outside the
`Wasm.Game` topic. It is kept separate from the widely imported `Wasm.Game.Adequacy.Thms` so that
importing this one fact does not pull in the adequacy development.

* `reach_normal_not_infinite`: at the deterministic profiles `profile o`, a host-free run reaching
  a normal form has no infinite host-free continuation from its start.

Proofs: `Silmaril.Proofs.Wasm.Game.Adequacy.Termination`.
-/

public section

namespace Silmaril.Wasm.Game

/-- **Termination excludes divergence** at the deterministic profiles: a host-free run reaching a
normal form has no infinite host-free continuation from its start. -/
theorem reach_normal_not_infinite {o : SingleThreaded.GrowOracle}
    {x y : Execution.Core.Store Nat × SingleThreaded.Thread}
    (run : Reach (SingleThreaded.profile o) x y)
    (normal : ∀ z, ¬ InternalP (SingleThreaded.profile o) y z) :
    ¬ Silmaril.InfiniteTrace (InternalP (SingleThreaded.profile o)) x :=
  Silmaril.Proofs.Wasm.Game.reach_normal_not_infinite run normal

end Silmaril.Wasm.Game
