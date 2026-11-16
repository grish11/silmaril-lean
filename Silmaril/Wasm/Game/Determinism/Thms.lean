module

public import Silmaril.Wasm.Game.Strategy.Defs
import Silmaril.Proofs.Wasm.Game.Strategy.Basic

/-!
# Determinism of an instance's hidden-state transitions: theorems

A small header for the determinism facts of `Silmaril.Proofs.Wasm.Game.Strategy.Basic`, for users
outside the `Wasm.Game` topic. It is kept separate from the widely imported
`Wasm.Game.Strategy.Thms`. At the deterministic profiles `profile o` only:

* `ScalarInstance.Trans.functional`: the next hidden state is a function of the state and the
  move;
* `ScalarInstance.Trans.player_unique`: Proponent's move from a hidden state is unique;
* `ScalarInstance.Path.functional`: the hidden state a play reaches is a function of the state
  it starts from and the play.

All three come from the uniqueness of normal forms of host-free runs (`reach_normal_unique`); they
fail at nondeterministic profiles (NaN payloads, relaxed operators, `grow` failure).

Proofs: `Silmaril.Proofs.Wasm.Game.Strategy.Basic`.
-/

public section

namespace Silmaril.Wasm.Game.ScalarInstance

open Silmaril.Games
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

variable {I : ScalarInstance}

/-- **The next hidden state is a function of the state and the move** (deterministic
profiles). -/
theorem Trans.functional {o : GrowOracle} {q q₁ q₂ : I.HState} {m : Move I.E I.F}
    (h₁ : I.Trans (profile o) q m q₁) (h₂ : I.Trans (profile o) q m q₂) : q₁ = q₂ :=
  Silmaril.Proofs.Wasm.Game.ScalarInstance.Trans.functional h₁ h₂

/-- **Proponent's move from a hidden state is unique** (deterministic profiles). -/
theorem Trans.player_unique {o : GrowOracle} {q q₁ q₂ : I.HState} {m m' : Move I.E I.F}
    (h₁ : I.Trans (profile o) q m q₁) (h₂ : I.Trans (profile o) q m' q₂) (hm : m.IsP) :
    m = m' :=
  Silmaril.Proofs.Wasm.Game.ScalarInstance.Trans.player_unique h₁ h₂ hm

/-- **The hidden state a play reaches is a function of its start and the play**
(deterministic profiles). -/
theorem Path.functional {o : GrowOracle} {q q₁ q₂ : I.HState} {p : List (Move I.E I.F)}
    (h₁ : I.Path (profile o) q p q₁) (h₂ : I.Path (profile o) q p q₂) : q₁ = q₂ :=
  Silmaril.Proofs.Wasm.Game.ScalarInstance.Path.functional h₁ h₂

end Silmaril.Wasm.Game.ScalarInstance
