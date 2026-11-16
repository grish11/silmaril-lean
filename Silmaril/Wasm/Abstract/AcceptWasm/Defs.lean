module

public import Silmaril.Wasm.Abstract.Accept.Defs
public import Silmaril.Wasm.Abstract.Function.Defs
public import Silmaril.Wasm.Abstract.Instance.Defs
public import Silmaril.Wasm.Behaviour.Semantics.V3.Defs
public import Silmaril.Wasm.Game.Untyped.Defs

/-! # Acceptance of concrete Wasm functions and instances, before abstraction

The concrete sides of the diagrams of `Silmaril.Wasm.Abstract.AcceptWasm.Thms`:

* `behRun P host D a vs`: the Core 3.0 behaviours (`behaviours`) of calling the function at
  address `a` on `vs` from an admitted store of `D`. With it, the export readings (some call
  returns an accepting result, no call returns a rejecting one) are the generic verdicts of
  `Silmaril.Semantics.Accept` over **concrete** runs.
* `uMachine U P`: the store-carrying (untyped) instance `U` as an abstract machine, the
  untyped analogue of `Silmaril.Wasm.Abstract.machine` for scalar instances. Its moves carry the
  caller's whole store, so observations can read memory (for example `accept(ptr, len)`).

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract.Accept

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type}

/-- **Concrete runner of a function**: the behaviours of the call from an admitted store. -/
def behRun (P : Profile) (host : HostSemantics H) (D : Set (Store H)) (a : Nat) (vs : List Val) :
    Set (Behaviour Val) :=
  {b | ∃ s ∈ D, b ∈ behaviours P host s a vs}

/-- The untyped instance `U` as an abstract machine. -/
noncomputable def uMachine (U : Silmaril.Wasm.Game.UInstance) (P : Profile) :
    Machine (sigGame U.E U.F) :=
  Machine.ofLTS (U.lts P)

end Silmaril.Wasm.Abstract.Accept
