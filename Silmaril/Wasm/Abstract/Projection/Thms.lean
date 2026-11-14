module

public import Silmaril.Wasm.Abstract.Projection.Defs
public import Silmaril.Wasm.Abstract.Function.Thms

/-!
# Core 3.0 functions as a projection: theorems

* `preserves_behEq`, `reflects_behEq`: `wasmFun` preserves and reflects
  equality of behaviours for the store-forgetting observation.
* `preserves_trapDivEq`, `reflects_trapDivEq`: it preserves and reflects
  `Behaviours.Equiv TrapDiv` for the store-forgetting trap ≈ divergence
  observation.

So the quotient of function references by each relation embeds into the
matching quotient of abstract functions. Both observations forget the final
store, and `AFun.exists_forgetState_not_congr` shows that they are not
congruences for later code in the same store.
-/

public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Games Silmaril.Games.Abstract

variable {H : Type}

theorem preserves_behEq : PreservesFun (X := WasmFunRef H) BehEq obsBeh :=
  fun _ _ h => obsEquiv_behaviour_iff.2 h

theorem reflects_behEq : ReflectsFun (X := WasmFunRef H) BehEq obsBeh :=
  fun _ _ h => obsEquiv_behaviour_iff.1 h

theorem preserves_trapDivEq : PreservesFun (X := WasmFunRef H) TrapDivEq obsBehTrapDiv :=
  fun _ _ h => obsEquiv_trapDiv_iff.2 h

theorem reflects_trapDivEq : ReflectsFun (X := WasmFunRef H) TrapDivEq obsBehTrapDiv :=
  fun _ _ h => obsEquiv_trapDiv_iff.1 h

end Silmaril.Wasm.Abstract
