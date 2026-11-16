module

public import Silmaril.Games.Abstract.Projection.Defs
public import Silmaril.Wasm.Abstract.Function.Defs
public import Silmaril.Wasm.Abstract.Outcome.Defs

/-!
# Core 3.0 functions as a projection

A `WasmFunRef H` is a function address under a numerics profile and host
semantics. Its projection is `wasmFun`. Two concrete relations on references:

* `BehEq`: the same behaviours at every store and argument;
* `TrapDivEq`: `Behaviours.Equiv TrapDiv` behaviours at every store and argument.

`Silmaril.Wasm.Abstract.Projection.Thms` proves that the projection preserves
*and* reflects each of them, for the matching store-forgetting observation.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

/-- A function address under a profile and a host semantics. -/
structure WasmFunRef (H : Type) where
  /-- The numerics profile. -/
  P : Profile
  /-- The host semantics. -/
  host : HostSemantics H
  /-- The function address. -/
  a : Nat

instance (H : Type) : FunProj (WasmFunRef H) Sig.empty (Store H) (List Val) (List Val ⊕ Nat) :=
  ⟨fun r => wasmFun r.P r.host r.a⟩

/-- Same behaviours at every store and argument. -/
def BehEq {H : Type} (x y : WasmFunRef H) : Prop :=
  ∀ s vs, behaviours x.P x.host s x.a vs = behaviours y.P y.host s y.a vs

/-- Trap ≈ divergence equivalent behaviours at every store and argument. -/
def TrapDivEq {H : Type} (x y : WasmFunRef H) : Prop :=
  ∀ s vs, Behaviours.Equiv Behaviour.TrapDiv (behaviours x.P x.host s x.a vs)
    (behaviours y.P y.host s y.a vs)

/-- The store-forgetting observation. -/
def obsBeh {H : Type} : CallBeh Sig.empty (Store H) (List Val ⊕ Nat) → Behaviour Val :=
  fun x => endToBehaviour x.2

/-- The store-forgetting trap ≈ divergence observation. -/
def obsBehTrapDiv {H : Type} : CallBeh Sig.empty (Store H) (List Val ⊕ Nat) → CTag (List Val ⊕ ULift Nat) :=
  fun x => (toTag (endToBehaviour x.2)).collapse

end Silmaril.Wasm.Abstract
