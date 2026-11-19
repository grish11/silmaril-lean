module

public import Silmaril.Wasm.Interp.CtxInv.Defs
public import Silmaril.Wasm.Abstract.HostCall.Thms

@[expose] public section

/-!
# The typed instance of the backward simulations' invariant (definitions)

`backTyped`: `Sim.ContextTyped` against hosts with typed answers (`HostTyped`) is a
`Interp.BackInv`. Preservation along runs is `ContextTyped.steps_typed`; a host also answering
one call by a trap in its store keeps typed answers (the trap keeps the store); divergence passes
through host-free steps by `diverges_through_steps`. The backward simulations
(`Abstract.HostClosingXP`, `Abstract.HostClosingInfXPBack`) are proved for every `BackInv`; their
typed statements are the case `backTyped`.
-/

namespace Silmaril.Wasm.Abstract

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Interp

variable {H : Type}

/-- **The principal types of a store's references are closed-valid** (what the interpreter's
exactness reads of `StoreOk`). -/
def StoreTy (s : Store H) : Prop :=
  ∀ (r : Ref) (rt₀ : Validation.CRefType), Ref.type? s r = some rt₀ → Validation.TyOk {} rt₀

/-- **The typed instance**: `Sim.ContextTyped` against hosts with typed answers. -/
def backTyped : BackInv H where
  toCtxInv := ctxTyped
  HostOk := HostTyped
  steps_host hT h hs := ContextTyped.steps_typed hT h hs
  hostOk_trap m hT := by
    intro s fi h vs ps rs hs hfi hcode he hvs out hout
    rcases hout with hout | ⟨-, rfl, -, rfl⟩
    · exact hT s fi h vs ps rs hs hfi hcode he hvs out hout
    · exact ⟨hs, Extend.refl hs, trivial⟩
  through h hK hd := diverges_through_steps (.single hd) h hK

/-- A typed invocation is in the typed invariant. -/
theorem ctxTyped_invoke {s : Store H} {a : Nat} {vs : List Val} (hs : StoreOk s)
    (hok : InvokeOk s a vs) : Sim.ContextTyped (invoke s a vs) :=
  let ⟨_, _, _, _, _, h⟩ := invoke_ok hs hok
  Sim.ContextTyped.of_configOk h

end Silmaril.Wasm.Abstract
