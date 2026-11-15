module

public import Silmaril.Wasm.Cfg.MachineClosed.Defs
public import Silmaril.Wasm.Cfg.Region.Defs
public import Silmaril.Wasm.Execution.Core.Sim.TypedProgress
public import Silmaril.Wasm.Execution.Core.Sim.TypedContext
import Silmaril.Wasm.SingleThreaded.Locality

@[expose] public section

/-!
# The native-slice guard along host-free runs

From a typed starting configuration (`ContextTyped`) on a store of native, arity-checked
functions, every configuration a host-free run reaches has a typed store (`ContextTyped` is
preserved) and the same functions (host-free steps never change them). So `NativeCallOk` holds
at a reached call exactly when its arguments are a typed invocation (`InvokeOk`).
-/

namespace Silmaril.Wasm.Cfg.Proofs.Region

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Region Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Numerics Silmaril.Wasm.Binaryen

variable {H : Type} {P : Profile}

theorem steps_funcs_closed {c c' : Config H} (h : Steps P (fun _ _ _ _ => False) c c') :
    c'.store.funcs = c.store.funcs := by
  induction h with
  | refl => rfl
  | tail _ hs ih => exact (SingleThreaded.Step.framesLocal hs).1.trans ih

/-- **The guard from typing**: from a typed start on native, arity-checked functions, the
native-slice guard holds at every reached call whose arguments are a typed invocation. -/
theorem guardedCalls_of_typed {c₀ : Config H} (hT : Sim.ContextTyped c₀)
    (hN : NativeFuncsOk c₀.store.funcs) (hS : Interp.StoreChk c₀.store.funcs)
    (hI : ∀ (c₂ : Config H) (E : Ctx) (ws us : List Val) (x : FuncIdx) (rest : List Admin)
      (a : Nat), Steps P (fun _ _ _ _ => False) c₀ c₂ →
      c₂.code = E.fill (vals (ws ++ us) ++ .plain (.call x) :: rest) →
      c₂.frame.module.funcs[x.toNat]? = some a → InvokeOk c₂.store a us) :
    GuardedCalls P (fun _ _ _ _ => False) Machine.NativeCallOk c₀ := by
  intro c₂ E ws us x rest a h hc hx
  have hfun := steps_funcs_closed h
  obtain ⟨C, ts, xs, hs, -, -, -⟩ := (hT.steps h).fragment_ctx
  exact ⟨hs, hfun ▸ hN, hfun ▸ hS, hI c₂ E ws us x rest a h hc hx⟩

end Silmaril.Wasm.Cfg.Proofs.Region
