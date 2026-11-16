module

public import Silmaril.Wasm.Cfg.MachineClosed.Defs
public import Silmaril.Wasm.Cfg.Region.Defs
public import Silmaril.Wasm.Execution.Core.Sim.TypedProgress
public import Silmaril.Wasm.Execution.Core.Sim.TypedContext
public import Silmaril.Wasm.Execution.Core.Soundness.PresCall
public import Silmaril.Proofs.Wasm.Cfg.Region
import Silmaril.Wasm.SingleThreaded.Locality

@[expose] public section

/-!
# The native-slice guard from a typed native start

From a typed starting configuration (`ContextTyped`) on a store of native, arity-checked
functions, every call a host-free run reaches is on the native slice (`NativeCallOk`):
* the store stays typed (`ContextTyped` is preserved by host-free steps);
* the functions are unchanged (host-free steps never change them);
* the call's arguments are a typed invocation (`InvokeOk`): after the call resolves, the typed
  `call_ref` on its `ps.length` arguments types them at the callee's parameters
  (`callRef_front`, the inversion of Core preservation for `call_ref`).
-/

namespace Silmaril.Wasm.Cfg.Proofs.Region

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Region Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Numerics Silmaril.Wasm.Binaryen Silmaril.Wasm.Validation

variable {H : Type} {P : Profile}

theorem steps_funcs_closed {c c' : Config H} (h : Steps P (fun _ _ _ _ => False) c c') :
    c'.store.funcs = c.store.funcs := by
  induction h with
  | refl => rfl
  | tail _ hs ih => exact (SingleThreaded.Step.framesLocal hs).1.trans ih

/-- **A typed resolved call types its arguments**: a typed `call_ref` form `cr` of `fi` (`call_ref
y`, or the `call_ref` of `fi`'s own type a direct call resolves to) on its `ps.length` top values
`us` is a typed invocation. -/
theorem invokeOk_of_typed {s : Store H} {f : Frame} {ws us : List Val} {a : Nat} {cr : Admin}
    {fi : FuncInst H} {ps rs : Ty (.list .val)} {rest : List Admin}
    (h : Sim.ContextTyped ⟨s, f, vals (ws ++ us) ++ .ref (.func a) :: cr :: rest⟩)
    (hcr : cr.IsCallRef) (hd : ∀ d, cr = .callRefType d → d = fi.type)
    (hfi : s.funcs[a]? = some fi) (he : Expand fi.type (.func ps rs)) (hn : us.length = ps.length) :
    InvokeOk s a us := by
  have h1 : Sim.ContextTyped ⟨s, f, vals (ws ++ us) ++ [.ref (.func a), cr]⟩ :=
    Sim.ContextTyped.suffix (rest := rest) (by simpa using h)
  obtain ⟨C, ts, xs, hs, hC, hc, hcode⟩ := h1.fragment_ctx
  obtain ⟨_, xs₁, _, hp, ht, _⟩ := AdminsOk.split hcode hC (vals ws)
    (vals us ++ [.ref (.func a), cr]) (by simp) (by simp)
  have hC' := hC.initLocals xs₁
  have hc' := hc.initLocals hp.vals_inits
  obtain ⟨-, -, -, -, -, -, -, -, hargs, -⟩ := PC.callRef_front hs ⟨hs.structsClosed, hs.arraysClosed⟩
    hc' hC' (c := cr) hcr
    (fun d hd' => by obtain rfl := hd d hd'; exact PC.StoreOk.func_tyOk hs hfi) hfi he hn ht
  exact ⟨fi, ps, rs, hfi, he, hargs⟩

/-- Typing descends through a context. -/
theorem contextTyped_fill : ∀ (E : Ctx) {s : Store H} {f : Frame} {X : List Admin},
    Sim.ContextTyped ⟨s, f, E.fill X⟩ → Sim.ContextTyped ⟨s, f, X⟩
  | .hole, _, _, _, h => h
  | .label ws n cont E rest, _, _, _, h =>
    contextTyped_fill E (Sim.ContextTyped.label (vs := ws) (rest := rest) (by simpa [Ctx.fill] using h))
  | .handler ws n cs E rest, _, _, _, h =>
    contextTyped_fill E (Sim.ContextTyped.handler (vs := ws) (rest := rest)
      (by simpa [Ctx.fill] using h))

/-- **The guard from typing**: from a typed start on native, arity-checked functions, every call
a host-free run reaches is on the native slice. -/
theorem guardedCalls_of_typed {c₀ : Config H} (hT : Sim.ContextTyped c₀)
    (hN : NativeFuncsOk c₀.store.funcs) (hS : Interp.StoreChk c₀.store.funcs) :
    GuardedCalls P (fun _ _ _ _ => False) Machine.NativeCallOk c₀ := by
  intro c₂ E ws us a cr rest fi ps rs h hc hcr hd hfi he hn
  have hfun := steps_funcs_closed h
  have hT₂ := hT.steps h
  obtain ⟨C, ts, xs, hs, -, -, -⟩ := hT₂.fragment_ctx
  refine ⟨hs, hfun ▸ hN, hfun ▸ hS, ?_⟩
  obtain ⟨s₂, f₂, code₂⟩ := c₂
  simp only at hc hfi ⊢
  subst hc
  exact invokeOk_of_typed (contextTyped_fill E hT₂) hcr hd hfi he hn

end Silmaril.Wasm.Cfg.Proofs.Region
