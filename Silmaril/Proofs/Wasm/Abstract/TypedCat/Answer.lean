module

public import Silmaril.Wasm.Abstract.TypedCat.Defs
public import Silmaril.Wasm.Abstract.ExposePTyped.Thms
public import Silmaril.Wasm.Abstract.XRecursionP.Thms
public import Silmaril.Wasm.Abstract.XRecursion.Thms
public import Silmaril.Wasm.Interp.PendSim.Thms

/-!
Proofs for `Silmaril.Wasm.Abstract.TypedCat.Thms`: **arity respect from typed answers.**

* An oracle answering at the callee's result types (`TypedAns`) respects arities.
* The closure `XRecursionP.closedCallXP` keeps the store's functions (least-fixpoint induction,
  restricting runs to the invariant), and, on calls passing the callee's parameter count
  (`fitP`), returns at least the callee's result count, by its soundness against Core 3.0
  (`PendSim.closedCallXP_sound`, which asks for that parameter count). So the closure restricted to
  fitting calls is arity-respecting, with no further premise.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.TypedCat

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Interp Silmaril.Wasm.Abstract.ExposePStruct Silmaril.Wasm.Abstract.ExposePTyped
open Silmaril.Wasm.Abstract.CallXP Silmaril.Wasm.Abstract.XRecursionP
open Silmaril.Wasm.Abstract.TypedCat

variable {H : Type}

/-- **Typed answers respect arities.** -/
theorem arityResp_of_typedAns {Γ : Ctx H} {C : Abstract.CallRel H} (h : TypedAns Γ C) :
    ArityResp Γ C := by
  intro s s₂ a args fl hc hg
  obtain ⟨hg₂, ht⟩ := h s s₂ a args fl hc hg
  refine ⟨hg₂, fun fi ps rs vs hfi hty hvs => ?_⟩
  have := (ht fi ps rs vs hfi hty hvs).length_eq
  simp only [List.length_reverse, List.length_take] at this
  omega

/-- **The closure keeps the store's functions.** -/
theorem closedCallXP_funcs :
    ∀ (s : Store H) a us out, closedCallXP s a us out → out.1.funcs = s.funcs := by
  let Q : Abstract.CallRel H := fun s a us out => closedCallXP s a us out ∧ out.1.funcs = s.funcs
  have hQ : (closedCallXP : Abstract.CallRel H) ≤ Q := by
    refine OrderHom.lfp_le _ ?_
    rintro s a us out ⟨fi, fn, ps, rs, f₂, s₁, o, hfi, hcode, hty, d, hfr⟩
    refine ⟨?_, ?_⟩
    · rw [closedCallXP_fixpoint]
      exact ⟨fi, fn, ps, rs, f₂, s₁, o, hfi, hcode, hty, d.mono fun _ _ _ _ h => h.1,
        hfr.mono fun _ _ _ _ h => h.1⟩
    · have hkeep : ∀ t a us out, Q t a us out → t.funcs = s.funcs → out.1.funcs = s.funcs :=
        fun _ _ _ _ hq hI => hq.2.trans hI
      obtain ⟨h₁, -⟩ := EvalOXP.restrictI (I := fun t : Store H => t.funcs = s.funcs)
        (fun hf hI => (Silmaril.Wasm.Abstract.XRecursion.evalFlat_funcs hf).trans hI)
        (fun _ _ _ hI => hI) hkeep d rfl
      exact (FrameP.restrictI hkeep hfr h₁).1
  exact fun s a us out h => (hQ _ _ _ _ h).2

/-- **The closure on fitting calls respects arities.** -/
theorem arityResp_fitClosed (Γ : Ctx H) : ArityResp Γ (fitP closedCallXP) := by
  rintro s s₂ a args fl ⟨hcl, hfit⟩ hg
  have hsound := Silmaril.Wasm.Interp.PendSim.closedCallXP_sound (P := Numerics.Profile.spec)
    (host := Binaryen.closedHost) Γ.tags s a args (s₂, fl) hcl hg.2
  refine ⟨⟨(closedCallXP_funcs s a args (s₂, fl) hcl).trans hg.1, hsound.1⟩, ?_⟩
  intro fi ps rs vs hfi hty hvs
  have hS : StoreChkE (ehExt Γ.tags) s.funcs := hg.1 ▸ Γ.storeChk
  obtain ⟨⟨ob, hob, hfl, -⟩, -⟩ :=
    hsound.2 {} fi ps rs (.callRefType default) hS hfi hty (hfit fi ps rs hfi hty) trivial
  rcases fl with vs' | ⟨_ | l, vs'⟩ | vs' | _ | _ <;> simp [Flow.retVals] at hvs
  · subst hvs
    rcases hob with rfl | rfl <;> simp [FlowOkE] at hfl
    omega
  · subst hvs
    simp [FlowOkE] at hfl
    omega
  · subst hvs
    exact hfl

end Silmaril.Proofs.Wasm.Abstract.TypedCat
