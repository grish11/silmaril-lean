module

public import Silmaril.Proofs.Wasm.Cfg.CallTransport
public import Silmaril.Wasm.Cfg.MachineClosed.Defs

@[expose] public section

/-!
# The checked closed oracle is complete for Core calls on the native slice

`closedCall_core_iff` (`Abstract.Oracle`) says the closed oracle is exactly the Core runs of
`invoke s a us` (empty caller frame, canonical annotation). With no host and only Wasm functions,
a Core call run in any caller frame and with any `call_ref` annotation is such an `invoke` run
(`call_transport`), so `closedCallOk` answers it.
-/

namespace Silmaril.Wasm.Cfg.Proofs.Region

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Region Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Numerics Silmaril.Wasm.Validation Silmaril.Wasm.Binaryen

variable {H : Type}

theorem flowRes_of_exit {n : Nat} {bfl fl : Flow} {r : Result} (he : Abstract.exitFlow n bfl = some fl)
    (hb : flowBeh fl = some r.toBehaviour) : FlowRes n bfl r := by
  cases bfl with
  | normal ws | ret ws =>
    simp only [Abstract.exitFlow, Option.some.injEq] at he; subst he
    cases r <;> simp_all [flowBeh, Result.toBehaviour, FlowRes, Flow.retVals]
  | brk k ws =>
    cases k with
    | zero =>
      simp only [Abstract.exitFlow, Option.some.injEq] at he; subst he
      cases r <;> simp_all [flowBeh, Result.toBehaviour, FlowRes, Flow.retVals]
    | succ k => simp [Abstract.exitFlow] at he
  | trap =>
    simp only [Abstract.exitFlow, Option.some.injEq] at he; subst he
    cases r <;> simp_all [flowBeh, Result.toBehaviour, FlowRes]
  | throw t =>
    simp only [Abstract.exitFlow, Option.some.injEq] at he; subst he
    cases r <;> simp_all [flowBeh, Result.toBehaviour, FlowRes]

/-- **`closedCallOk` is complete for Core calls on the native slice**, every profile, no host:
every Core run of a call of a typed Wasm function, from a store and arguments of the native
slice (`NativeCallOk`), in any caller frame and with any `call_ref` annotation, ends in the
caller's frame and is answered by `closedCallOk` with its result. -/
theorem callCompleteG_closedCallOk (P : Profile) :
    CallCompleteG P (fun _ _ _ _ => False) Machine.NativeCallOk (Abstract.closedCallOk (H := H)) := by
  intro s s' f f' a fi ps rs us c r hG hc hfi hty hn hrun
  obtain ⟨hs, hF, hS, hok⟩ := hG
  have hw : WasmFuncs s := fun fi' hm => by
    obtain ⟨fn, hcode, -⟩ := hF fi' hm
    exact ⟨fn, hcode⟩
  have he := expand_of_funcType hty
  obtain ⟨hf, hg⟩ := (call_transport hrun ⟨r, rfl⟩ hw).2 us a c fi _ _ rfl hc hfi he
    (by simp [Ty.length_ofList, hn])
  refine ⟨hf, ?_⟩
  have hinv : Steps P closedHost (invoke s a us) ⟨s', {}, r.toAdmin⟩ := by
    have h2 : Steps P closedHost ⟨s, {}, vals us ++ [.ref (.func a), .callRefType fi.type]⟩
        ⟨s', {}, r.toAdmin⟩ := hg {} (.callRefType fi.type) trivial
    simpa [invoke, hfi] using h2
  obtain ⟨fi', ps', rs', bfl, fl, hfi', hty', hcl, hex, hbeh⟩ :=
    (Abstract.closedCall_core_iff hs hF hS hok P r s').2 ⟨_, hinv, rfl, rfl⟩
  rw [hfi] at hfi'; cases hfi'
  rw [hty] at hty'; cases hty'
  exact ⟨bfl, ⟨hcl, hS, hok⟩, flowRes_of_exit hex hbeh⟩

end Silmaril.Wasm.Cfg.Proofs.Region
