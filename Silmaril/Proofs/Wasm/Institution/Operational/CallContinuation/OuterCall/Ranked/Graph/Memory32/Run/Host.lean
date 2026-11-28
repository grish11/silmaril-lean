module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Run.Host.Defs
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Run.Guard

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.RunProofs

open Execution.Runtime (Frame MemAddr MemInst Result Value)
open Wasm.V1.Execution

theorem host_store {H : Type} {mode : MemoryMode} {program : Program} {address : MemAddr}
    {base after : Store H} {initial : MemInst} (layout : Layout program base address initial)
    {before : ByteArray} (extent : mode.extent initial.data.size before)
    (effect : HostStoreEffect mode address initial (storeWithBytes base address initial before) after) :
    ∃ bytes, after = storeWithBytes base address initial bytes ∧
      mode.extent initial.data.size bytes ∧ before.size ≤ bytes.size ∧
      Layout program after address { initial with data := bytes } := by
  obtain ⟨prior, bytes, present, next, returned⟩ := effect
  have same := Option.some.inj (present.symm.trans (layout.with_bytes before).memory)
  have priorEq : prior = before := congrArg MemInst.data same
  subst prior
  have rendered : after = storeWithBytes base address initial bytes := by
    rw [returned]
    simp [storeWithBytes, setMemory, List.set_set]
  have bounded : mode.extent initial.data.size bytes ∧ before.size ≤ bytes.size := by
    cases mode with
    | fixed =>
      exact ⟨next.trans extent, next.symm.le⟩
    | growing =>
      exact ⟨⟨extent.1.trans next.1, next.2⟩, next.1⟩
  exact ⟨bytes, rendered, bounded.1, bounded.2, rendered.symm ▸ layout.with_bytes bytes⟩

theorem host_return {H : Type} {mode : MemoryMode} {program : Program} {address : MemAddr}
    {base after : Store H} {initial : MemInst} (layout : Layout program base address initial)
    {before : ByteArray} (extent : mode.extent initial.data.size before)
    {site : HostCall.V1.Site H} {host : HostSemantics H} {args : List Value} {r : Result}
    (contract : site.ReturnContract host (HostStoreEffect mode address initial)
      (storeWithBytes base address initial before) args)
    (returned : host site.target (storeWithBytes base address initial before) args (.returned after r))
    {calls : CallMode} {rank : Nat} {caller : Frame} {saved : List Value} {tail : List Admin}
    (continuation : CodeAllowedFor mode program address calls rank caller.module tail) :
    let code := values saved ++ result r ++ tail
    ∃ bytes, HostCall.V1.ResultTyped site.signature.results r ∧ before.size ≤ bytes.size ∧
      Layout program after address { initial with data := bytes } ∧
      ReadyFor mode program address calls rank initial.data.size ⟨bytes, caller, code⟩ ∧
      HostCall.V1.resumed after caller saved tail r = render base address initial ⟨bytes, caller, code⟩ := by
  obtain ⟨typed, effect⟩ := contract _ _ returned
  obtain ⟨bytes, rendered, bounded, monotone, liveLayout⟩ := host_store layout extent effect
  have admitted : CodeAllowedFor mode program address calls rank caller.module (result r) := by
    cases r with
    | values vs => exact values_allowed vs
    | trap => exact single_allowed.mpr .trap
  have ready : CodeAllowedFor mode program address calls rank caller.module (values saved ++ result r ++ tail) :=
    append_allowed.mpr ⟨append_allowed.mpr ⟨values_allowed saved, admitted⟩, continuation⟩
  exact ⟨bytes, typed, monotone, liveLayout, ⟨bounded, ready⟩, by rw [rendered]; rfl⟩

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.RunProofs
