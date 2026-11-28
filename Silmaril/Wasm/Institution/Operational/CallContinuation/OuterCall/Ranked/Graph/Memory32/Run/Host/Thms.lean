module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Run.Host.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Run.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Run.Host

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32

open Execution.Runtime (Frame MemAddr MemInst Result Value)
open Wasm.V1.Execution

/-- Recover the exact live bytes and allocated function/table layout from a
proved host store effect. The resulting store is still rendered against the
original base, with extent measured from the live pre-call memory. -/
theorem Layout.host_store {H : Type} {mode : MemoryMode} {program : Program} {address : MemAddr}
    {base after : Store H} {initial : MemInst} (layout : Layout program base address initial)
    {before : ByteArray} (extent : mode.extent initial.data.size before)
    (effect : HostStoreEffect mode address initial (storeWithBytes base address initial before) after) :
    ∃ bytes, after = storeWithBytes base address initial bytes ∧
      mode.extent initial.data.size bytes ∧ before.size ≤ bytes.size ∧
      Layout program after address { initial with data := bytes } :=
  RunProofs.host_store layout extent effect

/-- A contracted return, including a trap, supplies a ready administrative
continuation and an exact rendering of its native resumption on the returned
store. The caller supplies the existing guard for its continuation. -/
theorem Layout.host_return {H : Type} {mode : MemoryMode} {program : Program} {address : MemAddr}
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
      HostCall.V1.resumed after caller saved tail r = render base address initial ⟨bytes, caller, code⟩ :=
  RunProofs.host_return layout extent contract returned continuation

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32
