module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Checked.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitChecked

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst

open Silmaril.Formats Silmaril.Wasm.Execution.Core Silmaril.Wasm.Component

/-- The checked resolver refines the successful part of the writer interpretation. -/
theorem Own.resolveOpChecked_toOption (S : WitSig) (rt : Own.RT) (raw : Own.ROp S) :
    (Own.resolveOpChecked S rt raw).toOption = Own.resolveOp S rt raw :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitChecked.resolveOpChecked_toOption S rt raw

/-- Rejection preserves the table held at the start of this import, not the initial table of the
instance. -/
theorem Own.nodeResult_rejected (S : WitSig) (rt : Own.RT) (issue : NodeIssue) :
    Own.nodeResult S rt (.error issue) = (.error issue, rt) := rfl

/-- An import error permits only a call-local trap with the caller's store unchanged. -/
theorem checkedReply_rejected {Value : Type} (issue : NodeIssue) (call : UCall Nat)
    (onSuccess : Value → UReply → Prop) (reply : UReply) :
    checkedReply (.error issue) call onSuccess reply ↔ reply = ⟨call.store, .trap⟩ := Iff.rfl

/-- A speculative segment cannot bypass the canonical byte limits with a larger memory. -/
theorem boundedPayloadSegment_rejected (o : Accept.Callout) (address length : Nat)
    (tooLong : Component.Limits.spec.maxListBytes < length) :
    boundedPayloadSegment o address length = none := by
  simp [boundedPayloadSegment, Nat.not_le_of_lt tooLong]

/-- The checked decoder returns the canonical text or the same failure in every string mode. -/
theorem checked_string_reference (address : AddrType) (encoding : Component.ABI.StringEncoding)
    (o : Accept.Callout)
    (mem : ByteArray) (memory : o.mem = some mem) {bytes rest : List UInt8} {ptr tagged : Nat}
    (range : readPtrLenFor address bytes = some (ptr, tagged, rest)) :
    readValWith (checkedPayloadReader encoding o address) .string bytes =
      (Component.ABI.loadStringFromRange? encoding address mem.data.toList ptr tagged).map
        (fun value => (value.str, rest)) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitChecked.checked_string_reference
    address encoding o mem memory range

end Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst
