module

public import Silmaril.Wasm.Binary.Packed.Defs

/-! A packed decoder certificate for the shape `header; data section; one passive segment`.
Positions can be proposed by preprocessing, but each is checked by a real packed reader. -/

@[expose] public section

namespace Silmaril.Wasm.Binary.Packed

structure PassivePlan where
  sectionStart : Nat
  afterCount : Nat
  afterMode : Nat
  payloadStart : Nat

/-- The only section starts at offset eight and reaches EOF. A valid certificate reads the
header, data section id and size, vector count, passive mode and byte-vector length directly
from the packed source. Payload agreement compares packed bytes at the resulting cursor. -/
structure PassivePlan.Verified (plan : PassivePlan) (source : KBytes) (wf : source.wf = true)
    (payload : KBytes) : Prop where
  sectionPresent : 8 < source.len
  countFits : plan.afterCount < source.len
  consumesInput : plan.payloadStart + payload.len = source.len
  header : readHeader.run ⟨source, wf, 0⟩ = .ok ((), ⟨source, wf, 8⟩)
  id : readByte.run ⟨source, wf, 8⟩ = .ok (11, ⟨source, wf, 9⟩)
  size : (readU 32).run ⟨source, wf, 9⟩ =
    .ok (source.len - plan.sectionStart, ⟨source, wf, plan.sectionStart⟩)
  count : (readU 32).run ⟨source, wf, plan.sectionStart⟩ = .ok (1, ⟨source, wf, plan.afterCount⟩)
  mode : (readU 32).run ⟨source, wf, plan.afterCount⟩ = .ok (1, ⟨source, wf, plan.afterMode⟩)
  length : (readU 32).run ⟨source, wf, plan.afterMode⟩ =
    .ok (payload.len, ⟨source, wf, plan.payloadStart⟩)
  payloadMatches : (source.slice plan.payloadStart payload.len).sameBytes 4096 payload = true

end Silmaril.Wasm.Binary.Packed
