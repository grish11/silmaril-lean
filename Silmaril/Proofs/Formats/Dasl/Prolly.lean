module

public import Silmaril.Formats.Dasl.Prolly.Defs

public section

namespace Silmaril.Proofs.Formats.Dasl.Prolly

open Silmaril.Formats.Dasl Silmaril.Formats.Dasl.Prolly Silmaril.Semantics.Prolly

variable {Name Key Payload : Type}

theorem block_roundtrip (key : Encode.TotalCodec Key (Shallow Name)) (payload : Encode.TotalCodec Payload (Shallow Name))
    {block : Block Name Key Payload} {encoded : Shallow Name} (hit : encodeBlock key payload block = some encoded) :
    decodeBlock key payload encoded = some block := by
  cases block with
  | leaf entries =>
    injection hit with same
    subst encoded
    change ((entriesCodec key payload).decode? ((entriesCodec key payload).encode entries)).map Block.leaf = _
    rw [(entriesCodec key payload).recovers]
    rfl
  | branch level children =>
    by_cases valid : 0 < level ∧ level < 2^63
    · simp only [encodeBlock, ite_eq_left valid, Option.some.injEq] at hit
      subst encoded
      have same : (UInt64.ofNat level).toNat = level := by
        rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt]
        exact valid.2.trans (by decide)
      change (if 0 < (UInt64.ofNat level).toNat ∧ (UInt64.ofNat level).toNat < 2^63 then
        ((entriesCodec key objectLink).decode? ((entriesCodec key objectLink).encode children)).map
          (Block.branch (UInt64.ofNat level).toNat) else none) = _
      simp [same, valid, (entriesCodec key objectLink).recovers]
    · simp [encodeBlock, valid] at hit

end Silmaril.Proofs.Formats.Dasl.Prolly
