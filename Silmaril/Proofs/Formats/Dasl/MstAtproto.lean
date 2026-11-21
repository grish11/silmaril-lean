module

public import Silmaril.Formats.Dasl.Mst.Atproto.Defs

public section

namespace Silmaril.Proofs.Formats.Dasl.MstAtproto

open Silmaril.Formats.Dasl.Mst Silmaril.Formats.Dasl.Mst.Atproto

theorem keyLayer_le (key : Key) : keyLayer key ≤ 128 := by
  have bitsBound (bytes : List UInt8) : leadingZeroBits bytes ≤ 8 * bytes.length := by
    induction bytes with
    | nil => exact Nat.le_refl _
    | cons byte tail ih =>
      unfold leadingZeroBits
      split <;> simp only [List.length_cons] <;> omega
  have bound := bitsBound (Crypto.SHA256.digest key)
  rw [Crypto.SHA256.digest_length] at bound
  unfold keyLayer
  omega

end Silmaril.Proofs.Formats.Dasl.MstAtproto
