module

public import Silmaril.Formats.Dasl.Lift.Defs

public section

namespace Silmaril.Proofs.Formats.Dasl.Lift

open Silmaril.Formats.Dasl
open Silmaril.Formats.Dasl.Lift

theorem nat_i64_exact {number : Nat} (fits : number < 2^63) :
    (UInt64.ofNat number).toInt64.toInt = (number : Int) := by
  rw [UInt64.toInt64_ofNat', Int64.toInt_ofNat', Int.bmod_eq_of_le]
  · change -(2^63 : Int) ≤ (number : Int)
    omega
  · change (number : Int) < 9223372036854775808
    omega

theorem length_i64_iff (ctx : Semantics.Naming.Lift.Coordinate) (length : ctx.Meaning → Nat)
    (root : ctx.Surface) (output : Value) :
    lengthI64 ctx length root output ↔ ∃ size, lengthNat ctx length root size ∧ natI64 output size := by
  constructor
  · rintro ⟨⟨context, size, _⟩, ⟨decoded, repr, _⟩, equation⟩
    exact ⟨size, ⟨(context, size, ()), ⟨decoded, rfl, trivial⟩, equation⟩, repr⟩
  · rintro ⟨size, ⟨⟨context, other, _⟩, ⟨decoded, equal, _⟩, equation⟩, repr⟩
    change size = other at equal
    cases equal
    exact ⟨(context, size, ()), ⟨decoded, repr, trivial⟩, equation⟩

end Silmaril.Proofs.Formats.Dasl.Lift
