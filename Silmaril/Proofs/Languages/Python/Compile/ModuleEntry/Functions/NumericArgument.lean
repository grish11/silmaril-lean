module

public import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.NumericArgument.Defs

public section
namespace Silmaril.Proofs.Languages.Python.Compile.ModuleEntry.Functions.NumericArgument

open Silmaril.Languages.Python.Compile.ModuleEntry.Functions.NumericArgument

theorem power_magnitude {base exponent result : Int} (checked : power? base exponent = some result) :
    result.natAbs < 2 ^ 4096 := by
  unfold power? at checked
  split at checked
  next bounds =>
    have result_eq := Option.some.inj checked
    subst result
    rw [Int.natAbs_pow]
    by_cases zero : exponent.toNat = 0
    · rw [zero, Nat.pow_zero]
      exact Nat.one_lt_two_pow (n := 4096) (by decide)
    · calc
        _ < (2 ^ (base.natAbs.log2 + 1)) ^ exponent.toNat :=
          Nat.pow_lt_pow_left Nat.lt_log2_self zero
        _ = 2 ^ ((base.natAbs.log2 + 1) * exponent.toNat) := (Nat.pow_mul _ _ _).symm
        _ ≤ _ := Nat.pow_le_pow_right (by decide) bounds.2
  next => contradiction

theorem testBit_bitwise (operation : Bool → Bool → Bool) (left right : Int) (index : Nat) :
    testBit (bitwise operation left right) index = operation (testBit left index) (testBit right index) := by
  let lhs := signBit left
  let rhs := signBit right
  let sign := operation lhs rhs
  let op := fun x y => operation (x ^^ lhs) (y ^^ rhs) ^^ sign
  have zero : op false false = false := by simp [op, sign]
  have encode (negative : Bool) (bits : Nat) :
      testBit (if negative then .negSucc bits else .ofNat bits) index = (bits.testBit index ^^ negative) := by
    cases negative <;> rfl
  change testBit (if sign then .negSucc (Nat.bitwise op _ _) else .ofNat (Nat.bitwise op _ _)) index = _
  rw [encode, Nat.testBit_bitwise zero]
  change ((operation (testBit left index) (testBit right index) ^^ sign) ^^ sign) = _
  rw [Bool.xor_assoc, Bool.xor_self, Bool.xor_false]

end Silmaril.Proofs.Languages.Python.Compile.ModuleEntry.Functions.NumericArgument
