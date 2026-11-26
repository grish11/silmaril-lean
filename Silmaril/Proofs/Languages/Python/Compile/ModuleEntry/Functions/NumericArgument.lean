module

public import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.NumericArgument.Defs

public section
namespace Silmaril.Proofs.Languages.Python.Compile.ModuleEntry.Functions.NumericArgument

open Silmaril.Languages.Python.Compile.ModuleEntry.Functions.NumericArgument

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
