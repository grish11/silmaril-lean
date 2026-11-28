module

public import Silmaril.Languages.Starlark.Lists.GoDictionary.Abstraction.Defs
import Silmaril.Languages.Starlark.Lists.Thms

public section

namespace Silmaril.Proofs.Languages.Starlark.Lists.GoDictionary.Abstraction

open Silmaril.Languages.Starlark
open Silmaril.Languages.Starlark.Lists (Heap State ScalarKey)
open Silmaril.Languages.Starlark.Lists.GoDictionary (scalarHash numberHash finiteInt storedHash hashKey hashAt intHash)
open Silmaril.Languages.Starlark.Lists.GoDictionary.Abstraction

/-- Every scalar's raw Go hash factors through the exact canonical key. -/
private def codeHash : ScalarKey → UInt32
  | .none => 0
  | .bool flag => if flag then 1 else 0
  | .number value => numberHash value

private theorem scalarHash_code (value : Value) :
    scalarHash value = codeHash (ScalarKey.ofValue value) := by
  cases value with
  | int value =>
    have nonzero : (2 ^ 1074 : Int) ≠ 0 := Int.pow_ne_zero (by decide)
    simp only [scalarHash, codeHash, ScalarKey.ofValue, ScalarKey.int, Binary64.Number.ofInt, numberHash, finiteInt]
    split
    · rw [Int.mul_tdiv_cancel _ nonzero]
    · rw [Int.mul_ediv_cancel _ nonzero]
  | none | bool | float => rfl

private theorem scalar_compare (left right : Value) :
    Lists.Comparison.scalarEqual left right =
      (([.scalar (ScalarKey.ofValue left)] : Lists.Key) == [.scalar (ScalarKey.ofValue right)]) := by
  let state : State := {}
  have leftCode : state.keyOf (.scalar left) = .ok [.scalar (ScalarKey.ofValue left)] := rfl
  have rightCode : state.keyOf (.scalar right) = .ok [.scalar (ScalarKey.ofValue right)] := rfl
  have yes := Lists.scalar_key_match_iff_eq leftCode rightCode
  have out : applyBinary .eq left right = .ok (.bool (Lists.Comparison.scalarEqual left right)) := by
    simp only [applyBinary, Lists.Comparison.scalarEqual]
    cases left.orderedCompare right <;> rfl
  rw [out, Except.ok.injEq, Value.bool.injEq] at yes
  exact Bool.eq_iff_iff.mpr yes.symm

theorem scalar_coherent (heap : Heap) : Coherent heap scalarProfile := by
  constructor
  · intro key obs admitted
    cases key <;> simp [scalarProfile] at admitted
    subst obs
    rfl
  · intro key obs admitted
    cases key <;> simp [scalarProfile] at admitted
    subst obs
    exact ⟨_, rfl, rfl⟩
  · intro left right a b ha hb _
    cases left <;> simp [scalarProfile] at ha
    cases right <;> simp [scalarProfile] at hb
    subst a
    subst b
    exact congrArg Except.ok (scalar_compare ..)
  · intro left right a b ha hb same
    cases left <;> simp [scalarProfile] at ha
    cases right <;> simp [scalarProfile] at hb
    subst a
    subst b
    simp only [List.cons.injEq, Lists.KeyPart.scalar.injEq, and_true] at same
    simp only [scalarHash_code, same]

end Silmaril.Proofs.Languages.Starlark.Lists.GoDictionary.Abstraction
