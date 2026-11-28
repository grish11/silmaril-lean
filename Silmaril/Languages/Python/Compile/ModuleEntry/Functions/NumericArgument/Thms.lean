module

public import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.NumericArgument.Defs
import Silmaril.Proofs.Languages.Python.Compile.ModuleEntry.Functions.NumericArgument

public section
namespace Silmaril.Languages.Python.Compile.ModuleEntry.Functions.NumericArgument

theorem check_binary {operator : Source.BinaryOperator} {left right : Source.Expr} {lhs rhs result : Int}
    (leftChecked : integer? left = some lhs) (rightChecked : integer? right = some rhs)
    (computed : binary? operator lhs rhs = some result) :
    check (.binary operator left right) = some (.integer result) := by
  simp [check, integer?, leftChecked, rightChecked, computed]

theorem check_add {left right : Source.Expr} {lhs rhs : Int}
    (leftChecked : integer? left = some lhs) (rightChecked : integer? right = some rhs) :
    check (.binary .add left right) = some (.integer (lhs + rhs)) :=
  check_binary leftChecked rightChecked rfl

theorem check_sub {left right : Source.Expr} {lhs rhs : Int}
    (leftChecked : integer? left = some lhs) (rightChecked : integer? right = some rhs) :
    check (.binary .sub left right) = some (.integer (lhs - rhs)) :=
  check_binary leftChecked rightChecked rfl

theorem check_mul {left right : Source.Expr} {lhs rhs : Int}
    (leftChecked : integer? left = some lhs) (rightChecked : integer? right = some rhs) :
    check (.binary .mul left right) = some (.integer (lhs * rhs)) :=
  check_binary leftChecked rightChecked rfl

theorem power_iff {base exponent result : Int} :
    power? base exponent = some result ↔
      0 ≤ exponent ∧ (base.natAbs.log2 + 1) * exponent.toNat ≤ 4096 ∧ result = base ^ exponent.toNat := by
  unfold power?
  split <;> simp_all [eq_comm]

theorem power_magnitude {base exponent result : Int} (checked : power? base exponent = some result) :
    result.natAbs < 2 ^ 4096 :=
  Proofs.Languages.Python.Compile.ModuleEntry.Functions.NumericArgument.power_magnitude checked

theorem check_power {left right : Source.Expr} {base exponent result : Int}
    (lhs : integer? left = some base) (rhs : integer? right = some exponent)
    (checked : power? base exponent = some result) :
    check (.binary .pow left right) = some (.integer result) :=
  check_binary lhs rhs checked

theorem testBit_bitwise (operation : Bool → Bool → Bool) (left right : Int) (index : Nat) :
    testBit (bitwise operation left right) index = operation (testBit left index) (testBit right index) :=
  Proofs.Languages.Python.Compile.ModuleEntry.Functions.NumericArgument.testBit_bitwise operation left right index

end Silmaril.Languages.Python.Compile.ModuleEntry.Functions.NumericArgument
