module

public import Silmaril.Semantics.Calco2019.Trace.CounterSemiring.ThreeCycle.Defs

/-! # Scalar Conway star and doubling admit a three-cycle separator

The equations here concern one-state weighted iteration and scalar Conway star.
-/

public section

namespace Silmaril.Calco2019.CounterSemiring.ThreeCycle.Scalar

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

instance : CommSemiring Scalar where
  zero := 0
  one := 1
  add := (· + ·)
  mul := (· * ·)
  add_assoc := by decide
  zero_add := by decide
  add_zero := by decide
  add_comm := by decide
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide
  mul_comm := by decide
  zero_mul := by decide
  mul_zero := by decide
  left_distrib := by decide
  right_distrib := by decide
  nsmul := nsmulRec

theorem star_add : ∀ a b : Scalar, star (a + b) = star a * star (b * star a) := by decide

theorem star_mul : ∀ a b : Scalar, star (a * b) = 1 + a * star (b * a) * b := by decide

theorem iterate_fixpoint (a b : Scalar) : iterate a b = b + a * iterate a b := by
  exact (show ∀ a b : Scalar, iterate a b = b + a * iterate a b from by decide) a b

theorem iterate_naturality (a b c : Scalar) : iterate a b * c = iterate a (b * c) :=
  mul_assoc _ _ _

theorem iterate_codiagonal (a b out : Scalar) :
    iterate (iterate a b) (iterate a out) = iterate (a + b) out := by
  exact (show ∀ a b out : Scalar, iterate (iterate a b) (iterate a out) = iterate (a + b) out
    from by decide) a b out

/-- Doubling holds for every scalar recurrence and exit weight. -/
theorem iterate_double : ∀ a b : Scalar, iterate (a * a) (b + a * b) = iterate a b := by decide

/-- Tripling fails for the generator and exit weight one. -/
theorem iterate_triple_ne :
    iterate ((generator * generator) * generator)
      (1 + generator * (1 + generator * 1)) ≠ iterate generator 1 := by decide

end Silmaril.Calco2019.CounterSemiring.ThreeCycle.Scalar
