module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.Generation.Example.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.Generation.Thms

/-! # Generate the written nested CFG in the existing quotient -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.GenerationExample

open Paper.Extension.Singleton (ofRegion)
open Paper.Extension.Singleton.Generation (Generated)

theorem round_fragment : GuardedFragment false round_typed :=
  guarded_let₁_of_return false (ha := refresh_typed) (hp := poll_typed) rfl
    (.returned (.primitive Op.refresh (.var (i := 0) rfl)))
    (.returned (.primitive Op.poll (.var (i := 0) rfl)))

theorem nested_fragment : GuardedFragment false nested_typed :=
  .iterate (hr := inner_typed) (.iterate (hr := round_typed) round_fragment)

theorem nested_generated :
    Generated (Step (τ := Ty Empty) (Φ := Op) false)
      (ofRegion (Step (τ := Ty Empty) (Φ := Op) false) nested_typed) :=
  generated_guardedFragment false nested_fragment

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.GenerationExample
