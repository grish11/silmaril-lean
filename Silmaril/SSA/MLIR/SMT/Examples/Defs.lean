module

public import Silmaril.SSA.MLIR.SMT.Defs

@[expose] public section

namespace Silmaril.MLIR.SMT.Examples

/-- For input `p`, bind `saved = not p`, then yield the formula
`∀ x : Bool, ∃ y : Bool, y = x ∧ y = saved`. -/
def captured : Block [.bool] .bool :=
  .letOp (.not .here) <|
    .letQuantifier .all .bool []
      (.letQuantifier .ex .bool []
        (.letOp (.eq .here (.there .here)) <|
          .letOp (.eq (.there .here) (.there (.there (.there .here)))) <|
            .letOp (.and (.there .here) .here) <| .yield .here)
        (.yield .here))
      (.yield .here)

/-- Yield `∀ n : Int, ∃ (m : Int) (flag : Bool), flag ∧ m = n + 1`.
The nested body captures both the outer argument `n` and the earlier constant. -/
def successor : Block [] .bool :=
  .letOp (.intConst 1) <|
    .letQuantifier .all .int []
      (.letQuantifier .ex .int [.bool]
        (.letOp (.add (.there (.there .here)) (.there (.there (.there .here)))) <|
          .letOp (.eq (.there (.there .here)) .here) <|
            .letOp (.and (.there (.there .here)) .here) <| .yield .here)
        (.yield .here))
      (.yield .here)

/-- Yield `smt.eq` on three Int inputs in context order. -/
def chainedEquality : Block [.int, .int, .int] .bool :=
  .letOp (.eq .here (.there .here) [.there (.there .here)]) (.yield .here)

/-- For input `n`, quantify over `x : Int` and check that `n + 1 ≤ x`,
`n < x`, `x ≥ n + 1`, and `x > n` are all equal. -/
def orderedBounds : Block [.int] .bool :=
  .letOp (.intConst 1) <|
    .letOp (.add (.there .here) .here) <|
      .letQuantifier .all .int []
        (.letOp (.intCmp .gt .here (.there (.there (.there .here)))) <|
          .letOp (.intCmp .ge (.there .here) (.there (.there .here))) <|
            .letOp (.intCmp .lt
              (.there (.there (.there (.there (.there .here))))) (.there (.there .here))) <|
              .letOp (.intCmp .le
                (.there (.there (.there (.there .here)))) (.there (.there (.there .here)))) <|
                .letOp (.eq .here (.there .here)
                  [.there (.there .here), .there (.there (.there .here))]) <| .yield .here)
        (.yield .here)

end Silmaril.MLIR.SMT.Examples
