module

import Silmaril.SSA.MLIR.SCF.For

/-! Zero and multiple trips, unsigned comparisons, and arithmetic admission. -/

namespace Silmaril.MLIR.SCF.For.Examples

open Arith (Width Env)
open Silmaril.MLIR.Pure (Eval i1)

private def i8 : Width := ⟨8, by decide⟩
private def i16 : Width := ⟨16, by decide⟩

private inductive Op : List Width → Width → Type where
  | widen : Op [i8] i16
  | add : Op [i16, i16] i16
  | lowBit : Op [i8] i1

private def evalOp : Eval Op
  | _, _, .widen, .cons n .nil => BitVec.ofNat 16 n.toNat
  | _, _, .add, .cons a (.cons b .nil) => a + b
  | _, _, .lowBit, .cons n .nil => BitVec.ofBool (n.getLsbD 0)

/-- Accumulate the widened induction values and carry the last low bit.
The continuation adds a captured bias and returns the tuple. -/
private def sumInductions : For Op [i16, i8, i8, i8, i16, i1] [i16, i1] where
  width := i8
  widthSupported := by decide
  Carried := [i16, i1]
  lowerBound := .there .here
  upperBound := .there (.there .here)
  step := .there (.there (.there .here))
  init := .cons (.there (.there (.there (.there .here))))
    (.cons (.there (.there (.there (.there (.there .here))))) .nil)
  body :=
    .letOp .widen (.cons .here .nil) <|
    .letOp .add (.cons .here (.cons (.there (.there .here)) .nil)) <|
    .letOp .lowBit (.cons (.there (.there .here)) .nil) <|
    .terminator (.yield (.cons (.there .here) (.cons .here .nil)))
  cont :=
    .letOp .add (.cons .here (.cons (.there (.there .here)) .nil)) <|
    .terminator (.ret (.cons .here (.cons (.there (.there .here)) .nil)))

private def input (lower upper step : BitVec 8) : Env [i16, i8, i8, i8, i16, i1] :=
  .cons 5 (.cons lower (.cons upper (.cons step (.cons 10 (.cons 1 .nil)))))

private def zero : Env [i16, i8, i8, i8, i16, i1] := input 134 134 3
private def multiple : Env [i16, i8, i8, i8, i16, i1] := input 126 134 3

example : sumInductions.run evalOp zero = some (.cons 15 (.cons 1 .nil)) := rfl
example : sumInductions.run evalOp (input 135 134 3) = some (.cons 15 (.cons 1 .nil)) := rfl
example : sumInductions.lower.run (For.lowerEval evalOp) 2 zero = none := rfl
example : sumInductions.lower.run (For.lowerEval evalOp) 3 zero = some (.cons 15 (.cons 1 .nil)) := rfl

/-- Unsigned comparison visits 126, 129, and 132. The exiting induction is 135. -/
example : sumInductions.tripCount multiple = 3 := rfl
example : sumInductions.inductionAt multiple 3 = 135 := rfl
example : sumInductions.run evalOp multiple = some (.cons 402 (.cons 0 .nil)) := rfl
example : sumInductions.lower.run (For.lowerEval evalOp) 8 multiple = none := rfl
example : sumInductions.lower.run (For.lowerEval evalOp) 9 multiple =
    some (.cons 402 (.cons 0 .nil)) := rfl

example : sumInductions.lower.run (For.lowerEval evalOp) 9 multiple =
    sumInductions.run evalOp multiple :=
  sumInductions.lower_run_at evalOp multiple (by decide)

example : sumInductions.run evalOp (input 126 134 0) = none := rfl

/-- The only body would see 252, but its following update to 256 overflows. -/
example : sumInductions.tripCount (input 252 255 4) = 1 := rfl
example : sumInductions.run evalOp (input 252 255 4) = none := rfl

end Silmaril.MLIR.SCF.For.Examples
