module

import Silmaril.SSA.MLIR.SCF.IndexSwitch.Thms

namespace Silmaril.MLIR.SCF.IndexSwitch.Examples

open Arith (Width Env)
open Silmaril.MLIR.Pure (Eval)

private def i8 : Width := ⟨8, by decide⟩
private def i16 : Width := ⟨16, by decide⟩

private inductive Op : List Width → Width → Type where
  | inc8 : Op [i8] i8
  | addTen : Op [i16] i16
  | extend : Op [i8] i16
  | add16 : Op [i16, i16] i16

private def evalOp : Eval Op
  | _, _, .inc8, .cons x .nil => x + 1
  | _, _, .addTen, .cons x .nil => x + 10
  | _, _, .extend, .cons x .nil => x.zeroExtend 16
  | _, _, .add16, .cons x (.cons y .nil) => x + y

private abbrev Input := [i8, indexWidth, i16]
private abbrev Yielded := [i8, i16]

private def atZero : Arm Op Input Yielded :=
  .letOp .inc8 (.cons .here .nil)
    (.terminator (.cons .here (.cons (.there (.there (.there .here))) .nil)))

private def atTwoTo32 : Arm Op Input Yielded :=
  .letOp .addTen (.cons (.there (.there .here)) .nil)
    (.terminator (.cons (.there .here) (.cons .here .nil)))

private def atSignedMin : Arm Op Input Yielded :=
  .letOp .inc8 (.cons .here .nil) <|
  .letOp .inc8 (.cons .here .nil) <|
    .terminator (.cons .here (.cons (.there (.there (.there (.there .here)))) .nil))

private def dispatch : Program Op Input [i16] where
  Yielded := Yielded
  selector := .there .here
  cases := [(0, atZero), (4294967296, atTwoTo32), (-9223372036854775808, atSignedMin)]
  unique := by decide
  fallback := .terminator (.cons .here (.cons (.there (.there .here)) .nil))
  cont := .letOp .extend (.cons .here .nil) <|
    .letOp .add16 (.cons .here (.cons (.there (.there .here)) .nil)) <|
    .terminator (.cons .here .nil)

private def input (selector : CaseValue) : Env Input :=
  .cons 7 (.cons selector (.cons 300 .nil))

example : dispatch.eval evalOp (input 0) = .cons 308 .nil := rfl
example : dispatch.eval evalOp (input 4294967296) = .cons 317 .nil := rfl
example : dispatch.eval evalOp (input 9223372036854775808) = .cons 309 .nil := rfl
example : dispatch.eval evalOp (input 8589934592) = .cons 307 .nil := rfl

example : dispatch.lower.run evalOp 3 (input 0) = some (.returned (.cons 308 .nil)) := rfl
example : dispatch.lower.run evalOp 3 (input 4294967296) =
    some (.returned (.cons 317 .nil)) := rfl
example : dispatch.lower.run evalOp 3 (input 9223372036854775808) =
    some (.returned (.cons 309 .nil)) := rfl
example : dispatch.lower.run evalOp 4 (input 8589934592) =
    some (.returned (.cons 307 .nil)) := rfl
example : dispatch.lower.run evalOp 2 (input 0) = none := rfl

private def defaultOnly : Program Op [indexWidth, i16] [i16] where
  Yielded := [i16]
  selector := .here
  cases := []
  unique := by decide
  fallback := .letOp .addTen (.cons (.there .here) .nil) (.terminator (.cons .here .nil))
  cont := .terminator (.cons .here .nil)

example : defaultOnly.lower.run evalOp 3 (.cons 4294967296 (.cons 300 .nil)) =
    some (.returned (.cons 310 .nil)) := rfl

private def emptyYield : Program Op [indexWidth] [] where
  Yielded := []
  selector := .here
  cases := []
  unique := by decide
  fallback := .terminator .nil
  cont := .terminator .nil

example : emptyYield.lower.run evalOp 3 (.cons 0 .nil) = some (.returned .nil) := rfl

/-- The two Lean spellings name the same canonical 64-bit attribute. -/
example : ¬ ([-1, 18446744073709551615] : List CaseValue).Nodup := by decide

end Silmaril.MLIR.SCF.IndexSwitch.Examples
