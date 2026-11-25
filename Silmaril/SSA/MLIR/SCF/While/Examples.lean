module

import Silmaril.SSA.MLIR.SCF.While

/-! Executable and divergence checks for the public SCF-to-CF interface. -/

namespace Silmaril.MLIR.SCF.Examples

open Arith (Width Env BinOp)
open Silmaril.MLIR.Pure (Eval i1)

private def i8 : Width := ⟨8, by decide⟩
private def i16 : Width := ⟨16, by decide⟩

private inductive Op : List Width → Width → Type where
  | ltTwo : Op [i8] i1
  | widen : Op [i8] i16
  | addWide : Op [i16, i16] i16
  | inc : Op [i8] i8
  | trueBit : Op [] i1

private def evalOp : Eval Op
  | _, _, .ltTwo, .cons n .nil => if n.toNat < 2 then 1 else 0
  | _, _, .widen, .cons n .nil => BitVec.ofNat 16 n.toNat
  | _, _, .addWide, .cons x (.cons y .nil) => BinOp.addi.denote x y
  | _, _, .inc, .cons n .nil => BinOp.addi.denote n 1
  | _, _, .trueBit, .nil => 1

/-- The before region forwards a wide result and the old counter. The after
region increments the counter. Before and the parent continuation each add
the captured wide input once. -/
private def countToTwo : While Op [i8, i16] [i16, i8] where
  State := [i8]
  Payload := [i16, i8]
  init := .cons .here .nil
  before :=
    .letOp .ltTwo (.cons .here .nil) <|
    .letOp .widen (.cons (.there .here) .nil) <|
    .letOp .addWide (.cons .here (.cons (.there (.there (.there (.there .here)))) .nil)) <|
    .terminator (.condition (.there (.there .here))
      (.cons .here (.cons (.there (.there (.there .here))) .nil)))
  after :=
    .letOp .inc (.cons (.there .here) .nil) <|
    .terminator (.yield (.cons .here .nil))
  cont :=
    .letOp .addWide (.cons .here (.cons (.there (.there (.there .here))) .nil)) <|
    .terminator (.ret (.cons .here (.cons (.there (.there .here)) .nil)))

private def input : Env [i8, i16] := .cons 0 (.cons 40 .nil)
private def result : Env [i16, i8] := .cons 82 (.cons 2 .nil)

example : countToTwo.run evalOp 2 input = none := rfl
example : countToTwo.run evalOp 3 input = some result := rfl
example : countToTwo.lower.run evalOp 6 input = none := rfl
example : countToTwo.lower.run evalOp 7 input = some result := rfl

/-- Starting at the bound skips the after region and still executes the
parent continuation. -/
example : countToTwo.run evalOp 1 (.cons 2 (.cons 40 .nil)) = some result := rfl
example : countToTwo.lower.run evalOp 3 (.cons 2 (.cons 40 .nil)) = some result := rfl

/-- Empty before and after parameter lists still allow an unconditional cycle. -/
private def forever : While Op [] [] where
  State := []
  Payload := []
  init := .nil
  before := .letOp .trueBit .nil (.terminator (.condition .here .nil))
  after := .terminator (.yield .nil)
  cont := .terminator (.ret .nil)

private theorem forever_diverges : forever.Diverges evalOp .nil := by
  intro fuel
  induction fuel with
  | zero => rfl
  | succ _ ih => exact ih

example : forever.lower.Diverges evalOp .nil :=
  (forever.lower_diverges_iff evalOp .nil).2 forever_diverges

end Silmaril.MLIR.SCF.Examples
