module

import Silmaril.SSA.MLIR.SCF.ParallelYield.Thms

/-! A captured, heterogeneous reduction with an enclosing structural yield. -/

namespace Silmaril.MLIR.SCF.ParallelYield.Examples

open Arith (Width Env)
open Silmaril.MLIR.Pure (Eval OpSignature i1)

private def i8 : Width := ⟨8, by decide⟩

private inductive Op : OpSignature where
  | add (w : Width) : Op [w, w] w

private def evalOp : Eval Op
  | _, _, .add _, .cons left (.cons right .nil) => left + right

private def addRegion (w : Width) : Combiner Op [i8, i1] w :=
  .letOp (.add w) (.cons .here (.cons (.there .here) .nil)) (.terminator (.ret .here))

private def program : Program Op [i8, i1] [i1, i8] where
  indexWidth := i8
  space := ⟨1, 5, 3, by decide⟩
  stepFits := by decide
  exitFits := by decide
  Slots := [i8, i1]
  initial := .cons .here (.cons (.there .here) .nil)
  body := .terminator (.reduce (.cons .here (.cons (.there (.there .here)) .nil)))
  combiners := .cons (addRegion i8) (.cons (addRegion i1) .nil)
  continuation :=
    .letOp (.add i8) (.cons .here (.cons (.there (.there .here)) .nil))
      (.terminator (.yield (.cons (.there (.there .here)) (.cons .here .nil))))

private def captures : Env [i8, i1] := .cons 10 (.cons 1 .nil)
private def reduced : Env program.Slots := .cons 15 (.cons 1 .nil)
private def result : Env [i1, i8] := .cons 1 (.cons 25 .nil)

private theorem laws : program.combiners.Laws evalOp captures :=
  ⟨⟨BitVec.add_assoc⟩, ⟨BitVec.add_comm⟩, ⟨BitVec.add_assoc⟩, ⟨BitVec.add_comm⟩, trivial⟩

example : (program.reduction evalOp captures).denote program.space = reduced := rfl

example : program.denote evalOp captures = result := rfl

example (observed : Env [i1, i8]) :
    program.Returns evalOp captures observed ↔ observed = result :=
  program.returns_iff_eq_denote evalOp captures observed laws

/-- The region's local sum and reordered slots are exposed at a fragment return. -/
example : program.continuation.asReturn.eval evalOp Return.eval (reduced.append captures) = result :=
  program.continuation.asReturn_eval evalOp reduced captures

private def emptyProgram : Program Op [i8, i1] [i1, i8] :=
  { program with
    space := ⟨5, 1, 3, by decide⟩
    stepFits := by decide
    exitFits := by decide }

example (observed : Env [i1, i8]) :
    emptyProgram.Returns evalOp captures observed ↔ observed = .cons 1 (.cons 20 .nil) :=
  emptyProgram.returns_iff_of_empty evalOp captures observed (by decide)

end Silmaril.MLIR.SCF.ParallelYield.Examples
