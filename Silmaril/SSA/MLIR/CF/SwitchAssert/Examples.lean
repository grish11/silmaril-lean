module

import Silmaril.SSA.MLIR.CF.SwitchAssert
import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Thms

/-! Executable and static checks for CF edges and assertion outcomes. -/

namespace Silmaril.MLIR.CF.SwitchAssert.Examples

open Arith (Width Env)
open Silmaril.MLIR.Pure (Eval i1)

private def i8 : Width := ⟨8, by decide⟩
private def i65 : Width := ⟨65, by decide⟩

private inductive Op : List Width → Width → Type where
  | inc : Op [i8] i8

private def evalOp : Eval Op
  | _, _, .inc, .cons n .nil => n + 1

private inductive JoinLabel : List Width → Type where
  | join : JoinLabel [i8]

/-- Both conditional edges target the join. Each passes a different input. -/
private def sameTarget : CF.Cfg Op JoinLabel [i1, i8, i8] [i8] where
  entry := .terminator (.condBr .here
    ⟨.join, .cons (.there .here) .nil⟩
    ⟨.join, .cons (.there (.there .here)) .nil⟩)
  block | .join => .terminator (.ret (.cons .here .nil))

private def joinInput (test : BitVec 1) : Env [i1, i8, i8] :=
  .cons test (.cons 7 (.cons 19 .nil))

example : sameTarget.run evalOp 2 (joinInput 1) = some (.cons 7 .nil) := rfl
example : sameTarget.run evalOp 2 (joinInput 0) = some (.cons 19 .nil) := rfl
example : (Cfg.embed sameTarget).run evalOp 2 (joinInput 1) =
    some (.returned (.cons 7 .nil)) := rfl
example : (Cfg.embed sameTarget).run evalOp 2 (joinInput 0) =
    some (.returned (.cons 19 .nil)) := rfl

example : True := by
  fail_if_success have _wrongCount : Edge JoinLabel [i1, i8, i8] := ⟨.join, .nil⟩
  fail_if_success
    have _wrongWidth : Edge JoinLabel [i1, i8, i8] := ⟨.join, .cons .here .nil⟩
  fail_if_success
    have _entryTarget : Edge JoinLabel [i1, i8, i8] :=
      { argsTy := [i1, i8, i8]
        label := sameTarget.entry
        args := .cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil)) }
  trivial

private inductive Label : List Width → Type where
  | matched : Label [i8]
  | fallback : Label [i1, i8]

/-- The cases differ only at bit 64 and pass different operands to the same
successor. The default forwards a tuple of a different type and arity. -/
private def dispatch : Cfg Op Label [i1, i65, i8, i8] [i8] where
  entry := .assert .here "dispatch enabled" <| .terminator (.switch {
    flag := .there .here
    widthSupported := by decide
    defaultEdge := ⟨.fallback, .cons .here (.cons (.there (.there (.there .here))) .nil)⟩
    cases := [(1, ⟨.matched, .cons (.there (.there .here)) .nil⟩),
      (18446744073709551617, ⟨.matched, .cons (.there (.there (.there .here))) .nil⟩)]
    unique := by decide
  })
  block
    | .matched =>
        .letOp .inc (.cons .here .nil) (.terminator (.basic (.ret (.cons .here .nil))))
    | .fallback => .terminator (.basic (.ret (.cons (.there .here) .nil)))

private def input (test : BitVec 1) (flag : BitVec 65) : Env [i1, i65, i8, i8] :=
  .cons test (.cons flag (.cons 7 (.cons 19 .nil)))

example : dispatch.run evalOp 2 (input 1 1) = some (.returned (.cons 8 .nil)) := rfl
example : dispatch.run evalOp 2 (input 1 18446744073709551617) =
    some (.returned (.cons 20 .nil)) := rfl
example : dispatch.run evalOp 2 (input 1 9) = some (.returned (.cons 19 .nil)) := rfl
example : dispatch.run evalOp 1 (input 1 9) = none := rfl
example : dispatch.run evalOp 0 (input 0 9) = none := rfl
example : dispatch.run evalOp 1 (input 0 9) = some .aborted := rfl

example : dispatch.denotePart evalOp (input 1 1) = Part.some (.returned (.cons 8 .nil)) :=
  (dispatch.denotePart_eq_some_iff evalOp (input 1 1) _).mpr ⟨2, rfl⟩

example : dispatch.denotePart evalOp (input 1 18446744073709551617) =
    Part.some (.returned (.cons 20 .nil)) :=
  (dispatch.denotePart_eq_some_iff evalOp (input 1 18446744073709551617) _).mpr ⟨2, rfl⟩

example : dispatch.denotePart evalOp (input 1 9) = Part.some (.returned (.cons 19 .nil)) :=
  (dispatch.denotePart_eq_some_iff evalOp (input 1 9) _).mpr ⟨2, rfl⟩

-- The default edge uses the first block's fuel and needs another block to return.
example : Elgot.Part.runFor (fun state => Part.some (dispatch.step evalOp (input 1 9) state)) 1
    ⟨_, dispatch.entry, input 1 9⟩ = Part.none :=
  dispatch.runFor_eq_ofOption_run evalOp 1 (input 1 9)

example : dispatch.denotePart evalOp (input 0 9) = Part.some .aborted :=
  (dispatch.denotePart_eq_some_iff evalOp (input 0 9) _).mpr ⟨1, rfl⟩

private inductive LoopLabel : List Width → Type where
  | again : LoopLabel []

/-- A default-only `i1` switch forms a cycle when the assertion succeeds. -/
private def loopBody : Block Op LoopLabel [] [i1] :=
  .assert .here "loop enabled" <| .terminator (.switch {
    flag := .here
    widthSupported := by decide
    defaultEdge := ⟨.again, .nil⟩
    cases := []
    unique := by decide
  })

private def loop : Cfg Op LoopLabel [i1] [] where
  entry := loopBody
  block | .again => loopBody

example : loop.run evalOp 1 (.cons 0 .nil) = some .aborted := rfl

private theorem loop_diverges : loop.Diverges evalOp (.cons 1 .nil) := by
  intro fuel
  induction fuel with
  | zero => rfl
  | succ _ ih => exact ih

example : loop.denotePart evalOp (.cons 1 .nil) = Part.none :=
  (loop.denotePart_eq_none_iff evalOp (.cons 1 .nil)).mpr loop_diverges

example : (16777215 : Nat) ≤ maxSwitchWidth := by decide
example : ¬ (16777216 : Nat) ≤ maxSwitchWidth := by decide
example : ¬ ([255, -1] : List (BitVec 8)).Nodup := by decide

end Silmaril.MLIR.CF.SwitchAssert.Examples
