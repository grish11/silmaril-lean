module

import Silmaril.Wasm.Execution.Core.Intrinsic.Thms

open Silmaril.Wasm Silmaril.Wasm.Validation Silmaril.Wasm.Numerics Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Execution.Core.Intrinsic

private def world : World Unit {} where
  store := {}
  moduleInst := {}
  storeOk := by constructor <;> simp
  moduleOk := ModuleInstOk.mk (k := 0) (by simp) .nil .nil .nil .nil .nil
    (by simp) .nil (by simp) (by simp) (by simp) (by simp)

private def twoLocals := [IntType.i32, .i32]

private def divisionCode (sign : Signedness) : Code twoLocals [.i64] [.i32, .i64] :=
  .seq (.localGet .here (by decide))
    (.seq (.localGet (.there .here) (by decide)) (.seq (.intBin (.div sign)) (.seq .nop .done)))

private def start (lhs rhs : BitVec 32) (sign : Signedness) : State world twoLocals [.i32, .i64] :=
  ⟨⟨.cons lhs (.cons rhs .nil)⟩, .run (.cons 99 .nil) (divisionCode sign)⟩

private abbrev resultValues : Result := .values [.i64 99, .i32 12]

private def finish : Config Unit := ⟨world.store, (start 84 7 .unsigned).frame.erase, resultValues.toAdmin⟩

private abbrev testProfile : Profile := .deterministic (fun _ _ _ _ => false)
private abbrev testHost : HostSemantics Unit := fun _ _ _ _ => False

example : (start 84 7 .unsigned).erase.code =
    [.plain (.intConst .i64 99), .plain (.localGet ⟨0⟩), .plain (.localGet ⟨1⟩),
      .plain (.intBinOp .i32 (.div .unsigned)), .plain .nop] := rfl

example : ConfigOk (start 84 7 .unsigned).erase [.i64, .i32] := (start 84 7 .unsigned).sound

example : ((start 84 7 .unsigned).runFor 4).result? = some resultValues := rfl
example : ((start 84 0 .unsigned).runFor 3).result? = none := rfl
example : ((start 84 0 .unsigned).runFor 3).erase.code = [.plain (.intConst .i64 99), .trap, .plain .nop] := rfl
example : ((start 84 0 .unsigned).runFor 4).result? = some .trap := rfl
example : ((start 0x80000000 (-1) .signed).runFor 4).result? = some .trap := rfl

private def unreachableState : State world twoLocals [.i32] :=
  ⟨⟨.cons 1 (.cons 2 .nil)⟩, .run (.cons (kind := .i64) 4 .nil) (.seq .unreachable .done)⟩

example : (unreachableState.runFor 2).result? = some .trap := rfl

example : Steps testProfile testHost (start 84 7 .unsigned).erase finish :=
  (start 84 7 .unsigned).runFor_sound 4

example : Steps testProfile testHost (start 84 7 .unsigned).erase finish := by
  let first : Config Unit := ⟨world.store, (start 84 7 .unsigned).frame.erase,
    [.plain (.intConst .i64 99), .plain (.intConst .i32 84), .plain (.localGet ⟨1⟩),
      .plain (.intBinOp .i32 (.div .unsigned)), .plain .nop]⟩
  let second : Config Unit := ⟨world.store, first.frame,
    [.plain (.intConst .i64 99), .plain (.intConst .i32 84), .plain (.intConst .i32 7),
      .plain (.intBinOp .i32 (.div .unsigned)), .plain .nop]⟩
  let third : Config Unit := ⟨world.store, first.frame,
    [.plain (.intConst .i64 99), .plain (.intConst .i32 12), .plain .nop]⟩
  have readLeft : Step testProfile testHost (start 84 7 .unsigned).erase first :=
    .ctxtInstrs (vs := [.i64 99])
      (rest := [.plain (.localGet ⟨1⟩), .plain (.intBinOp .i32 (.div .unsigned)), .plain .nop])
      (.variable (.localGet (x := ⟨0⟩) (v := .i32 84) rfl)) (.inl (by simp))
  have readRight : Step testProfile testHost first second :=
    .ctxtInstrs (vs := [.i64 99, .i32 84])
      (rest := [.plain (.intBinOp .i32 (.div .unsigned)), .plain .nop])
      (.variable (.localGet (x := ⟨1⟩) (v := .i32 7) rfl)) (.inl (by simp))
  have divide : Step testProfile testHost second third :=
    .ctxtInstrs (vs := [.i64 99]) (.numeric (.intBinOp rfl)) (.inl (by simp))
  have finishStep : Step testProfile testHost third finish :=
    .ctxtInstrs (vs := [.i64 99, .i32 12]) (.parametric .nop) (.inl (by simp))
  exact (Relation.ReflTransGen.single readLeft).tail readRight |>.tail divide |>.tail finishStep

example (target : Config Unit) :
    ¬ Step testProfile testHost ((start 84 0 .unsigned).runFor 4).erase target :=
  (State.result_sound (profile := testProfile) (state := (start 84 0 .unsigned).runFor 4) rfl).2 target

example : ∃ next, ((start 84 0 .unsigned).runFor 3).step? = some next ∧
    Relation.ReflGen (Step testProfile testHost)
      ⟨world.store, (start 84 0 .unsigned).frame.erase, [.plain (.intConst .i64 99), .trap]⟩ next.erase := by
  have rawBubble : Step testProfile testHost ((start 84 0 .unsigned).runFor 3).erase
      ⟨world.store, (start 84 0 .unsigned).frame.erase, [.plain (.intConst .i64 99), .trap]⟩ :=
    .ctxtInstrs (vs := [.i64 99])
      (.trapInstrs (vs := []) (rest := [.plain .nop]) (.inr (by simp))) (.inl (by simp))
  exact State.step_reflect rawBubble

example : True := by
  fail_if_success have _badStack : Op [] [.i32, .i64] [.i32] := .intBin .add
  fail_if_success have _badLocal : Slot [IntType.i64] .i32 := .here
  trivial

#print axioms State.sound
#print axioms State.step_sound
#print axioms State.run_reflect
#print axioms State.step_reflect
#print axioms State.result_sound
#print axioms State.runFor_sound
