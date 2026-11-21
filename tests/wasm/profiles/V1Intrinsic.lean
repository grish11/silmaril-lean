module

import Silmaril.Wasm.V1.Intrinsic.Scalar.Thms
import Silmaril.Wasm.Validation.Check.Validate

open Silmaril.Wasm
open Silmaril.Wasm.V1.Intrinsic.Scalar

private def sig : V1.FuncType := ⟨[.i32], [.i32]⟩

private def arithmetic : ClosedModule sig where
  exportName := "sumTimesInput"
  fn := {
    resolved := rfl
    singleResult := Nat.le_refl 1
    locals := [.i32]
    body := .step [] (.localGet ⟨0⟩ rfl) <|
      .step [.i32] (.intConst .i32 7) <|
      .step [] (.intBinOp .i32 .add) <|
      .step [] (.localSet ⟨1⟩ rfl) <|
      .step [] (.localGet ⟨1⟩ rfl) <|
      .step [.i32] (.localGet ⟨0⟩ rfl) <|
      .step [] (.intBinOp .i32 .mul) (.nil [.i32]) }

example : arithmetic.erase.funcs = [⟨⟨0⟩, [.i32],
    [.localGet ⟨0⟩, .intConst .i32 7, .intBinOp .i32 .add, .localSet ⟨1⟩,
     .localGet ⟨1⟩, .localGet ⟨0⟩, .intBinOp .i32 .mul]⟩] := rfl
example : arithmetic.toCore.exports = [⟨"sumTimesInput", .func ⟨0⟩⟩] := rfl
example : V1.Validation.ModuleValid arithmetic.erase := arithmetic.sound
example : (Validation.validate? arithmetic.toCore).isSome = true := by decide +kernel
example : V1.Module.ofCore? arithmetic.toCore = some arithmetic.erase := arithmetic.ofCore?_toCore
example : Lime1.Validation.ModuleValid arithmetic.erase.toLime := arithmetic.lime_sound
example : arithmetic.erase.toLime.toCore = arithmetic.toCore := arithmetic.lime_toCore_eq

private def selfCall : ClosedModule sig where
  exportName := "self"
  fn := {
    resolved := rfl
    singleResult := Nat.le_refl 1
    locals := []
    body := .step [] (.localGet ⟨0⟩ rfl) <|
      .step [] (.call ⟨0⟩ (sig := sig) rfl) (.nil [.i32]) }

example : selfCall.toCore.funcs = [⟨⟨0⟩, [], [.localGet ⟨0⟩, .call ⟨0⟩]⟩] := rfl
example : Validation.ModuleValid selfCall.toCore := selfCall.core_sound
example : (Validation.validate? selfCall.toCore).isSome = true := by decide +kernel

example : True := by
  fail_if_success
    have bad : V1.Intrinsic.Scalar.Instr {} [.i32, .i64] [.i32] := .intBinOp .i32 .add
  fail_if_success
    have bad := V1.Intrinsic.Scalar.Instr.localGet (ctx := { locals := [.i32] }) ⟨1⟩ (ty := .i32) rfl
  fail_if_success
    have bad := V1.Intrinsic.Scalar.Instr.call (ctx := closedContext sig) ⟨1⟩ (sig := sig) rfl
  trivial
example : IsEmpty (ClosedModule ⟨[], [.i32, .i64]⟩) :=
  ⟨fun term => Nat.not_succ_le_self 1 term.fn.singleResult⟩

#print axioms Instr.sound
#print axioms Body.sound
#print axioms Body.toCore_eq
#print axioms Function.sound
#print axioms Function.toCore_eq
#print axioms ClosedModule.sound
#print axioms ClosedModule.toCore_eq
#print axioms ClosedModule.core_sound
#print axioms ClosedModule.ofCore?_toCore
#print axioms ClosedModule.lime_sound
#print axioms ClosedModule.lime_toCore_eq
