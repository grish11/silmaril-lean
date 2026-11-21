module

import Silmaril.Wasm.Profiles.Thms
import Silmaril.Wasm.Profiles.Binary
import Silmaril.Wasm.Validation.Check.Validate

open Silmaril.Wasm Silmaril.Wasm.Validation
open Silmaril.Wasm.Models (v10 v20 v30)
open Silmaril.Wasm.Profiles (Wasm1 Wasm2 Wasm3 Lime FX Functional Strict HasTyping CheckedModule SomeTypedModule)

example : Profiles.Module Wasm1 = V1.Module := rfl
example : Profiles.Module Wasm2 = V2.Module := rfl
example : Profiles.Module Lime = Lime1.Module := rfl
example : Profiles.Instruction FX = Models.FX.InstrFX := rfl

private def constantFn : Func := ⟨⟨0⟩, [], [.intConst .i32 7]⟩
private def constant : Module :=
  { types := [⟨[⟨true, [], .func ⟨[], [.i32]⟩⟩]⟩], funcs := [constantFn] }

private def saturating : Module :=
  { constant with funcs := [⟨⟨0⟩, [], [.floatConst .f32 0, .convert (.truncSat .f32 .i32 .signed)]⟩] }

private def tailCall : Module :=
  { constant with funcs := [constantFn, ⟨⟨0⟩, [], [.returnCall ⟨0⟩]⟩] }

example : (Profiles.CoreImage.check? v10 saturating).isSome = false := by decide +kernel
example : (Profiles.CoreImage.check? v20 saturating).isSome = true := by decide +kernel
example : (Profiles.CoreImage.check? v20 tailCall).isSome = false := by decide +kernel
example : (Profiles.CoreImage.check? v30 tailCall).isSome = true := by decide +kernel
example : (validate? saturating).isSome = true := by decide +kernel
example : (validate? tailCall).isSome = true := by decide +kernel

private def pairType (mutability : Mutability) : RecType :=
  ⟨[⟨true, [], .struct [⟨mutability, .val .i32⟩, ⟨.const, .val .i32⟩]⟩]⟩

private def projectPair : Module :=
  { types := [pairType .const, ⟨[⟨true, [], .func ⟨[.i32, .i32], [.i32]⟩⟩]⟩]
    funcs := [⟨⟨1⟩, [], [.localGet ⟨0⟩, .localGet ⟨1⟩, .structNew ⟨0⟩, .structGet none ⟨0⟩ ⟨1⟩]⟩]
    exports := [⟨"snd", .func ⟨0⟩⟩] }

private def mutablePair : Module := { projectPair with types := pairType .var :: projectPair.types.drop 1 }

example : (Strict.check? mutablePair).isSome = false := by decide +kernel
example : (validate? mutablePair).isSome = true := by decide +kernel
example : (Profiles.CoreImage.check? Models.functionalMutGC mutablePair).isSome = true := by decide +kernel
example : (Strict.check? { constant with memories := [⟨.i32, ⟨1, none⟩⟩] }).isSome = false := by decide +kernel
example : (Strict.check? { constant with imports := [⟨"host", "f", .func ⟨0⟩⟩] }).isSome = false := by decide +kernel
example : (Strict.check? { constant with tags := [⟨0⟩] }).isSome = false := by decide +kernel
example : (Strict.check? { mutablePair with funcs := [⟨⟨1⟩, [], [.structSet ⟨0⟩ ⟨0⟩]⟩] }).isSome = false :=
  by decide +kernel

private def strictPair : Profiles.Module Strict := (Strict.check? projectPair).get (by decide +kernel)
private def pairInterface : CModuleType := (validate? projectPair).get (by decide +kernel)
private def checkedPair : CheckedModule Strict pairInterface :=
  ⟨strictPair, validate?_sound (by rfl)⟩

example : (Strict.checkedEquiv pairInterface checkedPair).val = projectPair := Strict.checkedEquiv_val checkedPair
example : (Strict.toFunctional strictPair).val = projectPair := Strict.toFunctional_val strictPair
example : (Strict.parts strictPair).toCore = projectPair := Strict.parts_toCore strictPair
example : (Strict.decode? ⟨#[0, 97, 115, 109, 1, 0, 0, 0]⟩).isSome = true := by decide +kernel
example : (Strict.decode? ⟨#[0, 97, 115, 109, 1, 0, 0, 0, 5, 3, 1, 0, 1]⟩).isSome = false := by decide +kernel

private def iface := (validate? constant).get (by decide +kernel)
private def declared : Profiles.DeclaredModule Wasm3 := ⟨(constant, iface), validate?_sound (by rfl)⟩

example : (Profiles.Typing.declaredEquiv declared).1 = iface := Profiles.Typing.declaredEquiv_index declared
example : declared.forget.val = constant := rfl
example (typed : SomeTypedModule Wasm3) : typed.checked.1 = typed.1 := rfl

#print axioms Profiles.Typing.declaredEquiv
#print axioms Profiles.Typing.Declared.forget_eq_iff
#print axioms Profiles.wasm3ModuleEquiv
#print axioms Profiles.wasm3FunctionEquiv
#print axioms Profiles.Strict.checkedEquiv
#print axioms Profiles.Strict.decode?_sound
