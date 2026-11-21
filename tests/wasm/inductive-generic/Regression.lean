module

import Silmaril.Wasm.Validation.Generic.Thms
import Silmaril.Wasm.Validation.Intrinsic.ReifyThms
import Silmaril.Wasm.Binaryen.ModuleParts.Thms
import Silmaril.Wasm.Validation.ModuleParts.Thms
import Silmaril.Wasm.SSA.Translate.Thms
import Silmaril.Wasm.SSA.OutOfSSA.Thms
import Silmaril.Wasm.SSA.Bridge.Thms
import Silmaril.Wasm.SSA.Fragment.Thms

open Silmaril Silmaril.Wasm
open Silmaril.Wasm.Binaryen (BExpr BFunc BModule)
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Validation.Inductive (Bounded Path)
open Silmaril.Wasm.SSA

private def firstPath : Path [.i32, .i32] ValType.i32 := .here
private def secondPath : Path [.i32, .i32] ValType.i32 := .there .here

example : firstPath ≠ secondPath := fun same => by cases same
example : Path.lookup ([.i32, .i32] : List ValType) 1 = some ⟨.i32, secondPath⟩ := rfl
example : Path.lookup ([.i32, .i32] : List ValType) 2 = none := rfl

example : (Bounded.equiv (kind := .local) ⟨secondPath, by decide⟩).index.toNat = 1 := rfl
example : (Bounded.equiv (kind := .local)).symm
    (Bounded.equiv ⟨secondPath, by decide⟩) = ⟨secondPath, by decide⟩ :=
  Bounded.equiv.left_inv _

private def signature : RecType := ⟨[⟨true, [], .func ⟨[.i32], [.i32]⟩⟩]⟩

private def header : ModuleSections :=
  { types := [signature], exports := [⟨"entry", .func ⟨0⟩⟩, ⟨"other", .func ⟨1⟩⟩] }

private def calls : Wasm.Module :=
  header.assemble [⟨⟨0⟩, [], [.localGet ⟨0⟩, .call ⟨1⟩]⟩, ⟨⟨0⟩, [], [.localGet ⟨0⟩, .call ⟨1⟩]⟩]

private def typedCalls := Intrinsic.Reify.reify? calls

example : typedCalls.isSome = true := by decide +kernel
example : (Intrinsic.Reify.reify? { calls with funcs := [⟨⟨0⟩, [], [.localGet ⟨0⟩, .call ⟨2⟩]⟩,
    calls.funcs[1]'(by decide)] }).isSome = false :=
  by decide +kernel

private def converted := Generic.Typed.Module.ofIntrinsic (typedCalls.get (by decide +kernel)).typed

example : ((converted.defs.get (.there .here)).typeRef.val.toNat) = 0 := rfl

example : (converted.defs.get (.there .here)).erase.body = [.localGet ⟨0⟩, .call ⟨1⟩] := rfl

example (witness : Intrinsic.Reify.Reified calls) :
    (Generic.Typed.Module.intrinsicEquiv witness.typed).erase = calls := by
  rw [← Generic.Typed.Module.forget_toCore, Generic.Typed.Module.intrinsicEquiv_erase, Wasm.Module.toCore_split]
  exact witness.erase_eq

private def richParts : ModuleParts Wasm.Func :=
  ⟨{ types := [signature, ⟨[⟨true, [], .func ⟨[], []⟩⟩]⟩]
     imports := [⟨"host", "transform", .func ⟨0⟩⟩]
     tags := [⟨1⟩]
     globals := [⟨⟨.const, .i32⟩, [.intConst .i32 7]⟩]
     memories := [⟨.i32, ⟨1, some 1⟩⟩]
     tables := [⟨⟨.i32, ⟨1, some 1⟩, ⟨true, .abstract .func⟩⟩, [.refNull (.abstract .func)]⟩]
     data := [⟨⟨#[42]⟩, .active ⟨0⟩ [.intConst .i32 0]⟩]
     elems := [⟨⟨true, .abstract .func⟩, [[.refFunc ⟨2⟩]], .declarative⟩]
     start := some ⟨3⟩
     exports := [⟨"entry", .func ⟨1⟩⟩, ⟨"alias", .func ⟨1⟩⟩, ⟨"ram", .memory ⟨0⟩⟩] },
    [⟨⟨0⟩, [.i64], [.localGet ⟨0⟩, .call ⟨2⟩]⟩,
     ⟨⟨0⟩, [], [.localGet ⟨0⟩, .call ⟨2⟩]⟩, ⟨⟨1⟩, [], [.nop]⟩]⟩

example : richParts.toCore.split = richParts := richParts.split_toCore
example : richParts.toCore.functionDecls.map (·.locals) = [[.i64], [], []] := rfl
example : richParts.toCore.functionSignature? ⟨0⟩ = some ⟨[.i32], [.i32]⟩ := rfl
example : richParts.toCore.functionSignature? ⟨3⟩ = some ⟨[], []⟩ := rfl
example : richParts.toCore.functionSignature? ⟨4⟩ = none := rfl
example : sectionFuncRefs richParts.sections = [2, 1, 1] := by decide +kernel

private def rich := (Intrinsic.Reify.reify? richParts.toCore).get (by decide +kernel)
private def richGeneric := Generic.Typed.Module.intrinsicEquiv rich.typed

example : richGeneric.header.scope = rich.typed.context :=
  Generic.Typed.Module.intrinsicEquiv_context rich.typed

example : richGeneric.erase.split = richParts := by
  change (richGeneric.forget Generic.Typed.Function.erase).toCore.split = richParts
  rw [ModuleParts.split_toCore]
  exact (Generic.Typed.Module.intrinsicEquiv_erase rich.typed).trans
    ((congrArg Wasm.Module.split rich.erase_eq).trans richParts.split_toCore)

private def fragments : ModuleParts (Generic.Function FragFunc) :=
  ⟨header, [⟨⟨0⟩, [], exampleInc⟩, ⟨⟨0⟩, [], exampleDiv⟩]⟩

private def ssa : ModuleParts (Generic.Function SFunc) := fragments.map (Declaration.Func.mapBody compileFunc)

example : (ssa.defs[0]'(by decide)).body.Run [.i32 41] (.ret (some (.i32 42))) :=
  compileFunc_iff.mpr exampleInc_run

example : (ssa.defs[1]'(by decide)).body.Run [.i32 0] .trap :=
  compileFunc_iff.mpr (FragFunc.eval_sound (fuel := 10) (by decide))

private def outOfSSA (fn : Generic.Function SFunc) : Option BFunc := do
  toBFunc? fn.type (← decompileFunc fn.body)

private def binaryen := ssa.traverse outOfSSA

private def lower (mod : ModuleParts BFunc) : ModuleParts Wasm.Func :=
  mod.map (Declaration.Func.mapBody BExpr.lowerList)

example (mod : ModuleParts BFunc) : (lower mod).toCore = (BModule.ofParts mod).lower :=
  (BModule.lower_ofParts mod).symm

example (f : FragFunc) (run : decompileFunc (ssa.defs[0]'(by decide)).body = some f) :
    f.Run [.i32 41] (.ret (some (.i32 42))) :=
  (decompileFunc_iff run).mpr (compileFunc_iff.mpr exampleInc_run)

example : binaryen.isSome = true := by decide +kernel

example : (binaryen.map (fun mod => (lower mod).toCore.exports.map Wasm.Export.name)) =
    some ["entry", "other"] := rfl

example : (binaryen.map fun mod => (validate? (lower mod).toCore).isSome) = some true :=
  by decide +kernel

example : (binaryen.map fun mod => (Intrinsic.Reify.reify? (lower mod).toCore).isSome) = some false :=
  by decide +kernel

#print axioms Bounded.equiv
#print axioms Module.splitEquiv
#print axioms Declaration.Func.splitEquiv
#print axioms ModuleParts.functionSignature?_mapBody
#print axioms ModuleParts.validate?_sound
#print axioms sectionContext_sections
#print axioms Generic.Typed.Function.intrinsicEquiv
#print axioms Generic.Typed.Module.intrinsicEquiv
#print axioms Generic.Typed.Module.intrinsicEquiv_erase
#print axioms Generic.Typed.Module.intrinsicEquiv_context
#print axioms Generic.Typed.Module.forget_commutes
#print axioms Generic.Typed.Module.lift_erase
#print axioms compileFunc_iff
#print axioms decompileFunc_iff
