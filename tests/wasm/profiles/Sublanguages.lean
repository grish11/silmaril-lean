module

import Silmaril.Wasm.Sublanguages.Link.Thms
import Silmaril.Wasm.V1.Validation.Examples
import Silmaril.Wasm.Verify.Kernel.Defs

open Silmaril.Wasm Silmaril.Wasm.Sublanguages
open Silmaril.Wasm.V1.Validation.Examples (idx0 idx1)

private def signature : V1.FuncType := ⟨[], [.i32]⟩

private def constFn : V1.Func := ⟨idx0, [], [.intConst .i32 7]⟩

private def runFn (type : TypeIdx) : V1.Func :=
  ⟨type, [], [.call idx0, .intConst .i32 1, .intBinOp .i32 .add]⟩

private def provider : wasm1.Module := {
  types := [signature]
  funcs := [constFn]
  exports := [⟨"const", .func idx0⟩] }

private def consumer : wasm1.Module := {
  types := [signature]
  funcs := [runFn idx0]
  imports := [⟨"p", "const", .func idx0⟩]
  exports := [⟨"run", .func idx1⟩] }

private def linked : wasm1.Module := {
  types := [signature, signature]
  funcs := [constFn, runFn idx1]
  exports := [⟨"const", .func idx0⟩, ⟨"run", .func idx1⟩] }

private theorem core_link : Link.GC.link? "p" (wasm1.toModule provider) (wasm1.toModule consumer) =
    some (wasm1.toModule linked) := by kernel_rfl

private theorem encodable : ∃ bytes, Binaryen.Exe.encodeModule? (wasm1.toModule linked) = .ok bytes := by
  have ok : (Binaryen.Exe.encodeModule? (wasm1.toModule linked)).isOk = true := by kernel_rfl
  cases encoded : Binaryen.Exe.encodeModule? (wasm1.toModule linked) with
  | error _ => rw [encoded] at ok; cases ok
  | ok bytes => exact ⟨bytes, rfl⟩

private theorem linked_ok : wasm1Readback.link? "p" provider consumer = some linked := by
  obtain ⟨_, bytes⟩ := encodable
  exact Readback.link?_complete core_link bytes

example : wasm1Readback.link? "wrong" provider consumer = none := rfl

example : wasm1.toModule linked ∈ lime.admittedImage Models.v20 := by
  have admitted : wasm1.Admits Models.v10 linked := by
    change Models.Module.inFeatB Models.v10 (wasm1.toModule linked) = true
    kernel_rfl
  exact Language.admittedImage_mono wasm1IntoLime Models.v10_le_v20 ⟨linked, admitted, rfl⟩

private def legacyElem : V2.Module := {
  Profiles.Injections.wasm1ToWasm2 linked with
  elems := [⟨.funcref, [[.refFunc idx0]], .declare⟩] }

private def retagged : core.Module :=
  (Profiles.Injections.wasm2ToWasm3Binary.run legacyElem).getD {}

example : (wasm2Readback.candidate retagged).isSome = true := by kernel_rfl

example : wasm2Readback.exact? retagged = none := by kernel_rfl

example : limeReadback.link? "p" (wasm1IntoLime.mod provider) (wasm1IntoLime.mod consumer) =
    some (wasm1IntoLime.mod linked) := by
  obtain ⟨_, bytes⟩ := encodable
  exact Readback.link?_natural wasm1IntoLime limeReadback linked_ok bytes

example : Nonempty (Link.GC.Recipe.Assembly "p" (wasm1.toModule provider) (wasm1.toModule consumer)
    (wasm1.toModule linked)) := Readback.link?_recipe linked_ok

example : ∃ iface, ∃ typed : Profiles.TypedModule Profiles.Wasm3 iface,
    Profiles.HasIntrinsic.eraseModule typed = wasm1.toModule linked := Readback.link?_intrinsic linked_ok

open V1.Validation in
private theorem linked_native_valid : ModuleValid linked where
  types := by simp [linked, FuncTypeValid, signature]
  imports := by simp [linked]
  functions := by
    intro fn member
    simp only [linked, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact ⟨signature, rfl, Nat.le_refl 1, .singleton (.intConst .i32 7)⟩
    · refine ⟨signature, rfl, Nat.le_refl 1, .cons (.call idx0 (ft := signature) rfl) ?_⟩
      exact .cons (.frame [.i32] (.intConst .i32 1)) (.singleton (.intBinOp .i32 .add))
  tables := by simp [linked]
  memories := by simp [linked]
  globals := by simp [linked]
  elements := by simp [linked]
  data := by simp [linked]
  start := by simp [StartValid, linked]
  exports := by
    intro exp member
    simp only [linked, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact ⟨.func signature, rfl⟩
  uniqueExports := by decide
  singleTable := by decide
  singleMemory := by decide

#print axioms Inclusion.comp_intoCore
#print axioms Language.admittedImage_mono
#print axioms wasm2_checked_image
#print axioms Readback.link?_square
#print axioms Readback.link?_complete
#print axioms Readback.link?_recipe
#print axioms Readback.link?_intrinsic
#print axioms Readback.link?_natural
#print axioms linked_ok
#print axioms linked_native_valid
