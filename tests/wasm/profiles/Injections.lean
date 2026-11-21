module

import Silmaril.Wasm.Profiles.Injections.Thms
import Silmaril.Wasm.V1.Validation.Examples

open Silmaril.Wasm Silmaril.Wasm.Profiles Silmaril.Wasm.Profiles.Injections
open Silmaril.Wasm.V1.Validation.Examples (addModule addModule_valid)

private def checkedAdd : CheckedModule Wasm1 () := ⟨addModule, addModule_valid⟩

private theorem addOffsets : Lime1.Validation.Module.SegmentOffsetsImported (wasm1ToLime addModule) := by
  have noElems : (wasm1ToLime addModule).elems = [] := rfl
  have noData : (wasm1ToLime addModule).data = [] := rfl
  simp [Lime1.Validation.Module.SegmentOffsetsImported, noElems, noData]

example : ∃ ports : HasTyping.Interface Wasm2, ∃ checked : CheckedModule Wasm2 ports,
    checked.val = wasm1ToWasm2 addModule ∧ (checkedWasm2ToWasm3 checked).val = wasm1ToWasm3 addModule := by
  obtain ⟨ports, valid⟩ := (validWasm1ToWasm2 checkedAdd addOffsets).property
  exact ⟨ports, ⟨_, valid⟩, rfl, checkedWasm1_via_wasm2 checkedAdd valid⟩

example : wasm2ToFX.run (wasm1ToWasm2 addModule) = some (wasm1ToWasm3 addModule) := by
  exact congrArg (fun arrow : ModuleInjection Wasm1 FX => arrow.run addModule) wasm1_fx_via_wasm2

example : (wasm3ToFXUnbound Nat (wasm1ToWasm3 addModule)).bindings 7 = none := rfl

private def badWrap (target : NumType) : Profiles.Module Wasm2 :=
  { funcs := [⟨⟨0⟩, [], [.cvtOp target (.int .i32) .wrap]⟩] }

example : wasm2ToWasm3.run (badWrap (.int .i64)) = none ∧
    wasm2ToWasm3.run (badWrap (.float .f64)) = none := ⟨rfl, rfl⟩

example : badWrap (.int .i64) ≠ badWrap (.float .f64) := by
  intro eq
  cases congrArg (fun mod : V2.Module => mod.funcs.head?.map (·.body)) eq

private def legacyElement : Profiles.Module Wasm2 :=
  { wasm1ToWasm2 addModule with elems := [⟨.funcref, [[.refFunc ⟨0⟩]], .declare⟩] }

example : (wasm2ToWasm3.run legacyElement).bind (fun mod => mod.elems.head?.map (·.type)) =
    some V2.coreFuncref := rfl

example : (wasm2ToWasm3Binary.run legacyElement).bind (fun mod => mod.elems.head?.map (·.type)) =
    some V2.coreRefFunc := rfl

#print axioms PartialInjection.comp_assoc
#print axioms Injections.wasm1_fx_via_wasm2
#print axioms Injections.wasm2Function_defined
#print axioms Injections.checkedWasm2ToWasm3Embedding
#print axioms Injections.checkedWasm2ToWasm3_lift
#print axioms Injections.checkedWasm1_via_wasm2
