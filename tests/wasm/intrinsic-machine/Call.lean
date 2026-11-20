module

import Silmaril.Wasm.Execution.Core.Intrinsic.Call.Thms
import Silmaril.Wasm.Execution.Core.Intrinsic.Thms
import Silmaril.Wasm.Validation.Check.Validate

open Silmaril.Wasm Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Execution.Core.Intrinsic Silmaril.Wasm.Numerics

private def signature : RecType := ⟨[⟨true, [], .func ⟨[.i32, .i32], [.i32]⟩⟩]⟩
private def closed : DefType := (Context.rollGroup {} signature)[0]'(by decide +kernel)
private def params : Ty (.list .val) := .cons .i32 (.cons .i32 .nil)
private def results : Ty (.list .val) := .cons .i32 .nil
private theorem expands : Expand closed (.func params results) := Expand.iff.mpr rfl
private theorem closedOk : TyOk {} closed := TyOk.check_sound (by decide +kernel)

private def divideBody : Code [.i32, .i32, .i64] [] [.i32] :=
  .seq (.localGet (.there (.there .here)) (by decide)) (.seq .drop
    (.seq (.localGet .here (by decide)) (.seq (.localGet (.there .here) (by decide))
      (.seq (.intBin (.div .unsigned)) .done))))

private def rawCode : Func := ⟨⟨0⟩, [.i64], divideBody.erase⟩
private def calleeInst : ModuleInst := { types := [closed] }
private def calleeContext : Context := { types := [closed] }
private def entry : FuncInst Unit := ⟨closed, calleeInst, .wasm rawCode⟩
private def store : Store Unit := { funcs := [entry] }

private theorem calleeOk : ModuleInstOk store calleeInst calleeContext :=
  ModuleInstOk.mk (k := 0) (by simpa [calleeInst] using closedOk) .nil .nil .nil .nil .nil
    (by simp [calleeInst]) .nil (by simp [calleeInst]) (by simp [calleeInst])
    (by simp [calleeInst]) (by simp)

private theorem codeOk : FuncOk calleeContext rawCode closed :=
  .mk rfl expands (.cons (.set (TyOk.check_sound (by decide +kernel)) trivial) .nil) (divideBody.sound rfl)

private theorem storeOk : StoreOk store := by
  constructor <;> simp [store]
  exact .wasm closedOk calleeOk rfl codeOk (Sub.refl _ (k := .def) trivial closed)

private def callerInst : ModuleInst := { funcs := [0] }
private def callerContext : Context := { funcs := [closed] }

private def caller : World Unit callerContext where
  store := store
  moduleInst := callerInst
  storeOk := storeOk
  moduleOk := ModuleInstOk.mk (k := 0) (by simp [callerInst]) .nil .nil
    (.cons (ExternAddrOk.func (fi := entry) rfl) .nil) .nil .nil (by simp [callerInst]) .nil
    (by simp [callerInst]) (by simp [callerInst]) (by simp [callerInst]) (by simp)

private def divide : DirectCall caller [.i32, .i32] [.i32] :=
  ⟨⟨0⟩, 0, entry, [.i64], ⟨0⟩, divideBody, calleeContext, calleeOk, rfl, rfl, expands, rfl⟩

private def args (denominator : BitVec 32) : Values [.i32, .i32] := .cons 84 (.cons denominator .nil)
private def frame : LocalFrame caller [.i64] := ⟨.cons 7 .nil⟩
private abbrev profile : Profile := .deterministic (fun _ _ _ _ => false)
private abbrev host : HostSemantics Unit := fun _ _ _ _ => False

example : (divide.start (args 7)).frame.erase.locals = [some (.i32 84), some (.i32 7), some (.i64 0)] := rfl
example : divide.runFor (args 7) 4 = none := rfl
example : divide.runFor (args 7) 5 = some (some (.cons 12 .nil)) := rfl
example : divide.runFor (args 0) 5 = some none := rfl

example : Steps profile host (divide.source frame (args 7)) ⟨store, frame.erase, [.plain (.intConst .i32 12)]⟩ :=
  divide.run_sound frame (args 7) 5 (answer := some (.cons 12 .nil)) rfl

example : Steps profile host (divide.source frame (args 0)) ⟨store, frame.erase, [.trap]⟩ :=
  divide.run_sound frame (args 0) 5 (answer := none) rfl

#print axioms DirectCall.entry
#print axioms DirectCall.run_sound
