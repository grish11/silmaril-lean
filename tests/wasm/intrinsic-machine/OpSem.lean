module

import Silmaril.Wasm.Execution.Core.Intrinsic.OpSem.Thms

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Execution.Core.Intrinsic
  Silmaril.Wasm.Validation Silmaril.Wasm.Numerics Silmaril.Semantics.Operational

private def world : World Unit {} where
  store := {}
  moduleInst := {}
  storeOk := by constructor <;> simp
  moduleOk := ModuleInstOk.mk (k := 0) (by simp) .nil .nil .nil .nil .nil
    (by simp) .nil (by simp) (by simp) (by simp) (by simp)

private def divide (divisor : BitVec 32) : State world [] [.i32] :=
  ⟨⟨.nil⟩, .run (.cons (kind := .i32) divisor (.cons 84 .nil)) (.seq (.intBin (.div .unsigned)) .done)⟩

private def model : WithUB (Config Unit) Completion := rawSem (fun _ _ _ _ => false) [.i32]

example : model.toOpSem.May (divide 7).erase (.returned (.ok [.i32 12])) :=
  ((divide 7).may_iff (oracle := fun _ _ _ _ => false) _).mpr
    ⟨_, ((divide 7).typedReach_iff _).mpr ⟨1, rfl⟩, .values [.i32 12], rfl, rfl⟩

example : model.toOpSem.TrapReachable (divide 0).erase ∧ model.SafeAt (divide 0).erase :=
  ⟨((divide 0).may_iff (oracle := fun _ _ _ _ => false) _).mpr
    ⟨_, ((divide 0).typedReach_iff _).mpr ⟨1, rfl⟩, .trap, rfl, rfl⟩, (divide 0).raw_safe⟩

private def bad : Config Unit := ⟨world.store, {}, []⟩

private theorem badTyping : ¬ ConfigOk bad [.i32] := by
  rintro ⟨_, ⟨storeOk, frameOk⟩, codeOk⟩
  have typing := (AdminsOk.nil_aux codeOk rfl (FrameOk.toTypeCtx_okReg storeOk frameOk)).2.2.1
  cases typing

example : model.UBReachable bad := ⟨bad, .refl, .inr badTyping⟩

example (outcome : Outcome Completion) : ¬ model.toOpSem.May bad outcome := by
  rintro ⟨target, path, observe⟩
  rcases path.cases_head with rfl | ⟨_, edge, _⟩
  · exact badTyping observe.1
  · exact badTyping edge.1

#print axioms State.may_iff
#print axioms State.raw_safe
#print axioms State.typedReach_iff
#print axioms State.typed_deterministic
