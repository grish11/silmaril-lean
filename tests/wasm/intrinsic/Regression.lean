module

public import Example
public import RawExample

namespace WasmIntrinsicRegression

open Silmaril.Wasm.Validation WasmIntrinsicExample
open WasmRawExample (raw)

wasm_prove_erasure erased : intrinsic => raw

theorem rawTyped : ModuleOk raw interface := erased ▸ intrinsic.sound

example : (validate? raw).isSome = true := by decide +kernel

example : (Intrinsic.Module.equiv interface) ((Intrinsic.Module.equiv interface).symm ⟨raw, rawTyped⟩) =
    ⟨raw, rawTyped⟩ := (Intrinsic.Module.equiv interface).apply_symm_apply _

example : ∃ lifted : Intrinsic.Module interface, lifted.erase = raw := Intrinsic.Module.lift_erase rawTyped

private def jump : Intrinsic.Step labelCtx (.plain [.i32] [.i64]) :=
  .br (stackPrefix := []) ⟨zero, rfl⟩ (InstrTypeOk.check_sound (by decide +kernel))

private def finish : Intrinsic.Step bodyCtx (.plain [.i32] [.i64]) :=
  .return_ (stackPrefix := []) rfl (InstrTypeOk.check_sound (by decide +kernel))

private def trap : Intrinsic.Step bodyCtx (.plain [.i64] [.i32]) :=
  .unreachable (InstrTypeOk.check_sound (by decide +kernel))

example : InstrOk labelCtx (.br zero) (.plain [.i32] [.i64]) := jump.sound
example : InstrOk bodyCtx .return_ (.plain [.i32] [.i64]) := finish.sound
example : InstrOk bodyCtx .unreachable (.plain [.i64] [.i32]) := trap.sound

example : True := by
  fail_if_success
    let _bad : Intrinsic.Step {} (.plain [] [.i32]) := .localGet ⟨zero, rfl⟩
  trivial

private def explicitNil : Intrinsic.Body bodyCtx (.plain [] []) := .nil
private def framedNil : Intrinsic.Body bodyCtx (.plain [] []) :=
  .frame (stackPrefix := []) .nil (by simp [ResultOk])

private def isFrame {context sig} : Intrinsic.Body context sig → Bool
  | .frame .. => true
  | _ => false

example : explicitNil.erase = framedNil.erase := rfl
example : explicitNil ≠ framedNil := by
  intro eq
  have impossible : false = true := congrArg isFrame eq
  cases impossible

#print axioms erased
#print axioms rawTyped
#print axioms Intrinsic.Function.equiv
#print axioms Intrinsic.Module.equiv

end WasmIntrinsicRegression
