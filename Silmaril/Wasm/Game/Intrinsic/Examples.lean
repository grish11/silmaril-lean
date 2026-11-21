module

import Silmaril.Wasm.Game.Intrinsic.Thms
import Silmaril.Wasm.Validation.Intrinsic.Reify
import Silmaril.Wasm.Verify.Check.Thms
import Silmaril.Wasm.SingleThreaded.Exec.InvokeRun

namespace Silmaril.Wasm.Game.Intrinsic.Examples

open Silmaril.Games Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Numerics Silmaril.Wasm.SingleThreaded Silmaril.Wasm.SingleThreaded.Exec
  Silmaril.Wasm.Validation

private def sig : FnType := ⟨[], []⟩

private def returnCode : Func := ⟨⟨0⟩, [], [.nop]⟩
private def trapCode : Func :=
  ⟨⟨0⟩, [], [.intConst .i32 1, .intConst .i32 0, .intBinOp .i32 (.div .unsigned), .drop]⟩
private def callCode : Func := ⟨⟨0⟩, [], [.call ⟨0⟩]⟩

private def raw : Module where
  types := [⟨[⟨true, [], .func ⟨[], []⟩⟩]⟩]
  imports := [⟨"env", "callback", .func ⟨0⟩⟩]
  funcs := [returnCode, trapCode, callCode]
  exports := [⟨"return", .func ⟨1⟩⟩, ⟨"trap", .func ⟨2⟩⟩, ⟨"call", .func ⟨3⟩⟩]

private def program : Validation.Intrinsic.Reify.Reified raw :=
  (Validation.Intrinsic.Reify.reify? raw).get (by decide +kernel)

private def checked : CModuleType × ScalarInstance := (Verify.instance? raw).get (by decide +kernel)
private def instance_ : ScalarInstance := checked.2

private def registered : Registered program.typed where
  instance_ := instance_
  ready := by
    rw [program.erase_eq]
    exact Verify.isInstance_of_instance? (by rfl)
  exports := .cons ⟨_, rfl, rfl⟩ (.cons ⟨_, rfl, rfl⟩ (.cons ⟨_, rfl, rfl⟩ .nil))

private def defType : DefType := program.typed.definedFuncs[0]'(by decide +kernel)

private def typed (code : Func) (valid : (Validation.Intrinsic.Reify.reifyFunction? program.typed.context
    defType code).isSome) := (Validation.Intrinsic.Reify.reifyFunction? program.typed.context defType code).get valid

private def implementation : ModuleInst :=
  (instance_.store.funcs[1]?.map FuncInst.module).getD {}

private def returnEntry : Entry (typed returnCode (by decide +kernel)).val instance_ instance_.store sig :=
  ⟨⟨0, by decide +kernel⟩, rfl, rfl, 1, rfl, implementation, by rw [(typed returnCode _).property]; rfl⟩

private def trapEntry : Entry (typed trapCode (by decide +kernel)).val instance_ instance_.store sig :=
  ⟨⟨1, by decide +kernel⟩, rfl, rfl, 2, rfl, implementation, by rw [(typed trapCode _).property]; rfl⟩

private def callEntry : Entry (typed callCode (by decide +kernel)).val instance_ instance_.store sig :=
  ⟨⟨2, by decide +kernel⟩, rfl, rfl, 3, rfl, implementation, by rw [(typed callCode _).property]; rfl⟩

private def args : Typed sig.params := ⟨[], .nil⟩
private def silent : Env instance_.E := Env.silent _
private theorem silentThrows : ThrowsBelow silent instance_.store.exns.length := fun _ _ impossible =>
  nomatch impossible

private def final {code : Validation.Intrinsic.Function program.typed.context defType}
    (entry : Entry code instance_ instance_.store sig) : Config Nat :=
  (runI neverFail 12 (invoke instance_.store entry.address args.val)).1

private theorem reaches {code : Validation.Intrinsic.Function program.typed.context defType}
    (entry : Entry code instance_ instance_.store sig) :
    Steps (profile neverFail) Det.noHost (invoke instance_.store entry.address args.val) (final entry) := by
  obtain ⟨_, _, _, _, _, valid⟩ := invoke_ok registered.ready.ok.storeOk (entry.invokeOk args)
  exact runI_steps_typed (o := neverFail) 12 valid

example : Behaviour.returns [] ∈ dcompositeObs (silent.dstrategy.comp (registered.denote (profile neverFail)))
    (returnEntry.question args) := by
  change Behaviour.returns [] ∈ returnEntry.denote (profile neverFail) silent args
  rw [returnEntry.adequacy registered.ready.ok silent silentThrows]
  exact returns_mem_behavioursOf (EndToEnd.Steps.of_noHost _ (reaches returnEntry))
    (Config.outcome?_sound (show (final returnEntry).outcome? = some (.values []) from by decide +kernel))

example : Behaviour.traps ∈ trapEntry.denote (profile neverFail) silent args := by
  rw [trapEntry.adequacy registered.ready.ok silent silentThrows]
  exact traps_mem_behavioursOf (EndToEnd.Steps.of_noHost _ (reaches trapEntry))
    (Config.outcome?_sound (show (final trapEntry).outcome? = some .trap from by decide +kernel))

private def importQuestion : instance_.E.Op := ⟨⟨0, by decide +kernel⟩, args⟩

private theorem decodesImport : instance_.importOp? 0 [] = some importQuestion := by
  unfold ScalarInstance.importOp? ifaceOp?
  split
  · split
    · rfl
    · rename_i bound invalid
      exact False.elim (invalid (show List.Forall₂ ScalarType.HasVal [] [] from .nil))
  · rename_i invalid
    exact False.elim (invalid (by decide +kernel))

private def decoded := decompose? (final callEntry).store (final callEntry).code
private def callout := decoded.get (by decide +kernel)

example : [.inr (.ask (callEntry.question args)), .inl (.ask importQuestion)] ∈
    instance_.strategy (profile neverFail) instance_.store := by
  apply (callEntry.first_import_iff args importQuestion).mpr
  have host : callout.2.2.1 = 0 := by decide +kernel
  have values : callout.2.2.2 = [] := by decide +kernel
  refine ⟨final callEntry, reaches callEntry, callout.1, callout.2.1, callout.2.2.1, callout.2.2.2, ?_, ?_⟩
  · exact (Option.some_get (by decide +kernel : decoded.isSome)).symm
  · rw [host, values]
    exact decodesImport

end Silmaril.Wasm.Game.Intrinsic.Examples
