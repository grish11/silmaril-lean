module

import Silmaril.Wasm.Execution.Core.Entry.ClosedFunctional.Thms
import Silmaril.Wasm.Execution.Core.Exec.InstantiateIff
import Silmaril.Wasm.Det.NaN.Litmus.Thms
import Silmaril.Wasm.Validation.Check.Validate

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Execution.Core.Entry
  Silmaril.Wasm.Execution.Core.Entry.ClosedFunctional Silmaril.Wasm.Numerics Silmaril.Wasm.Validation
  Silmaril.Wasm.SingleThreaded Silmaril.Wasm.SingleThreaded.Det Silmaril.Wasm.SingleThreaded.Exec
  Silmaril.Semantics.Operational
open Silmaril.Wasm.Profiles (GCMode Strict)
open Silmaril.Wasm.Profiles.FunctionalISA (Raw)

private def body : Raw .immutable :=
  .blockI32 (.cons (.localGet ⟨0⟩) (.cons (.structNew ⟨0⟩) (.cons (.structGet none ⟨0⟩ ⟨0⟩)
    (.cons (.localGet ⟨1⟩) (.cons .brIf0 (.cons (.intConst 0) (.cons (.bin .i32 (.div .unsigned)) .done))))))) .done

private def pickModule : Module :=
  { types := [⟨[⟨true, [], .struct [⟨.const, .val .i32⟩]⟩]⟩,
      ⟨[⟨true, [], .func ⟨[.i32, .i32], [.i32]⟩⟩]⟩]
    funcs := [⟨⟨1⟩, [], body.erase⟩]
    exports := [⟨"pick", .func ⟨0⟩⟩] }

example : (Strict.check? pickModule).isSome = true := by decide +kernel

private def iface : CModuleType := (validate? pickModule).get (by decide +kernel)
private theorem valid : ModuleOk pickModule iface := validate?_sound rfl

private def empty : Store Empty := {}
private def allocated : Config Empty := (instantiate? evalConst? empty pickModule []).getD ⟨{}, {}, []⟩
private def ready : Ready Empty := ⟨allocated.store, allocated.frame.module⟩
private theorem init : Instantiate (Profile.spec false) divHost empty pickModule [] allocated :=
  (instantiate?_iff ⟨iface.exports, [], valid, .nil⟩).mp rfl

private theorem storeOk : StoreOk ready.store :=
  (Instantiate.ok divHost_ok (by constructor <;> simp [empty]) init).choose_spec.1.1

private theorem closed : Bodies ready.store := by
  intro entry member
  have one : ∃ fn : FuncInst Empty, ready.store.funcs = [fn] ∧ fn.code = .wasm ⟨⟨1⟩, [], body.erase⟩ :=
    ⟨ready.store.funcs[0]'(by decide +kernel), rfl, rfl⟩
  obtain ⟨fn, onlyOne, wasm⟩ := one
  rw [onlyOne, List.mem_singleton] at member
  exact ⟨_, body, member.symm ▸ wasm, rfl⟩

private def args (flag : BitVec 32) : List Val := [.i32 42, .i32 flag]
private def activation (flag : BitVec 32) : Config Empty := invoke ready.store 0 (args flag)
private def input (flag : BitVec 32) : ExportInput Empty := ⟨ready, "pick", args flag⟩
private theorem lookup (flag : BitVec 32) : Game.Accept.exportFunc? (input flag).ready.instance_ (input flag).name = some 0 := rfl

private theorem typed (flag : BitVec 32) : ConfigOk (activation flag) [.i32] := by
  let entry := ready.store.funcs[0]'(by decide +kernel)
  have actual : ready.store.funcs[0]? = some entry := rfl
  have signature : Expand entry.type (.func (.cons .i32 (.cons .i32 .nil)) (.cons .i32 .nil)) := Expand.iff.mpr rfl
  obtain ⟨fn, params, results, found, fnType, ok⟩ := invoke_ok storeOk
    (show InvokeOk ready.store 0 (args flag) from ⟨entry, _, _, actual, signature, .cons (.num _) (.cons (.num _) .nil)⟩)
  cases Option.some.inj (actual.symm.trans found)
  cases Expand.func_eq signature fnType
  exact ok

private def bounded (flag : BitVec 32) := runI neverFail 40 (activation flag)

private theorem finished (flag : BitVec 32) {result : Result}
    (computes : (bounded flag).2 = true) (observed : (bounded flag).1.outcome? = some result) (P : Profile) :
    Finishes P noHost (activation flag) (bounded flag).1 result :=
  (finishes_iff_run (P := P) closed (typed flag)).mpr
    ⟨Config.outcome?_sound observed, 40, Prod.ext rfl computes⟩

example (P : Profile) : Finishes P noHost (activation 1) (bounded 1).1 (.values [.i32 42]) :=
  finished 1 (by decide +kernel) (by decide +kernel) P

example (P : Profile) : Finishes P noHost (activation 0) (bounded 0).1 .trap :=
  finished 0 (by decide +kernel) (by decide +kernel) P

example : (bounded 1).1.store.structs.length = 1 := by decide +kernel
example : (bounded 0).1.store.structs.length = 1 := by decide +kernel

example (P : Profile) : (rawExport P noHost [.i32]).semantics.SafeAt (activation 0) := safe (typed 0)

example (P : Profile) : (rawExport P noHost [.i32]).May (input 0) .trap :=
  (export_may_iff_run (input 0) (lookup 0) closed (typed 0) .trap).mpr
    ⟨(bounded 0).1, .trap, 40, Prod.ext rfl (by decide +kernel),
      Config.outcome?_sound (by decide +kernel), rfl⟩

example (nd : Bool) : (ordinary (Profile.spec nd) noHost).ResultDetAt (activation 1) := result_det closed

open Silmaril.Wasm.Det.NaN.Litmus

example : (Strict.check? nanMod).isSome = true := by decide +kernel
example : (validate? nanMod).isSome = true := by decide +kernel

private def payloadBits : Intrinsic.Completion → Nat
  | .ok [.num ⟨_, bits⟩] => bits.toNat
  | _ => 0

example (nd : Bool) : ¬ (ordinary (Profile.spec nd) noHost).NonTrapDetAt
    (invoke nanStore 0 [f32v nanP, f32v nanP]) := by
  intro det
  have seen {bits : BitVec 32} (allowed : floatBinOpRel .f32 .add nanP nanP bits) :
      (ordinary (Profile.spec nd) noHost).May (invoke nanStore 0 [f32v nanP, f32v nanP])
        (.returned (.ok [f32v bits])) :=
    ⟨_, raw_run rfl allowed, .values [f32v bits], rfl, rfl⟩
  have plus := seen (bits := nanP) (by unfold floatBinOpRel; decide +kernel)
  have minus := seen (bits := nanN) (by unfold floatBinOpRel; decide +kernel)
  have different : nanP.toNat ≠ nanN.toNat := by decide
  exact different (congrArg payloadBits (OpSem.nonTrapDetAt_iff.mp det plus minus))

#print axioms typed_free
#print axioms ClosedFunctional.finishes_unique
#print axioms finishes_iff_run
#print axioms export_may_iff_run
