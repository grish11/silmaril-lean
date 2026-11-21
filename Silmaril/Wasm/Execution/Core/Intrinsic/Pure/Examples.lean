module

import Silmaril.Wasm.Execution.Core.Intrinsic.Pure.Thms
import Silmaril.Wasm.Execution.Core.Intrinsic.Thms
import Silmaril.Wasm.Profiles.Thms
import Silmaril.Wasm.Validation.Check.Validate

namespace Silmaril.Wasm.Execution.Core.Intrinsic.Pure.Examples

open Silmaril.Wasm Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded

private def signature : RecType := ⟨[⟨true, [], .func ⟨[.i32, .i32], [.i32]⟩⟩]⟩
private def closed : DefType := (Context.rollGroup {} signature)[0]'(by decide +kernel)
private theorem closedOk : TyOk {} closed := TyOk.check_sound (by decide +kernel)
private theorem expands : Expand closed (.func (.cons .i32 (.cons .i32 .nil)) (.cons .i32 .nil)) :=
  Expand.iff.mpr rfl

private abbrev Body := Code [.i32, .i32] [] [.i32]

private def sub : Body := .seq (.localGet .here (by decide))
  (.seq (.localGet (.there .here) (by decide)) (.seq (.intBin .sub) .done))

private def nopSub : Body := .seq .nop sub

private def divide : Body := .seq (.localGet .here (by decide))
  (.seq (.localGet (.there .here) (by decide)) (.seq (.intBin (.div .unsigned)) .done))

private def raw (body : Body) : Func := ⟨⟨0⟩, [], body.erase⟩

private def closedModule : Module :=
  { types := [signature], funcs := [raw sub, raw divide],
    exports := [⟨"sub", .func ⟨0⟩⟩, ⟨"divide", .func ⟨1⟩⟩] }

example : (Profiles.Strict.check? closedModule).isSome := by decide +kernel
example : (validate? closedModule).isSome := by decide +kernel

private def callee : ModuleInst := { types := [closed] }
private def calleeContext : Context := { types := [closed] }
private def entry (body : Body) : FuncInst Nat := ⟨closed, callee, .wasm (raw body)⟩
private def store (body : Body) : Store Nat := { funcs := [entry body] }

private theorem calleeOk (body : Body) : ModuleInstOk (store body) callee calleeContext :=
  ModuleInstOk.mk (k := 0) (by simpa [callee] using closedOk) .nil .nil .nil .nil .nil
    (by simp [callee]) .nil (by simp [callee]) (by simp [callee]) (by simp [callee]) (by simp)

private theorem storeOk (body : Body) : StoreOk (store body) := by
  constructor <;> try (solve | simp [store])
  intro fn membership
  simp only [store, List.mem_singleton] at membership
  subst fn
  have codeOk : FuncOk calleeContext (raw body) closed := .mk rfl expands .nil (body.sound rfl)
  exact .wasm closedOk (calleeOk body) rfl codeOk (Sub.refl _ (k := .def) trivial closed)

private def caller (body : Body) : World Nat { funcs := [closed] } where
  store := store body
  moduleInst := { funcs := [0] }
  storeOk := storeOk body
  moduleOk := ModuleInstOk.mk (k := 0) (by simp) .nil .nil
    (.cons (ExternAddrOk.func (fi := entry body) rfl) .nil) .nil .nil
    (by simp) .nil (by simp) (by simp) (by simp) (by simp)

private def link (body : Body) : Linked (parameters := [.i32, .i32]) (declared := []) body where
  context := { funcs := [closed] }
  world := caller body
  call := ⟨⟨0⟩, 0, ⟨closed, callee, .wasm (raw body)⟩, [], ⟨0⟩, body,
    calleeContext, calleeOk body, rfl, rfl, expands, rfl⟩
  locals := rfl
  code := rfl

private def args (lhs rhs : BitVec 32) : Values [.i32, .i32] := .cons lhs (.cons rhs .nil)

example : PostEquivalent (parameters := [.i32, .i32]) (declared := []) sub nopSub :=
  (postEquivalent_iff (link sub) (link nopSub) neverFail).mpr (fun _ => rfl)

example : ¬ PostEquivalent (parameters := [.i32, .i32]) (declared := []) sub divide := by
  intro equal
  have same := (postEquivalent_iff (link sub) (link divide) neverFail).mp equal (args 9 0)
  change some _ = none at same
  cases same

example : behaviours (profile neverFail) Det.noHost (store sub) 0 (args 9 2).erase =
    {Behaviour.returns [.num ⟨.int .i32, 7⟩]} := (link sub).observation (args 9 2) neverFail

example : behaviours (profile neverFail) Det.noHost (store divide) 0 (args 9 0).erase =
    {Behaviour.traps} := (link divide).observation (args 9 0) neverFail

private def suffix : Code [.i32, .i32] [.i32] [.i32] :=
  .seq (.localGet .here (by decide)) (.seq (.intBin .add) .done)

example : behaviours (profile neverFail) Det.noHost (store (sub.append suffix)) 0 (args 9 0).erase ≠
    behaviours (profile neverFail) Det.noHost (store (divide.append suffix)) 0 (args 9 0).erase := by
  change behaviours (profile neverFail) Det.noHost (link (sub.append suffix)).world.store
    (link (sub.append suffix)).call.address (args 9 0).erase ≠
    behaviours (profile neverFail) Det.noHost (link (divide.append suffix)).world.store
    (link (divide.append suffix)).call.address (args 9 0).erase
  rw [(link (sub.append suffix)).observation (args 9 0) neverFail,
    (link (divide.append suffix)).observation (args 9 0) neverFail]
  intro equal
  have result := Set.singleton_eq_singleton_iff.mp equal
  cases result

end Silmaril.Wasm.Execution.Core.Intrinsic.Pure.Examples
