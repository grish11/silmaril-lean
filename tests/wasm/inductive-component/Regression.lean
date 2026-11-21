module

import Silmaril.Wasm.Component.IntrinsicWiring.Thms
import Silmaril.Wasm.Validation.Intrinsic.ReifyThms
import Silmaril.Wasm.ModuleParts.Thms

open Silmaril Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Validation
open Silmaril.Wasm.Component.IntrinsicWiring
open Silmaril.Wasm.Component.Types

private def signature : Wasm.RecType := ⟨[⟨true, [], .func ⟨[], [.i32]⟩⟩]⟩

private def providerParts : ModuleParts Wasm.Func :=
  ⟨{ types := [signature], exports := [⟨"get", .func ⟨0⟩⟩] }, [⟨⟨0⟩, [], [.intConst .i32 42]⟩]⟩

private def consumerParts : ModuleParts Wasm.Func :=
  ⟨{ types := [signature], imports := [⟨"env", "get", .func ⟨0⟩⟩], exports := [⟨"run", .func ⟨1⟩⟩] },
    [⟨⟨0⟩, [], [.call ⟨0⟩]⟩]⟩

private def provider := providerParts.toCore
private def consumer := consumerParts.toCore

private abbrev Payload := Σ raw : Wasm.Module, Wasm.Validation.Intrinsic.Reify.Reified raw

private def providerPayload : Payload :=
  ⟨provider, (Wasm.Validation.Intrinsic.Reify.reify? provider).get (by decide +kernel)⟩

private def consumerPayload : Payload :=
  ⟨consumer, (Wasm.Validation.Intrinsic.Reify.reify? consumer).get (by decide +kernel)⟩

private def bodyErase (payload : Payload) : Wasm.Module := payload.2.typed.erase

private def interface? (payload : Payload) : Option (CoreModuleType Core3Extern) :=
  core3ModuleType? (bodyErase payload)

private abbrev State := DefState Core3Extern
private abbrev From (before : State) := Σ after, Program .p2 core3Profile interface? before after

private def emitCore {before : State} (payload : Payload) : Option (From before) :=
  match checked : interface? payload with
  | none => none
  | some type => some ⟨_, .cons (.core payload type checked) .nil⟩

private def emit {before : State} (cmd : Command) : Option (From before) :=
  match checked : cmd.check .p2 core3Profile before with
  | .error _ => none
  | .ok after => some ⟨after, .cons (.command cmd checked) .nil⟩

private def append {before : State} (part : Option (From before)) (next : ∀ state, Option (From state)) :
    Option (From before) := do
  let ⟨state, left⟩ ← part
  let ⟨after, right⟩ ← next state
  pure ⟨after, left.then right⟩

private def first : Option (From initState) :=
  append (emitCore providerPayload) fun _ => emit (.instance_ (.instantiate 0 []))

private def connect (before : State) (moduleName : String) (instanceIndex : Nat) : Option (From before) :=
  append (emitCore consumerPayload) fun _ => emit (.instance_ (.instantiate 1 [(moduleName, instanceIndex)]))

private def connected := append first fun state => connect state "env" 0

private def finish (before : State) : Option (From before) :=
  append (emit (.alias (.coreExport 1 "run" .func))) fun _ =>
  append (emit (.funcType { params := [], result := some (.prim .u32) })) fun _ =>
  append (emit (.canon (.lift 0 [] 0))) fun _ =>
  emit (.export_ { name := "run" } ⟨.func, 0⟩)

private def linked := (append connected finish).get (by decide +kernel)

example : (append first fun state => connect state "wrong" 0).isSome = false := by decide +kernel
example : (append first fun state => connect state "env" 1).isSome = false := by decide +kernel

private def erased := (linked.2.map (targets := core3ModuleType?) bodyErase (fun checked => checked)).erase

example : erased = Syntax.Component.map bodyErase linked.2.erase :=
  linked.2.erase_map bodyErase (fun checked => checked)

example : bodyErase providerPayload = provider := providerPayload.2.erase_eq
example : bodyErase consumerPayload = consumer := consumerPayload.2.erase_eq

example : (bodyErase consumerPayload).split = consumerParts :=
  (congrArg Wasm.Module.split consumerPayload.2.erase_eq).trans consumerParts.split_toCore

example : erased.coreModules.map (fun mod => mod.exports.map Wasm.Export.name) = [["get"], ["run"]] :=
  by decide +kernel

example : ValidComponentCore3 .p2 erased (componentTypeOfDefs linked.1.ctx) :=
  checkCore3?_sound ((linked.2.map bodyErase (fun checked => checked)).check_closed (by decide +kernel))

example : ((checkCore3? .p2 erased).toOption.map fun typ => typ.exports.map Prod.fst) = some ["run"] :=
  by decide +kernel

#print axioms Program.erase_then
#print axioms Program.erase_map
#print axioms Program.map_then
#print axioms Program.sound
#print axioms checkCore3?_sound
