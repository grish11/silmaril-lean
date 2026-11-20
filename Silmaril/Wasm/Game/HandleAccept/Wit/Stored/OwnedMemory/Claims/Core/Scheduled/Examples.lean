module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Defs
import Silmaril.Wasm.Component.Reference.Machine.Soundness.Thms
meta import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Defs
meta import Silmaril.Wasm.Component.Reference.Machine.Exec.Defs

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Examples

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.AsyncRef Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Execution.Core

public abbrev grow := SingleThreaded.neverFail
public abbrev engine := core3 grow
@[expose] public def resource : RtId := ⟨0⟩
@[expose] public def element : Option (WIT.ClosedType RtId) := some (.prim .u16)

@[expose] public def signature : Signature :=
  ⟨Option Bool, (fun
    | some false => .tuple [.own resource, .own resource, .stream element]
    | some true => .option (.borrow resource)
    | none => .stream element), fun _ => .fixed 0⟩

private def contract : Endpoints.Core.Contract signature :=
  ⟨0, ("host", "accept-node"), (fun
    | 0 => some (some false)
    | 1 => some (some true)
    | 2 => some none
    | _ => none), {}, ⟨0⟩⟩

private def transfers : List (Binding signature) :=
  [⟨"give-owner", ⟨0⟩, .giveOwner resource⟩, ⟨"drop-owner", ⟨0⟩, .dropOwner resource⟩,
    ⟨"give-reader", ⟨0⟩, .giveEndpoint .stream element⟩,
    ⟨"wrong-owner", ⟨0⟩, .dropOwner ⟨1⟩⟩]

private def ready : HostReady (HostState signature) := fun _ _ => false
private def dispatch (inst : ModuleInst) : Canon.Call engine → Session grow signature (Ret engine) :=
  specDispatch ready (host (Binding.accept contract inst 0 :: transfers))

private def wordFn (params results : Nat) : V1.FuncType :=
  ⟨List.replicate params (.int .i32), List.replicate results (.int .i32)⟩

private def imports : List (String × V1.FuncType × CanonHost engine) :=
  let bound : Binding signature := ⟨"accept-node", ⟨0⟩, .accept contract none⟩
  ((bound :: transfers).map fun imp => (imp.name, imp.type, .embedder imp.name imp.type)) ++
    [("new-own", wordFn 1 1, .builtin (.resourceNew resource .i32) ⟨0⟩),
      ("new-stream", ⟨[], [.int .i64]⟩, .builtin (.streamNew element) ⟨0⟩),
      ("rep", wordFn 1 1, .builtin (.resourceRep resource .i32) ⟨0⟩),
      ("close-reader", wordFn 1 0, .builtin (.streamDropReadable element) ⟨0⟩),
      ("close-writer", wordFn 1 0, .builtin (.streamDropWritable element) ⟨0⟩)]

private def idx {kind : IndexKind} (index : Nat) : Idx kind := ⟨Fin.ofNat _ index⟩
private def word (value : Nat) : Instr := .intConst .i32 (BitVec.ofNat 32 value)
private def storeWord (ptr value : Nat) : List Instr :=
  [word ptr, word value, .intStore .i32 none ⟨0⟩ ⟨0, 0⟩]

private def instantiate (trapping : Bool) : Option (Store (CanonHost engine) × ModuleInst) := do
  let (store, addrs) := imports.foldl (fun (current, addresses) (_, type, code) =>
    let (next, addr) := SingleThreaded.allocHost current type code
    (next, addresses ++ [ExternAddr.func addr])) ({}, [])
  let names := imports.map (·.1)
  let wrapper := fun (index : Nat) =>
    let params := (imports[index]?.map (·.2.1.params.length)).getD 0
    let setup := if index == 0 then storeWord 32 1 ++ storeWord 36 2 ++ storeWord 40 3 ++ storeWord 48 2 else []
    (⟨idx index, [], setup ++ (List.range params).map (fun param => .localGet (idx param)) ++
      [.call (idx index)]⟩ : Func)
  let destructor := [word 16, .localGet (idx 0), .intStore .i32 none ⟨0⟩ ⟨0, 0⟩,
    word 1, word 1, .call (idx 2), .drop, .drop] ++ (if trapping then [.unreachable] else [])
  let module_ : Module := {
    types := imports.map (·.2.1.toCoreRec) ++ [(wordFn 1 0).toCoreRec]
    imports := names.zipIdx |>.map fun (name, index) => ⟨"host", name, .func (idx index)⟩
    memories := [⟨.i32, ⟨1, none⟩⟩]
    funcs := (List.range names.length).map wrapper ++ [⟨idx names.length, [], destructor⟩]
    exports := (names ++ ["destructor"]).zipIdx |>.map fun (name, index) =>
      ⟨name, .func (idx (index + names.length))⟩ }
  let (store, inst, none) ← Core3.prepareE? store module_ addrs | none
  return (store, inst)

private def exportAddr (inst : ModuleInst) (name : String) : Option engine.FuncAddr := do
  let (_, .func address) ← (Core3.instExports inst).find? (·.1 == name) | none
  return address

private def session (inst : ModuleInst) : Session grow signature (Ret engine) := do
  let run (name : String) (args : List Nat) (expected : List FlatValue) := do
    let some addr := exportAddr inst name | internal s!"missing Core export {name}"
    trapIf ((← callCore addr (args.map i32Flat)) != expected) (.internal s!"unexpected result: {name}")
  let refused := [i32Flat 1, i32Flat 0]
  let success (value : Nat) := [i32Flat 0, i32Flat value]
  run "new-own" [77] [i32Flat 1]
  run "new-own" [77] [i32Flat 2]
  run "new-stream" [] [.int .i64 (BitVec.ofNat 64 (packEnds 3 4))]
  run "accept-node" [1, 32, 0, 0] refused
  run "accept-node" [0, 32, 0, 0] (success 1)
  run "wrong-owner" [1, 1] refused
  run "give-owner" [1, 0] (success 3)
  run "give-owner" [1, 0] refused
  run "rep" [3] [i32Flat 77]
  run "drop-owner" [1, 1] (success 0)
  run "drop-owner" [1, 1] refused
  run "give-reader" [1, 0] (success 2)
  run "give-reader" [1, 0] refused
  run "accept-node" [2, 48, 0, 0] (success 2)
  run "give-owner" [1, 0] refused
  run "give-reader" [2, 0] (success 2)
  run "close-reader" [2] []
  run "close-writer" [4] []
  return .unit

private def initial (trapping : Bool) : Option (ModuleInst × Machine.Config engine (HostState signature)) := do
  let (store, inst) ← instantiate trapping
  let dtor ← exportAddr inst "destructor"
  let reference : CStore engine := { CStore.empty with
    core := store, insts := [{}], resourceTypes := [{ impl := some ⟨0⟩, dtor := some dtor }],
    tasks := [{ ft := ⟨[], none, false⟩, opts := {}, inst := ⟨0⟩, caller := ⟨0⟩ }],
    threads := [{ status := .running, task := ⟨0⟩ }] }
  return (inst, {
    store := reference, host := {}, conts := [none]
    ctl := [Machine.Activation.ofProg (some ⟨0⟩) (session inst)] })

private def run (inst : ModuleInst) (config : Machine.Config engine (HostState signature)) :=
  Machine.run ready (dispatch inst) (core3Exec grow) Machine.Oracle.first 1500 config

private theorem run_sound (inst : ModuleInst) (config : Machine.Config engine (HostState signature)) :
    Machine.Steps .deterministic ready (dispatch inst) config (run inst config).labels (run inst config).config :=
  Machine.run_sound ready (dispatch inst) (core3Exec grow) Machine.Oracle.first 1500 config

private def expectedTranscript (trapping : Bool) : List Event :=
  let accept := fun ticket tag => Event.entered ticket "accept-node"
    (Endpoints.Core.Scheduled.acceptType contract) [i32Flat tag, i32Flat 32, i32Flat 0, i32Flat 0]
  let transfer := fun ticket name position => Event.entered ticket name
    Endpoints.Core.Scheduled.giveType [i32Flat 1, i32Flat position]
  [accept 0 1, .refused 0 (.accept (.boundary (.stored (.lift .storedBorrow)))),
    accept 1 0, .published 1 1, .returned 1 1,
    transfer 2 "wrong-owner" 1, .refused 2 (.claim .wrongResourceType),
    transfer 3 "give-owner" 0, .returned 3 3,
    transfer 4 "give-owner" 0, .refused 4 (.claim .unclaimed),
    transfer 5 "drop-owner" 1,
    transfer 6 "drop-owner" 1, .refused 6 (.claim .unclaimed)] ++
  if trapping then [] else
    [.returned 5 0,
      transfer 7 "drop-owner" 1, .refused 7 (.claim .unclaimed),
      transfer 8 "give-reader" 0, .returned 8 2,
      transfer 9 "give-reader" 0, .refused 9 (.claim .unclaimedEndpoint),
      .entered 10 "accept-node" (Endpoints.Core.Scheduled.acceptType contract)
        [i32Flat 2, i32Flat 48, i32Flat 0, i32Flat 0], .published 10 2, .returned 10 2,
      transfer 11 "give-owner" 0, .refused 11 (.claim .unclaimed),
      .entered 12 "give-reader" Endpoints.Core.Scheduled.giveType [i32Flat 2, i32Flat 0], .returned 12 2]

private def regression (trapping : Bool) : Bool :=
  match initial trapping with
  | none => false
  | some (inst, config) =>
    let result := run inst config
    let writer := result.config.host.writer
    let store := result.config.store
    let traps := result.labels.filterMap fun | .trap reason => some reason | _ => none
    let expected : List Issue := [.claim .unclaimed, .claim .unclaimed, .claim .wrongResourceType,
      .accept (.boundary (.stored (.lift .storedBorrow)))]
    result.outcome == (if trapping then .trap else .resolved) &&
    traps == (if trapping then [.coreTrap] else []) && writer.held.isEmpty &&
    writer.accepted.length == (if trapping then 1 else 2) &&
    ((writer.accepted.flatMap rootReceipts).map receiptId == [⟨0⟩, ⟨1⟩]) &&
    writer.accepted.flatMap rootEndpoints == (if trapping then [⟨0⟩] else [⟨0⟩, ⟨0⟩]) &&
    writer.endpoints == (if trapping then [⟨0⟩] else []) &&
    (store.insts[0]?.bind fun state => state.handles.get? 3) == some (.resource ⟨2⟩) &&
    (store.core.mems[0]?.map fun mem => (mem.bytes.extract 16 20).data) == some #[77, 0, 0, 0] &&
    result.config.host.transcript == expectedTranscript trapping &&
    result.config.host.refusals == (if trapping then expected
      else .claim .unclaimed :: .claim .unclaimedEndpoint :: .claim .unclaimed :: expected)

#guard regression false
#guard regression true

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Examples
