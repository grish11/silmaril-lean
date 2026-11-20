module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Core.Scheduled.Defs
public import Silmaril.Wasm.Component.Reference.Machine.Soundness.Thms
meta import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Core.Scheduled.Defs
meta import Silmaril.Wasm.Component.Reference.Machine.Exec.Defs

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Core.Scheduled.Examples

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.AsyncRef
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Game.HandleAccept.Wit.Async (Channel Channel.endKind)

public abbrev grow := SingleThreaded.neverFail
public abbrev engine := core3 grow
private def resource : RtId := ⟨0⟩
private def element : Option (WIT.ClosedType RtId) :=
  some (.record [("word", .prim .u16), ("owner", .own resource)])

@[expose] public def signature (channel : Channel) : Signature :=
  ⟨Bool, fun unsupported =>
    let fields := if unsupported then some (.option (.borrow ⟨0⟩))
      else some (.record [("word", .prim .u16), ("owner", .own ⟨0⟩)])
    .option (match channel with | .stream => .stream fields | .future => .future fields),
    fun _ => .fixed 0⟩

private def contract (channel : Channel) : Contract (signature channel) :=
  ⟨0, ("host", "accept-node"), fun raw => if raw < 2 then some (raw == 1) else none, {}, ⟨0⟩⟩

private def handoff (channel : Channel) : Handoff := ⟨"give", ⟨1⟩, channel, element⟩

private def ready {channel : Channel} : HostReady (HostState (signature channel)) := fun _ _ => false
private def dispatch (channel : Channel) (inst : ModuleInst) :
    Canon.Call engine → Session grow (signature channel) (Ret engine) :=
  specDispatch ready (host (contract channel) inst 0 (handoff channel))

private structure ImportSpec where
  name : String
  type : V1.FuncType
  code : CanonHost engine

private def builtin (name : String) (inst : InstId) (op : ResolvedBuiltin engine)
    (type : V1.FuncType) : ImportSpec :=
  ⟨name, type, .builtin op inst⟩

private def embedder (name : String) (type : V1.FuncType) : ImportSpec :=
  ⟨name, type, .embedder name type⟩

private structure ExportSpec where
  name : String
  index : Nat
  setup : List Instr := []

private def idx {kind : IndexKind} (index : Nat) : Idx kind := ⟨Fin.ofNat _ index⟩

private def instantiate (store : Store (CanonHost engine)) (imports : List ImportSpec)
    (exports : List ExportSpec) : Option (Store (CanonHost engine) × ModuleInst) := do
  let (hostStore, addrs) := imports.foldl (fun (current, addresses) imp =>
    let (updated, address) := SingleThreaded.allocHost current imp.type imp.code
    (updated, addresses ++ [ExternAddr.func address])) (store, [])
  let module_ : Module := {
    types := imports.map fun imp => imp.type.toCoreRec
    imports := imports.zipIdx |>.map fun (imp, index) => ⟨"host", imp.name, .func (idx index)⟩
    memories := [⟨.i32, ⟨1, none⟩⟩]
    funcs := exports.map fun entry =>
      let count := (imports[entry.index]?.map (·.type.params.length)).getD 0
      ⟨idx entry.index, [], entry.setup ++ (List.range count).map (fun index => .localGet (idx index)) ++
        [.call (idx entry.index)]⟩
    exports := exports.zipIdx |>.map fun (entry, index) => ⟨entry.name, .func (idx (index + imports.length))⟩ }
  let (updated, inst, none) ← Core3.prepareE? hostStore module_ addrs | none
  return (updated, inst)

private def storeWord (ptr value : Nat) : List Instr :=
  [.intConst .i32 (BitVec.ofNat 32 ptr), .intConst .i32 (BitVec.ofNat 32 value),
    .intStore .i32 none ⟨0⟩ ⟨0, 0⟩]

private def memoryWriter : engine.MemAddr := (0 : Nat)
private def memoryReader : engine.MemAddr := (1 : Nat)

private def wordFn (params results : Nat) : V1.FuncType :=
  ⟨List.replicate params (.int .i32), List.replicate results (.int .i32)⟩

private def instantiateWriter (channel : Channel) (store : Store (CanonHost engine)) :=
  let opts : CanonOpts engine := { memory := some memoryWriter, async_ := true }
  let (create, copy, close, argc) : ResolvedBuiltin engine × ResolvedBuiltin engine ×
      ResolvedBuiltin engine × Nat := match channel with
    | .stream => (.streamNew element, .streamWrite element opts, .streamDropWritable element, 3)
    | .future => (.futureNew element, .futureWrite element opts, .futureDropWritable element, 2)
  let payload := storeWord 0 12 ++ storeWord 4 3 ++
    (if channel == Channel.stream then storeWord 8 31 ++ storeWord 12 4 else [])
  instantiate store
    [embedder "accept-node" (acceptType (contract channel)), builtin "new" ⟨0⟩ create ⟨[], [.int .i64]⟩,
      builtin "own" ⟨0⟩ (.resourceNew resource .i32) (wordFn 1 1),
      builtin "set" ⟨0⟩ .waitableSetNew (wordFn 0 1), builtin "join" ⟨0⟩ .waitableJoin (wordFn 2 0),
      builtin "write" ⟨0⟩ copy (wordFn argc 1),
      builtin "poll" ⟨0⟩ (.waitableSetPoll memoryWriter) (wordFn 2 1),
      builtin "close-set" ⟨0⟩ .waitableSetDrop (wordFn 1 0),
      builtin "close" ⟨0⟩ close (wordFn 1 0)]
    [⟨"bad", 0, storeWord 32 0 ++ storeWord 36 1⟩,
      ⟨"accept", 0, storeWord 32 1 ++ storeWord 36 1⟩,
      ⟨"new", 1, []⟩, ⟨"own", 2, []⟩, ⟨"set", 3, []⟩, ⟨"join", 4, []⟩,
      ⟨"write", 5, payload⟩,
      ⟨"poll", 6, []⟩, ⟨"close-set", 7, []⟩, ⟨"close", 8, []⟩]

private def instantiateReader (channel : Channel) (store : Store (CanonHost engine)) :=
  let opts : CanonOpts engine := { memory := some memoryReader, async_ := true }
  let (copy, cancel, close, argc) : ResolvedBuiltin engine × ResolvedBuiltin engine ×
      ResolvedBuiltin engine × Nat := match channel with
    | .stream => (.streamRead element opts, .streamCancelRead element true, .streamDropReadable element, 3)
    | .future => (.futureRead element opts, .futureCancelRead element true, .futureDropReadable element, 2)
  instantiate store
    [embedder (handoff channel).name giveType, builtin "read" ⟨1⟩ copy (wordFn argc 1),
      builtin "cancel" ⟨1⟩ cancel (wordFn 1 1),
      builtin "rep" ⟨1⟩ (.resourceRep resource .i32) (wordFn 1 1),
      builtin "drop" ⟨1⟩ (.resourceDrop resource) (wordFn 1 0),
      builtin "close" ⟨1⟩ close (wordFn 1 0)]
    [⟨"give", 0, []⟩, ⟨"read", 1, []⟩, ⟨"cancel", 2, []⟩,
      ⟨"rep", 3, []⟩, ⟨"drop", 4, []⟩, ⟨"close", 5, []⟩]

private def expect {channel : Channel} (inst : ModuleInst) (name : String) (args : List Nat)
    (expected : List FlatValue) : Session grow (signature channel) Unit := do
  let some (_, .func address) := (Core3.instExports inst).find? (·.1 == name)
    | internal s!"missing Core export {name}"
  let result ← callCore address (args.map i32Flat)
  trapIf (result != expected) (.internal s!"wrong Core result: {name}")

private def copyArgs (channel : Channel) (slot : Nat) : List Nat :=
  match channel with | .stream => [slot, 0, 2] | .future => [slot, 0]

private def copyPayload (channel : Channel) (result : CopyResult) (count : Nat) : Nat :=
  match channel with | .stream => packStreamCopyResult result count | .future => futureCopyPayload result

private def writer (channel : Channel) (inst : ModuleInst) : Session grow (signature channel) (Ret engine) := do
  let run := expect (channel := channel) inst
  run "new" [] [.int .i64 (BitVec.ofNat 64 (packEnds 1 2))]
  run "own" [71] [i32Flat 3]
  if channel == .stream then run "own" [93] [i32Flat 4]
  run "bad" [1, 32, 0, 0] [i32Flat 1, i32Flat 0]
  run "accept" [0, 32, 0, 0] [i32Flat 0, i32Flat 1]
  run "accept" [0, 32, 0, 0] [i32Flat 1, i32Flat 0]
  block (some ⟨1⟩)
  run "set" [] [i32Flat 1]
  run "join" [2, 1] []
  run "write" (copyArgs channel 2) [i32Flat blocked]
  run "poll" [1, 16] [i32Flat EventCode.none.toNat]
  resumeThread ⟨1⟩
  run "poll" [1, 16] [i32Flat (channel.endKind .write).eventCode.toNat]
  let event ← readMem { opts := { memory := some memoryWriter }, inst := ⟨0⟩ } 16 8
  trapIf (event.data != (u32Bytes 2).data ++ (u32Bytes (copyPayload channel .completed 2)).data)
    (.internal "wrong canonical poll event fields")
  run "join" [2, 0] []
  run "close-set" [1] []
  run "close" [2] []
  resumeThread ⟨1⟩
  pure .unit

private def reader (channel : Channel) (inst : ModuleInst) (stale : Bool) :
    Session grow (signature channel) (Ret engine) := do
  let run := expect (channel := channel) inst
  run "give" [1, 0] [i32Flat 0, i32Flat 1]
  run "give" [1, 0] [i32Flat 1, i32Flat 0]
  run "read" (copyArgs channel 1) [i32Flat blocked]
  run "cancel" [1] [i32Flat (copyPayload channel .cancelled 0)]
  let untouched ← readMem { opts := { memory := some memoryReader }, inst := ⟨1⟩ } 0 16
  trapIf (untouched.data != (List.replicate 16 (0 : UInt8)).toArray) (.internal "cancel wrote memory")
  block (some ⟨0⟩)
  run "read" (copyArgs channel 1) [i32Flat (copyPayload channel .completed 2)]
  run "rep" [2] [i32Flat 71]
  run "drop" [2] []
  if channel == .stream then
    run "rep" [3] [i32Flat 93]
    run "drop" [3] []
  block none
  if channel == .stream then run "read" (copyArgs channel 1) [i32Flat (copyPayload channel .dropped 0)]
  run "close" [1] []
  if stale then run "read" (copyArgs channel 1) []
  pure .unit

private def initial (channel : Channel) (stale : Bool) :
    Option (ModuleInst × Machine.Config engine (HostState (signature channel))) := do
  let (store, writerInst) ← instantiateWriter channel {}
  let (store, readerInst) ← instantiateReader channel store
  guard (writerInst.mems == [0] && readerInst.mems == [1])
  let reference : CStore engine := { CStore.empty with
      core := store, insts := [{}, {}], resourceTypes := [{ impl := some ⟨0⟩ }],
      tasks := [{ ft := ⟨[], none, false⟩, opts := {}, inst := ⟨0⟩, caller := ⟨0⟩ },
        { ft := ⟨[], none, false⟩, opts := {}, inst := ⟨1⟩, caller := ⟨1⟩ }],
      threads := [{ status := .running, task := ⟨0⟩ }, { status := .blocked, task := ⟨1⟩ }] }
  return (writerInst, {
    store := reference
    host := {}, conts := [none, some (Machine.Activation.ofProg (some ⟨1⟩) (reader channel readerInst stale))],
    ctl := [Machine.Activation.ofProg (some ⟨0⟩) (writer channel writerInst)] })

private def run (channel : Channel) (inst : ModuleInst)
    (config : Machine.Config engine (HostState (signature channel))) :=
  Machine.run ready (dispatch channel inst) (core3Exec grow) Machine.Oracle.first 1600 config

theorem run_sound (channel : Channel) (inst : ModuleInst)
    (config : Machine.Config engine (HostState (signature channel))) :
    Machine.Steps .deterministic ready (dispatch channel inst) config
      (run channel inst config).labels (run channel inst config).config :=
  Machine.run_sound ready (dispatch channel inst) (core3Exec grow) Machine.Oracle.first 1600 config

private def regression (channel : Channel) (stale : Bool) : Bool :=
  match initial channel stale with
  | none => false
  | some (inst, config) =>
    let result := run channel inst config
    let observed := result.config.host
    let store := result.config.store
    let traps := result.labels.filterMap fun | .trap reason => some reason | _ => none
    result.outcome == (if stale then .trap else .resolved) &&
    traps == (if stale then [.unknownHandle 1] else []) &&
    observed.writer.accepted.map rootIds == [[⟨0⟩]] && observed.writer.held.isEmpty &&
    observed.refusals == [.give .unclaimed, .accept (.localEffect (.trapped (.unknownHandle 1))),
      .accept (.stored (.lift .storedBorrow))] &&
    (store.core.mems[1]?.map fun mem => (mem.bytes.extract 0 16).data) ==
      some (#[12, 0, 0, 0, 2, 0, 0, 0] ++
        if channel == .stream then #[31, 0, 0, 0, 3, 0, 0, 0] else #[0, 0, 0, 0, 0, 0, 0, 0]) &&
    store.insts.map (fun inst => [1, 2, 3, 4].map inst.handles.get?) ==
      [[none, none, none, none], [none, none, none, none]]

#guard regression .stream false
#guard regression .stream true
#guard regression .future false
#guard regression .future true

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Core.Scheduled.Examples
