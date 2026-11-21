module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Thms
meta import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Defs
import Silmaril.Wasm.Game.HandleAccept.MemSound.Ast.Defs

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Examples

open Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Core (Contract)

public def resource : RtId := ⟨0⟩
public def element : Option (WIT.ClosedType RtId) := some (.prim .u16)

public inductive Tag where
  | mixed | invalid | lateTrap | text

@[expose] public def sig : Signature :=
  ⟨Tag, fun
    | .mixed => .record [("owner", .own resource), ("read", .stream element)]
    | .invalid => .result (some (.own resource)) (some (.list (.option (.borrow resource))))
    | .lateTrap => .tuple [.own resource, .stream element, .own resource]
    | .text => .tuple [.own resource, .option (.prim .string)], fun _ => .fixed 0⟩

private def contract : Contract sig :=
  ⟨0, ("wit", "accept-node"), fun raw => match raw.toNat with
    | 0 => some .mixed | 1 => some .invalid | 2 => some .lateTrap | 3 => some .text | _ => none,
    {}, ⟨0⟩⟩

private abbrev grow := SingleThreaded.neverFail
private abbrev engine := core3 grow

private def writeWord (address value : Nat) : List Instr :=
  [.intConst .i32 (BitVec.ofNat 32 address), .intConst .i32 (BitVec.ofNat 32 value),
    .intStore .i32 none ⟨0⟩ ⟨0, 0⟩]

private def body (tag first second : Nat) : List Instr :=
  writeWord 16 first ++ writeWord 20 second ++ writeWord 24 1 ++
    [.intConst .i32 (BitVec.ofNat 32 tag), .intConst .i32 16, .intConst .i32 0, .intConst .i32 0,
      .call ⟨0⟩]

private def module_ : Module where
  types := [HandleAccept.MemSound.Ast.tyTag, ⟨[⟨true, [], .func ⟨[], [.i32]⟩⟩]⟩]
  imports := [⟨"wit", "accept-node", .func ⟨0⟩⟩]
  memories := [⟨.i32, ⟨1, none⟩⟩]
  funcs := [⟨⟨1⟩, [], body 1 0 1⟩, ⟨⟨1⟩, [], body 0 1 2⟩,
    ⟨⟨1⟩, [], body 2 4 5⟩, ⟨⟨1⟩, [], body 0 7 8⟩]
  exports := [⟨"unsupported", .func ⟨1⟩⟩, ⟨"first", .func ⟨2⟩⟩,
    ⟨"late-trap", .func ⟨3⟩⟩, ⟨"retry", .func ⟨4⟩⟩]

private def initialArena (E : CoreEngine) : CStore E :=
  let store : CStore E := { CStore.empty with
    resourceTypes := [{ impl := some ⟨0⟩ }],
    resHandles := List.replicate 3 { rt := resource, rep := 77, own := true } }
  let (reference, table) := ([0, 1, 2] : List Nat).foldl (fun (reference, table) index =>
    let (next, readable, writable) := newStream element (some ⟨0⟩) reference
    let entries := [HandleEntry.resource ⟨index⟩, .waitable (.end_ readable), .waitable (.end_ writable)]
    (HandleSt.setEndIndex writable (3 * index + 3) (HandleSt.setEndIndex readable (3 * index + 2) next),
      entries.foldl (fun inst entry => inst.addHandle entry) table)) (store, ({} : InstState))
  { reference with insts := [table] }

private def initial : World grow sig := ⟨initialArena engine, {}⟩

private def coreValue : FlatValue → Val
  | .int kind word => .num ⟨.int kind, word⟩
  | .float kind word => .num ⟨.float kind, word⟩

private def execute (binding : Contract sig) (memory : Nat) :
    Nat → Store Nat → SingleThreaded.Thread → World grow sig →
    List Issue → Except String (Store Nat × World grow sig × CallResult × List Issue)
  | 0, _, _, _, _ => .error "Core regression ran out of steps"
  | fuel + 1, store, thread, world, issues =>
    match engine.status store thread with
    | .returned result => .ok (store, world, result, issues.reverse)
    | .stuck => .error "Core instance stuck"
    | .running =>
      match (core3Exec grow).step? (store, thread) with
      | none => .error "Core interpreter could not step"
      | some (updated, next) => execute binding memory fuel updated next world issues
    | .callout target args =>
      let (updated, result) := attempt binding (some memory) world ⟨target, store, args.map coreValue⟩
      match result with
      | .error issue => execute binding memory fuel store (engine.resume store thread .trap) updated (issue :: issues)
      | .ok handle => execute binding memory fuel store
          (engine.resume store thread (.values [.int .i32 handle])) updated issues

private def prepare (module_ : Module) : Except String (Store Nat × ModuleInst × Nat) := do
  let (withHost, hostAddr) := SingleThreaded.allocHost ({} : Store Nat)
    ⟨List.replicate 4 (.int .i32), [.int .i32]⟩ 0
  let some (store, instanceInfo, none) := Core3.prepareE? withHost module_ [.func hostAddr]
    | throw "could not instantiate the Core acceptor"
  let some memory := instanceInfo.mems[0]? | throw "no linked memory"
  pure (store, instanceInfo, memory)

private def invoke (binding : Contract sig) (instanceInfo : ModuleInst) (memory : Nat)
    (name : String) (current : Store Nat) (world : World grow sig) := do
  let exports : List (String × ExternAddr) := Core3.instExports instanceInfo
  let some (_, ExternAddr.func address) := exports.find? (fun (entry : String × ExternAddr) => entry.1 == name)
    | throw "no exported Core function"
  execute binding memory 72 current (SingleThreaded.Thread.invokeFlat address []) world []

private def replay : Except String Bool := do
  let (store, instanceInfo, memory) ← prepare module_
  let invoke := invoke contract instanceInfo memory
  let slot (state : World grow sig) (index : Nat) :=
    (state.reference.inst? ⟨0⟩).bind (fun inst => inst.handles.get? index)
  let (store, world, rejected, issues) ← invoke "unsupported" store initial
  let preflight := rejected == .trap && issues == [.boundary (.stored (.lift .storedBorrow))] &&
    world.writer.accepted.isEmpty && world.writer.held.isEmpty && world.writer.endpoints.isEmpty &&
    slot world 1 == some (.resource ⟨0⟩) && slot world 2 == some (.waitable (.end_ ⟨0⟩))
  let (store, world, accepted, acceptIssues) ← invoke "first" store world
  let (store, world, late, lateIssues) ← invoke "late-trap" store world
  let prior := late == .trap && lateIssues == [.localEffect (.trapped (.unknownHandle 1))] &&
    world.writer.accepted.length == 1 && world.writer.held.map receiptId == [⟨0⟩] &&
    world.writer.endpoints == [⟨0⟩] && (slot world 4).isNone && (slot world 5).isNone &&
    ((world.reference.end? ⟨2⟩).map (fun endpoint => (endpoint.owner, endpoint.index))) == some (none, none) &&
    (store.mems[memory]?.map fun mem => (mem.bytes.extract 16 24).data) == some #[4, 0, 0, 0, 5, 0, 0, 0]
  let (_, world, retry, retryIssues) ← invoke "retry" store world
  pure (preflight && accepted == .values [.int .i32 1] && acceptIssues.isEmpty && prior &&
    retry == .values [.int .i32 2] && retryIssues.isEmpty && world.writer.accepted.length == 2 &&
    world.writer.held.map receiptId == [⟨2⟩, ⟨0⟩] && world.writer.endpoints == [⟨4⟩, ⟨0⟩])

#guard replay == .ok true

private def textBody (slot tagged word : Nat) : List Instr :=
  writeWord 16 slot ++ writeWord 20 1 ++ writeWord 24 48 ++ writeWord 28 tagged ++ writeWord 48 word ++
    [.intConst .i32 3, .intConst .i32 16, .intConst .i32 0, .intConst .i32 0, .call ⟨0⟩]

private def textReplay (encoding : ABI.StringEncoding) (malformedCount validCount : Nat) :
    Except String Bool := do
  let textModule := { module_ with
    funcs := [⟨⟨1⟩, [], textBody 1 malformedCount 0xD800⟩, ⟨⟨1⟩, [], textBody 4 validCount 0xE9⟩]
    exports := [⟨"malformed", .func ⟨1⟩⟩, ⟨"valid", .func ⟨2⟩⟩] }
  let binding := { contract with mode := { encoding } }
  let (store, instanceInfo, memory) ← prepare textModule
  let (store, world, rejected, issues) ← invoke binding instanceInfo memory "malformed" store initial
  let slot (state : World grow sig) (index : Nat) :=
    (state.reference.inst? ⟨0⟩).bind (fun inst => inst.handles.get? index)
  let malformed := ABI.loadRange encoding .i32 malformedCount
  let failed := (malformed.codec.decode? [0, 0xD8]).isNone && rejected == .trap &&
    issues == [.localEffect (.trapped .invalidUtf16)] && world.writer.accepted.isEmpty &&
    world.writer.held.isEmpty && (slot world 1).isNone && slot world 4 == some (.resource ⟨1⟩)
  let (_, world, accepted, issues) ← invoke binding instanceInfo memory "valid" store world
  let range := ABI.loadRange encoding .i32 validCount
  let expected := range.codec.decode? ([0xE9, 0].take range.byteLength)
  let text := match world.writer.accepted with
    | [.tag ⟨_, payload⟩ _ _] =>
      match payload.val.value with
      | .record [.own 77, .variant 1 (some (.string text))] => some text.v.str
      | _ => none
    | _ => none
  pure (failed && accepted == .values [.int .i32 1] && issues.isEmpty && text == expected &&
    text == some "é" && world.writer.held.map receiptId == [⟨1⟩] && (slot world 4).isNone)

#guard textReplay .utf16 1 1 == .ok true
#guard textReplay .latin1Utf16 0x80000001 0x80000001 == .ok true
#guard textReplay .latin1Utf16 0x80000001 1 == .ok true

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Examples
