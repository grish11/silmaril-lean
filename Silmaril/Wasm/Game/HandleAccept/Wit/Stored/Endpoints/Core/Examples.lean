module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Core.Thms
meta import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Core.Defs
import Silmaril.Wasm.Game.HandleAccept.MemSound.Ast.Defs

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Core.Examples

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game

public def element : Option (WIT.ClosedType RtId) :=
  some (.record [("word", .prim .u16), ("hint", .option (.prim .bool))])

@[expose] public def sig : Signature :=
  ⟨Bool, fun bad => if bad then .option (.stream (some (.option (.borrow ⟨0⟩))))
    else .option (.stream element), fun _ => .fixed 0⟩

private def contract : Contract sig :=
  ⟨0, ("wit", "accept-node"), fun raw => if raw < 2 then some (raw == 1) else none, {}, ⟨0⟩⟩

private abbrev grow := SingleThreaded.neverFail
private abbrev engine := core3 grow

private def body (tag slot : Nat) : List Instr :=
  [.intConst .i32 16, .intConst .i32 (if tag = 1 then 0 else 1), .intStore .i32 none ⟨0⟩ ⟨0, 0⟩,
   .intConst .i32 20, .intConst .i32 (BitVec.ofNat 32 slot), .intStore .i32 none ⟨0⟩ ⟨0, 0⟩,
   .intConst .i32 (BitVec.ofNat 32 tag), .intConst .i32 16, .intConst .i32 0, .intConst .i32 0,
   .call ⟨0⟩]

private def module_ : Module where
  types := [HandleAccept.MemSound.Ast.tyTag, ⟨[⟨true, [], .func ⟨[], [.i32]⟩⟩]⟩]
  imports := [⟨"wit", "accept-node", .func ⟨0⟩⟩]
  memories := [⟨.i32, ⟨1, none⟩⟩]
  funcs := [⟨⟨1⟩, [], body 1 1⟩, ⟨⟨1⟩, [], body 0 1⟩, ⟨⟨1⟩, [], body 0 3⟩]
  exports := [⟨"unsupported", .func ⟨1⟩⟩, ⟨"first", .func ⟨2⟩⟩, ⟨"second", .func ⟨3⟩⟩]

private def initial : World grow sig :=
  let (first, readable, writable) := newStream element (some ⟨0⟩) CStore.empty
  let (second, nextReadable, nextWritable) := newStream element (some ⟨0⟩) first
  let table := [readable, writable, nextReadable, nextWritable].foldl
    (fun inst endpoint => inst.addHandle (.waitable (.end_ endpoint))) ({} : InstState)
  let state := { second with insts := [table] }
  ⟨HandleSt.setEndIndex nextWritable 4 (HandleSt.setEndIndex nextReadable 3
    (HandleSt.setEndIndex writable 2 (HandleSt.setEndIndex readable 1 state))), {}⟩

private def coreValue : FlatValue → Val
  | .int kind word => .num ⟨.int kind, word⟩
  | .float kind word => .num ⟨.float kind, word⟩

private def execute (hostCode memory : Nat) : Nat → Store Nat → SingleThreaded.Thread → World grow sig →
    List Issue → Except String (Store Nat × World grow sig × CallResult × List Issue)
  | 0, _, _, _, _ => .error "regression ran out of Core steps"
  | fuel + 1, store, thread, world, issues =>
    match engine.status store thread with
    | .returned result => .ok (store, world, result, issues.reverse)
    | .stuck => .error "Core instance stuck"
    | .running =>
      match (core3Exec grow).step? (store, thread) with
      | none => .error "Core interpreter could not step"
      | some (updated, next) => execute hostCode memory fuel updated next world issues
    | .callout target args =>
      if target != hostCode then .error "unexpected Core import" else
      let (updated, result) := contract.attempt (some memory) world ⟨target, store, args.map coreValue⟩
      match result with
      | .error issue => execute hostCode memory fuel store (engine.resume store thread .trap)
          updated (issue :: issues)
      | .ok handle => execute hostCode memory fuel store
          (engine.resume store thread (.values [.int .i32 handle])) updated issues

private def replay : Except String Bool := do
  let (hostStore, hostAddr) := SingleThreaded.allocHost ({} : Store Nat)
    ⟨List.replicate 4 (.int .i32), [.int .i32]⟩ 0
  let some (store, instanceInfo, none) := Core3.prepareE? hostStore module_ [.func hostAddr]
    | throw "could not instantiate the Core acceptor"
  let some memory := instanceInfo.mems[0]? | throw "no linked Core memory"
  let invoke (name : String) (current : Store Nat) (world : World grow sig) := do
    let some (ExternAddr.func address) := ((Core3.instExports instanceInfo).find? (·.1 == name)).map (·.2)
      | throw "no exported Core function"
    execute 0 memory 64 current (SingleThreaded.Thread.invokeFlat address []) world []
  let (store, world, rejected, issues) ← invoke "unsupported" store initial
  let before := world.writer.accepted.isEmpty && world.writer.held.isEmpty &&
    (world.reference.inst? ⟨0⟩).bind (fun inst => inst.handles.get? 1) == some (.waitable (.end_ ⟨0⟩)) &&
    (store.mems[0]?.map fun mem => (mem.bytes.extract 16 24).data) == some #[0, 0, 0, 0, 1, 0, 0, 0]
  let (store, world, accepted, acceptIssues) ← invoke "first" store world
  let (store, world, stale, staleIssues) ← invoke "first" store world
  let (store, world, retry, retryIssues) ← invoke "second" store world
  let slots := (world.reference.inst? ⟨0⟩).map fun inst => [1, 2, 3, 4].map inst.handles.get?
  let priorWrite := store.mems[0]?.map fun mem => (mem.bytes.extract 16 24).data
  pure (before && rejected == .trap && issues == [.stored (.lift .storedBorrow)] &&
    accepted == .values [.int .i32 1] && acceptIssues.isEmpty && stale == .trap &&
    staleIssues == [.localEffect (.trapped (.unknownHandle 1))] &&
    retry == .values [.int .i32 2] && retryIssues.isEmpty &&
    world.writer.accepted.map rootIds == [[⟨2⟩], [⟨0⟩]] && world.writer.held == [⟨2⟩, ⟨0⟩] &&
    slots == some [none, some (.waitable (.end_ ⟨1⟩)), none, some (.waitable (.end_ ⟨3⟩))] &&
    priorWrite == some #[1, 0, 0, 0, 3, 0, 0, 0])

#guard replay == .ok true

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Core.Examples
