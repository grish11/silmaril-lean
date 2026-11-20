module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop.Defs
public import Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop.Replies.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Wasm.Game.IOAccept
  Silmaril.Wasm.Game.HandleAccept.MemSound Silmaril.Formats.Api
open Silmaril.Wasm.Game.HandleAccept.Memory (MemAtom utf8?)
open Silmaril.Wasm.Game.HandleAccept.MemSound.Readers (symTextAns blobAns)
open Silmaril.Formats (SymStrBytesSExp)

/-- The actual executable loop checker variants. -/
inductive Checker where
  | symbols
  | blobs

def Checker.imports : Checker → ListImports
  | .symbols => {}
  | .blobs => blobImports

def Checker.decodeChild : Checker → HostReply → BitVec 32 → SxA MemAtom (BitVec 32)
  | .symbols => symTextAns
  | .blobs => blobAns

def Checker.kind : Checker → Set SymStrBytesSExp
  | .symbols => ListCheck.symbols
  | .blobs => ListCheck.blobs

/-- The semantic child denoted by the payload, before constructing a Core reply.
Malformed UTF-8 is not a symbol; all byte sequences are valid blobs. -/
def Checker.decodeBytes : Checker → List UInt8 → Option MemAtom
  | .symbols, bytes => (utf8? bytes).map fun text => ⟨.symbol, by decide, text⟩
  | .blobs, bytes => some ⟨.bytes, by decide, bytes⟩

/-- A host can supply a fixed logical vector and any child payloads, while rewriting bytes
on each answer. `ready` records what must survive each answer to keep the script available. -/
structure ReplyPlan (host : SEnv UImp) (ready : Store Nat → Prop)
    (ans : HostReply → BitVec 32 → SxA MemAtom (BitVec 32))
    (root : BitVec 32) (handles : List (BitVec 32))
    (answerFor : BitVec 32 → SxA MemAtom (BitVec 32)) : Prop where
  items : ∀ store state, ready store → ∃ next nextState mem,
    host.Ans state ⟨0, store, [.i32 root, .i32 0]⟩ ⟨next, .values []⟩ nextState ∧
    ready next ∧ next.funcs = store.funcs ∧ next.mems[0]? = some mem ∧
    itemsList mem.bytes 0 = some handles ∧ mem.bytes.size ≤ 2 ^ 32
  child : ∀ handle ∈ handles, ∀ store state, ready store → ∃ next nextState,
    host.Ans state ⟨1, store, [.i32 handle, .i32 0]⟩ ⟨next, .values []⟩ nextState ∧
    ready next ∧ next.funcs = store.funcs ∧
    ans ⟨.values [], memOf (some 0) next⟩ 0 = answerFor handle

/-- Observations in the remaining rounds, up to and including the acceptance call.
Every round freshly reads the whole vector, including the last round. -/
def remainingReads (root : BitVec 32) (handles remaining : List (BitVec 32))
    (answerFor : BitVec 32 → SxA MemAtom (BitVec 32)) : List MemREv :=
  remaining.flatMap (fun handle => [.read (.items root) (.items handles),
    .read (.atom handle) (answerFor handle)]) ++ [.read (.items root) (.items handles), .accept root]

/-- A one-memory store in which the script has `capacity` bytes to work with. -/
def ReplySpace (capacity : Nat) (store : Store Nat) : Prop :=
  ∃ mem, store.mems = [mem] ∧ mem.bytes.size = capacity

/-- A reply script uses the checked vector encoder and a supplied child encoder. Core sees
an encoding error as a call-local trap with the input store intact. -/
inductive ScriptReply (handles : List (BitVec 32))
    (encodeChild : ByteArray → BitVec 32 → Except ReplyIssue ByteArray) :
    UCall Nat → UReply → Prop where
  | items {store : Store Nat} {mem : MemInst} {root : BitVec 32} {bytes : ByteArray} :
      store.mems = [mem] → writeItemsReply mem.bytes handles = .ok bytes →
      ScriptReply handles encodeChild ⟨0, store, [.i32 root, .i32 0]⟩
        ⟨store.setMem 0 { mem with bytes }, .values []⟩
  | child {store : Store Nat} {mem : MemInst} {handle : BitVec 32} {bytes : ByteArray} :
      store.mems = [mem] → handle ∈ handles → encodeChild mem.bytes handle = .ok bytes →
      ScriptReply handles encodeChild ⟨1, store, [.i32 handle, .i32 0]⟩
        ⟨store.setMem 0 { mem with bytes }, .values []⟩
  | itemsError {store : Store Nat} {mem : MemInst} {root : BitVec 32} {issue : ReplyIssue} :
      store.mems = [mem] → writeItemsReply mem.bytes handles = .error issue →
      ScriptReply handles encodeChild ⟨0, store, [.i32 root, .i32 0]⟩ ⟨store, .trap⟩
  | childError {store : Store Nat} {mem : MemInst} {handle : BitVec 32} {issue : ReplyIssue} :
      store.mems = [mem] → handle ∈ handles →
      encodeChild mem.bytes handle = .error issue →
      ScriptReply handles encodeChild ⟨1, store, [.i32 handle, .i32 0]⟩ ⟨store, .trap⟩
  | accept {store : Store Nat} {root : BitVec 32} :
      ScriptReply handles encodeChild ⟨2, store, [.i32 root]⟩ ⟨store, .values []⟩

def scriptHost (handles : List (BitVec 32))
    (encodeChild : ByteArray → BitVec 32 → Except ReplyIssue ByteArray) : SEnv UImp where
  S := Unit
  Ans _ call reply _ := ScriptReply handles encodeChild call reply
  Div _ _ := False

abbrev CompactReply (handles : List (BitVec 32)) (childBytes : BitVec 32 → ByteArray) :=
  ScriptReply handles (fun _ handle => .ok (childBytes handle))

def compactHost (handles : List (BitVec 32)) (childBytes : BitVec 32 → ByteArray) : SEnv UImp :=
  scriptHost handles (fun _ handle => .ok (childBytes handle))

/-- Write both replies into the current guest memory. The raw script supplies payloads,
not padded images or a replacement memory. -/
def byteReplyHost (handles : List (BitVec 32)) (raw : BitVec 32 → List UInt8) : SEnv UImp :=
  scriptHost handles (fun memory handle => writeByteReply memory (raw handle))

end Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop
