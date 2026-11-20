module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop.Defs
public import Silmaril.Wasm.Execution.Memory

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop

open Silmaril.Wasm.Execution

inductive ReplyIssue where
  | oversizedMemory32
  | insufficientSpace
  deriving DecidableEq, Repr

def encodeWords (words : List (BitVec 32)) : List UInt8 :=
  words.flatMap fun word => (Memory.encodeLE 4 word.toNat).data.toList

/-- Construct the compact `items` reply at return pointer zero, replacing only the header and
its child vector. Check the size before traversing the handles or narrowing the count to i32. -/
def writeItemsReply (memory : ByteArray) (handles : List (BitVec 32)) : Except ReplyIssue ByteArray :=
  if 2 ^ 32 < memory.size then .error .oversizedMemory32
  else if memory.size < 8 + 4 * handles.length then .error .insufficientSpace
  else
    let header := [8, BitVec.ofNat 32 handles.length]
    let bytes := (encodeWords header ++ encodeWords handles).toByteArray
    match Memory.writeBytes memory 0 bytes with
    | some updated => .ok updated
    | none => .error .insufficientSpace

/-- A compact `list<u8>` reply for `symbol_text` or `blob_bytes`. The memory32
check and header-space check precede narrowing the byte count to i32. -/
def writeByteReply (memory : ByteArray) (payload : List UInt8) : Except ReplyIssue ByteArray :=
  if 2 ^ 32 < memory.size then .error .oversizedMemory32
  else if memory.size < 8 + payload.length then .error .insufficientSpace
  else
    let header := encodeWords [8, BitVec.ofNat 32 payload.length]
    match Memory.writeBytes memory 0 (header ++ payload).toByteArray with
    | some updated => .ok updated
    | none => .error .insufficientSpace

end Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop
