module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop.Replies.Defs
public import Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Rules
import Silmaril.Wasm.Logic.Memory.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.LoopReplies

open Silmaril.Wasm.Execution
open Silmaril.Wasm.Game.HandleAccept.Memory (le32s)
open Silmaril.Wasm.Game.HandleAccept.MemSound (itemsList pair32 segOf)
open Silmaril.Wasm.Game.HandleAccept.MemSound.Text (bytesList)
open Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop
open Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound (le32s_encode readBytes_toList)
open Silmaril.Wasm.Logic.Core

private theorem encoded_length (words : List (BitVec 32)) : (encodeWords words).length = 4 * words.length := by
  induction words with
  | nil => rfl
  | cons word rest ih =>
    simp only [encodeWords, List.flatMap_cons, List.length_append, Array.length_toList,
      ByteArray.size_data, Memory.encodeLE_size, List.length_cons] at ih ⊢
    omega

private theorem decode_words (words : List (BitVec 32)) : le32s (encodeWords words) = some words := by
  induction words with
  | nil => rfl
  | cons word rest ih =>
    change le32s ((Memory.encodeLE 4 word.toNat).data.toList ++ encodeWords rest) = _
    rw [le32s_encode, ih]
    rfl

private theorem write_payload {memory : ByteArray} {payload : List UInt8} (count : BitVec 32)
    (space : 8 + payload.length ≤ memory.size) :
    ∃ updated, Memory.writeBytes memory 0 (encodeWords [8, count] ++ payload).toByteArray = some updated ∧
      updated.size = memory.size ∧ segOf updated 0 8 = some (encodeWords [8, count]) ∧
      segOf updated 8 payload.length = some payload := by
  let header := encodeWords [8, count]
  let bytes := (header ++ payload).toByteArray
  have headerLength : header.length = 8 := encoded_length _
  have bytesSize : bytes.size = 8 + payload.length := by simp [bytes, headerLength]
  have capacity : 0 + bytes.size ≤ memory.size := by rw [bytesSize, Nat.zero_add]; exact space
  obtain ⟨updated, write⟩ : ∃ updated, Memory.writeBytes memory 0 bytes = some updated :=
    ⟨_, by rw [Memory.writeBytes, ite_eq_left capacity]⟩
  have size := Memory.writeBytes_size memory bytes updated 0 write
  have headerIn : Region.Contains ⟨0, bytes.size⟩ ⟨0, 8⟩ := by
    simp [Region.Contains, Region.stop, bytesSize]
  have dataIn : Region.Contains ⟨0, bytes.size⟩ ⟨8, payload.length⟩ := by
    simp [Region.Contains, Region.stop, bytesSize]
  refine ⟨updated, write, size, ?_, ?_⟩
  · change segOf updated 0 8 = some header
    unfold segOf
    rw [readBytes_toList (by omega), bytesAt_writeBytes_inside' write headerIn]
    simp [bytesAt, bytes, ← headerLength]
  · unfold segOf
    rw [readBytes_toList (by omega), bytesAt_writeBytes_inside' write dataIn]
    simp [bytesAt, bytes, ← headerLength]

theorem bytes_roundtrip {memory : ByteArray} {payload : List UInt8}
    (width : memory.size ≤ 2 ^ 32) (space : 8 + payload.length ≤ memory.size) :
    ∃ updated, writeByteReply memory payload = .ok updated ∧ updated.size = memory.size ∧
      bytesList updated 0 = some payload := by
  let count := BitVec.ofNat 32 payload.length
  have countExact : count.toNat = payload.length := Nat.mod_eq_of_lt (by omega)
  obtain ⟨updated, write, size, headerRead, dataRead⟩ := write_payload count space
  refine ⟨updated, ?_, size, ?_⟩
  · unfold writeByteReply
    rw [ite_eq_right (Nat.not_lt.mpr width), ite_eq_right (Nat.not_lt.mpr space)]
    change (match Memory.writeBytes memory 0 (encodeWords [8, count] ++ payload).toByteArray with
      | some updated => Except.ok updated
      | none => Except.error ReplyIssue.insufficientSpace) = Except.ok updated
    rw [write]
  · simp only [bytesList, headerRead, Option.bind_eq_bind, Option.bind_some, decode_words, pair32]
    change segOf updated 8 count.toNat = some payload
    rw [countExact, dataRead]

theorem roundtrip {memory : ByteArray} {handles : List (BitVec 32)}
    (width : memory.size ≤ 2 ^ 32) (space : 8 + 4 * handles.length ≤ memory.size) :
    ∃ updated, writeItemsReply memory handles = .ok updated ∧ updated.size = memory.size ∧
      itemsList updated 0 = some handles ∧
      ∀ index, index < handles.length → Addressable 8 (BitVec.ofNat 32 index) := by
  let count := BitVec.ofNat 32 handles.length
  let data := encodeWords handles
  have dataLength : data.length = 4 * handles.length := encoded_length _
  have countExact : count.toNat = handles.length := Nat.mod_eq_of_lt (by omega)
  obtain ⟨updated, write, size, headerRead, dataRead⟩ :=
    write_payload (payload := data) count (by rwa [dataLength])
  refine ⟨updated, ?_, size, ?_, ?_⟩
  · unfold writeItemsReply
    rw [ite_eq_right (Nat.not_lt.mpr width), ite_eq_right (Nat.not_lt.mpr space)]
    change (match Memory.writeBytes memory 0 (encodeWords [8, count] ++ data).toByteArray with
      | some updated => Except.ok updated
      | none => Except.error ReplyIssue.insufficientSpace) = Except.ok updated
    rw [write]
  · rw [dataLength] at dataRead
    simp only [itemsList, headerRead, Option.bind_eq_bind, Option.bind_some, decode_words, pair32]
    change (segOf updated 8 (4 * count.toNat)).bind le32s = some handles
    rw [countExact, dataRead, Option.bind_some, show le32s data = some handles from decode_words _]
  · intro index bound
    apply addressable_iff.mpr
    change 8 + 4 * (index % 2 ^ 32) + 4 ≤ 2 ^ 32
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

end Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.LoopReplies
