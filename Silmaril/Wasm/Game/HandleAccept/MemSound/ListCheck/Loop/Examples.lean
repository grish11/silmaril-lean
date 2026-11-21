module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop.Thms
import Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop.Replies.Thms
import Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop.Run.Thms
import Silmaril.Wasm.Resource.Replay.Defs
import Silmaril.Wasm.Verify.Check.Defs
import Silmaril.Wasm.Validation.Check.Validate
meta import Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop.Replies.Defs

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop.Examples

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Game.HandleAccept.MemSound (itemsList)
open Silmaril.Wasm.Game.HandleAccept.Memory (MemAtom)
open Silmaril.Formats (SExp SymStrBytesSExp)
open Silmaril.Wasm.Resource (runTo?)

private def vectorReply : ByteArray :=
  ⟨#[8, 0, 0, 0, 3, 0, 0, 0, 41, 0, 0, 0, 67, 1, 0, 0, 5, 0, 0, 0]⟩

theorem symbol_checker_validates : (Silmaril.Wasm.Validation.validate? (mod {})).isSome := by
  decide +kernel

theorem blob_checker_validates : (Silmaril.Wasm.Validation.validate? (mod blobImports)).isSome := by
  decide +kernel

theorem final_word_fits : Addressable 4294967292 0 := by unfold Addressable; decide

theorem rejects_wrap_at_last_byte : ¬ Addressable 4294967293 0 := by unfold Addressable; decide

theorem rejects_wrap_in_offset : ¬ Addressable 0 1073741824 := by unfold Addressable; decide

theorem reads_three_distinct_words :
    itemsList vectorReply 0 = some [41, 323, 5] := by decide +kernel

private def childReply (size : Nat) (byte : UInt8) : ByteArray :=
  ⟨#[8, 0, 0, 0, 1, 0, 0, 0, byte]⟩ ++ ⟨Array.replicate (min size 20 - 9) 0⟩

private def replyMemory (handles : List (BitVec 32)) (children : List (BitVec 32 × UInt8))
    (importIdx : Nat) (args : List Val) (memory : ByteArray) : Option ByteArray :=
  if importIdx = 0 && args == [.i32 7, .i32 0] then (writeItemsReply memory handles).toOption
  else if importIdx = 1 then do
    let [.num ⟨.int .i32, handle⟩, retptr] := args | none
    if retptr != .i32 0 then none else do
      let byte ← children.lookup handle
      Execution.Memory.writeBytes memory 0 (childReply memory.size byte)
  else none

private def replay (handles : List (BitVec 32)) (children : List (BitVec 32 × UInt8)) :
    Nat → Config Nat → Option (List (Nat × List Val))
  | 0, config =>
    let final := (Exec.runI Silmaril.Wasm.Verify.refOracle 64 config).1
    if final.code.isEmpty then some [] else none
  | fuel + 1, config => do
    let (stopped, context, _, importIdx, args) ← runTo? 64 config
    let store := stopped.store
    let nextStore ← if importIdx = 2 && args == [.i32 7] then some store else do
      let memory ← store.mems[0]?
      let bytes ← replyMemory handles children importIdx args memory.bytes
      some { store with mems := [{ memory with bytes }] }
    let rest ← replay handles children fuel ⟨nextStore, stopped.frame, context.fill []⟩
    some ((importIdx, args) :: rest)

/-- Script a vector of any length that fits the guest memory, using the checked reply encoder
at each reread. `scratch = none` uses the module's initialized page; a replacement scratch
memory is only for small kernel regressions and is not a specification instance. -/
public def vectorReplay (handles : List (BitVec 32)) (children : List (BitVec 32 × UInt8))
    (scratch : Option ByteArray := none) :
    Option (List (Nat × List Val)) := do
  let (_, inst, _) ← Silmaril.Wasm.Verify.specInstance? (mod blobImports)
  let memory ← inst.store.mems[0]?
  let store := match scratch with
    | none => inst.store
    | some bytes => { inst.store with mems := [{ memory with bytes }] }
  replay handles children (2 * handles.length + 2) (invoke store 3 [.i32 7])

public def distinctChildrenReplay (scratch : Option ByteArray := none) :
    Option (List (Nat × List Val)) :=
  vectorReplay [41, 323, 5] [(41, 65), (323, 66), (5, 67)] scratch

public def distinctChildrenTrace : List (Nat × List Val) :=
  [(0, [.i32 7, .i32 0]), (1, [.i32 41, .i32 0]),
   (0, [.i32 7, .i32 0]), (1, [.i32 323, .i32 0]),
   (0, [.i32 7, .i32 0]), (1, [.i32 5, .i32 0]),
   (0, [.i32 7, .i32 0]), (2, [.i32 7])]

theorem visits_three_distinct_children_and_returns :
    distinctChildrenReplay (some vectorReply) = some distinctChildrenTrace := by decide +kernel

theorem calls_accept_for_empty_vector_without_child_calls :
    vectorReplay [] [] (some ⟨Array.replicate 8 0⟩) =
      some [(0, [.i32 7, .i32 0]), (2, [.i32 7])] := by decide +kernel

theorem visits_repeated_child_at_its_own_position :
    vectorReplay [41, 323, 5, 41] [(41, 65), (323, 66), (5, 67)]
        (some ⟨Array.replicate 24 0⟩) =
      some (distinctChildrenTrace.take 7 ++ [(1, [.i32 41, .i32 0]),
        (0, [.i32 7, .i32 0]), (2, [.i32 7])]) := by decide +kernel

theorem refuses_short_reply_memory :
    writeItemsReply ⟨Array.replicate 19 0⟩ [41, 323, 5] = .error .insufficientSpace := by
  apply rejects_short_memory <;> decide +kernel

/-- The validated example accepts an empty list in the actual one-page instance,
without relying on a scratch-memory override or any child payload. -/
theorem accepts_empty_list (profile : Silmaril.Wasm.Numerics.Profile) (checker : Checker)
    (policy : Silmaril.Accept.Handle.OnInvalid)
    {Rhos : Set (Silmaril.Accept.Handle.Env (BitVec 32) Silmaril.Formats.SymStrBytesSExp)}
    {rho : Silmaril.Accept.Handle.Env (BitVec 32) Silmaril.Formats.SymStrBytesSExp}
    (present : rho ∈ Rhos) {root : BitVec 32} (named : rho root = some (Silmaril.Formats.SExp.ofList [])) :
    Silmaril.Formats.SExp.ofList [] ∈ listReaderLang profile
      (Silmaril.Wasm.Game.HandleAccept.MemSound.ReplyEnvs
        Silmaril.Wasm.Game.HandleAccept.MemSound.Items.itemsReply)
      0 (mod checker.imports) checker.imports checker.decodeChild .trap policy Rhos := by
  obtain ⟨_, _, _, spec, page⟩ := checker_instance checker
  exact compact_accepts checker spec (by decide) page (handles := []) (by decide)
    (childBytes := fun _ => ByteArray.empty) (by simp) policy present named .nil (by simp)

private def mixedHandles : List (BitVec 32) := [41, 323, 5, 41]

private def mixedBlobBytes (handle : BitVec 32) : List UInt8 :=
  if handle = 41 then [] else if handle = 323 then [0, 255] else [128]

private def mixedBlobAtom (handle : BitVec 32) : MemAtom :=
  ⟨.bytes, by decide, mixedBlobBytes handle⟩

private def mixedBlobTree : SymStrBytesSExp := SExp.ofList (mixedHandles.map fun handle => .atom (mixedBlobAtom handle))

private def mixedBlobEnv : Silmaril.Accept.Handle.Env (BitVec 32) SymStrBytesSExp :=
  fun handle => if handle = 7 then some mixedBlobTree else some (.atom (mixedBlobAtom handle))

/-- An actual one-page checker run uses distinct byte lengths and revisits the first child. -/
theorem accepts_mixed_blob_sizes (profile : Silmaril.Wasm.Numerics.Profile)
    (policy : Silmaril.Accept.Handle.OnInvalid) :
    mixedBlobTree ∈ listReaderLang profile
      (Silmaril.Wasm.Game.HandleAccept.MemSound.ReplyEnvs
        Silmaril.Wasm.Game.HandleAccept.MemSound.Items.itemsReply)
      0 (mod Checker.blobs.imports) Checker.blobs.imports Checker.blobs.decodeChild .trap policy {mixedBlobEnv} := by
  refine byte_reply_accepts .blobs policy (rho := mixedBlobEnv) (Set.mem_singleton _) (root := 7)
    (handles := mixedHandles) (by decide) mixedBlobBytes ?_ rfl ?_ ?_
  · intro handle _
    unfold mixedBlobBytes
    split
    · decide
    · split <;> decide
  · exact .cons rfl (.cons rfl (.cons rfl (.cons rfl .nil)))
  · intro handle member
    refine ⟨mixedBlobAtom handle, rfl, ?_⟩
    have other : handle ≠ 7 := by
      intro root
      subst handle
      simp [mixedHandles] at member
    simp only [mixedBlobEnv, ite_eq_right other]

theorem refuses_short_child_memory :
    writeByteReply ⟨Array.replicate 8 0⟩ [0] = .error .insufficientSpace := by
  apply writeByteReply_rejects_short_memory <;> decide +kernel

#guard match writeByteReply ⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 188, 17]⟩ [255] with
  | .ok bytes => bytes.data == #[8, 0, 0, 0, 1, 0, 0, 0, 255, 188, 17]
  | .error _ => false

theorem short_child_reply_traps_without_store_change {store : Store Nat} {memory : MemInst}
    (single : store.mems = [memory]) (short : memory.bytes.size = 8) :
    (byteReplyHost [41] (fun _ => [0])).Ans () ⟨1, store, [.i32 41, .i32 0]⟩ ⟨store, .trap⟩ () := by
  apply ScriptReply.childError single (by simp)
  apply writeByteReply_rejects_short_memory <;> simp [short]

private def largeBlob : List UInt8 := List.replicate 65529 173

private def largeBlobAtom : MemAtom := ⟨.bytes, by decide, largeBlob⟩

private def largeBlobTree : SymStrBytesSExp := SExp.ofList [.atom largeBlobAtom]

private def largeBlobEnv : Silmaril.Accept.Handle.Env (BitVec 32) SymStrBytesSExp :=
  fun handle => if handle = 7 then some largeBlobTree else some (.atom largeBlobAtom)

theorem large_blob_reply_exceeds_one_page : 65536 < 8 + largeBlob.length := by
  rw [largeBlob, List.length_replicate]
  decide

/-- The last reply byte is in the second page of the actual instance. The proof
uses the symbolic reply encoder rather than evaluating the pages in Lean's kernel. -/
theorem accepts_blob_using_second_page (profile : Silmaril.Wasm.Numerics.Profile)
    (policy : Silmaril.Accept.Handle.OnInvalid) :
    largeBlobTree ∈ listReaderLang profile
      (Silmaril.Wasm.Game.HandleAccept.MemSound.ReplyEnvs
        Silmaril.Wasm.Game.HandleAccept.MemSound.Items.itemsReply)
      0 (mod Checker.blobs.imports ⟨2, by decide⟩)
      Checker.blobs.imports Checker.blobs.decodeChild .trap policy {largeBlobEnv} := by
  refine byte_reply_accepts_pages .blobs ⟨2, by decide⟩ policy
    (rho := largeBlobEnv) (Set.mem_singleton _) (root := 7) (handles := [41]) (by decide)
    (fun _ => largeBlob) (by intro _ _; rw [largeBlob, List.length_replicate]; decide) rfl (.cons rfl .nil) ?_
  intro handle member
  have same : handle = 41 := List.mem_singleton.mp member
  subst handle
  exact ⟨largeBlobAtom, rfl, rfl⟩

example : checkedPageShape .symbols ⟨0, by decide⟩ = true := checkedPageShape_all .symbols ⟨0, by decide⟩

example : checkedPageShape .blobs ⟨65536, by decide⟩ = true :=
  checkedPageShape_all .blobs ⟨65536, by decide⟩

end Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop.Examples
