module

import Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop.Growing.Thms
import Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop.Run.Defs
import Silmaril.Wasm.SingleThreaded.Exec.Interp
import Silmaril.Wasm.Verify.Check.Defs
meta import Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop.Growing.Defs
meta import Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop.Run.Defs
meta import Silmaril.Wasm.SingleThreaded.Exec.Interp
meta import Silmaril.Wasm.Verify.Check.Defs

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop.Growing.Examples

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Game.HandleAccept.MemSound.Text (bytesList)

private def beginCheck (store : Store Nat) (pages : BitVec 32) : Config Nat :=
  invoke store 3 [.i32 7, .i32 pages]

private def largeBytes : List UInt8 := List.replicate 65529 173

private def acceptingCall (oracle : GrowOracle) (store : Store Nat) : Except String (Store Nat) := do
  let mut active := beginCheck store 2
  let handles : List (BitVec 32) := [41, 42, 41]
  let items : Nat × List Val := (0, [.i32 7, .i32 0])
  let imports := handles.flatMap (fun handle => [items, (1, [.i32 handle, .i32 0])]) ++ [items, (2, [.i32 7])]
  for (expected, args) in imports do
    let (paused, _) := Exec.runI oracle 128 active
    let some (context, _, actual, operands) := decompose? paused.store paused.code |
      throw s!"missing checker import {expected}"
    unless expected == actual && args == operands do throw "unexpected checker import or operands"
    let some memory := paused.store.mems[0]? | throw "missing grown memory"
    unless memory.pages == 2 do throw "checker reached import before reserving two pages"
    let next ← match expected with
      | 0 => (writeItemsReply memory.bytes handles).mapError (fun _ => "items reply did not fit")
      | 1 => do
        let payload := if args == [.i32 41, .i32 0] then largeBytes else [0, 1, 255]
        let bytes ← (writeByteReply memory.bytes payload).mapError (fun _ => "child reply did not fit")
        unless bytesList bytes 0 == some payload do throw "the linked child decoder changed the blob"
        pure bytes
      | _ => do
        unless Execution.Memory.load memory.bytes 65536 1 == some 173 do
          throw "the items reread erased the final child byte"
        pure memory.bytes
    active := ⟨paused.store.setMem 0 { memory with bytes := next }, paused.frame, context.fill []⟩
  let (final, _) := Exec.runI oracle 128 active
  unless final.code.isEmpty do throw "checker did not return after accepting"
  pure final.store

private def regression : Except String Unit := do
  let some (_, instance_, _) := Verify.specInstance? (Growing.mod Checker.blobs.imports) |
    throw "the growing checker did not validate"
  unless instance_.store.mems[0]?.map (·.pages) == some 1 do throw "expected one initial page"
  let allow : GrowOracle := fun _ _ _ _ => false
  let refuse : GrowOracle := fun _ _ _ _ => true
  let (failed, _) := Exec.runI refuse 128 (beginCheck instance_.store 2)
  match failed.code with
  | [.trap] => pure ()
  | _ => throw "growth refusal did not trap before the first import"
  unless failed.store.mems[0]?.map (·.bytes) == instance_.store.mems[0]?.map (·.bytes) do
    throw "growth refusal changed memory"
  let grown ← acceptingCall allow failed.store
  let (overflow, _) := Exec.runI allow 128 (beginCheck grown 65537)
  match overflow.code with
  | [.trap] => pure ()
  | _ => throw "request beyond memory32 did not trap"
  unless overflow.store.mems[0]?.map (·.bytes) == grown.mems[0]?.map (·.bytes) do
    throw "out-of-range growth changed memory"
  let _ ← acceptingCall refuse overflow.store

#eval show IO Unit from
  match regression with
  | .ok () => pure ()
  | .error issue => throw (IO.userError issue)

open Silmaril.Wasm.Game.HandleAccept.MemSound Silmaril.Wasm.Game.HandleAccept.Memory
  Silmaril.Formats Silmaril.Formats.Api Silmaril.Accept.Handle

private def rawBlob (handle : BitVec 32) : List UInt8 :=
  if handle = 42 then [0, 1, 255] else largeBytes

private def blob (handle : BitVec 32) : MemAtom := ⟨.bytes, by decide, rawBlob handle⟩

private def tree : SymStrBytesSExp := SExp.ofList [.atom (blob 41), .atom (blob 42), .atom (blob 41)]

private def named : Silmaril.Accept.Handle.Env (BitVec 32) SymStrBytesSExp :=
  fun handle => if handle = 7 then some tree else some (.atom (blob handle))

theorem blob_reply_requires_growth : 65536 < 8 + (rawBlob 41).length := by
  rw [rawBlob, ite_eq_right (by decide : (41 : BitVec 32) ≠ 42), largeBytes, List.length_replicate]
  decide

theorem mixed_blobs_accept_after_growth (policy : OnInvalid) :
    tree ∈ ListCheck.listReaderLang (.deterministic fun _ _ _ _ => false) (ReplyEnvs Growing.reply) 0
      (Growing.mod Checker.blobs.imports InitialPages.one) Checker.blobs.imports Checker.blobs.decodeChild
      .trap policy {named} := by
  refine byte_reply_accepts (profile := .deterministic fun _ _ _ _ => false)
    .blobs InitialPages.one ⟨2, by decide⟩ (fun _ => rfl) policy
    (rho := named) (Set.mem_singleton _) (root := 7) (handles := [41, 42, 41]) (by decide) rawBlob
    ?_ rfl (.cons rfl (.cons rfl (.cons rfl .nil))) ?_
  · intro handle _
    change 8 + (rawBlob handle).length ≤ 131072
    unfold rawBlob
    split
    · decide
    · rw [largeBytes, List.length_replicate]
      decide
  · intro handle member
    have notRoot : handle ≠ 7 := by
      intro equal
      subst handle
      exact (by decide : (7 : BitVec 32) ∉ [41, 42, 41]) member
    exact ⟨blob handle, rfl, by simp only [named, ite_eq_right notRoot]⟩

end Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop.Growing.Examples
