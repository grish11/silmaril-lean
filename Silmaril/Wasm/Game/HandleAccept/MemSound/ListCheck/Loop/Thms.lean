module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop.Defs
public import Silmaril.Wasm.Logic.Memory.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop

open Silmaril.Wasm.Game.HandleAccept.Memory (le32s)
open Silmaril.Wasm.Game.HandleAccept.MemSound (itemsList)
open Silmaril.Wasm.Logic.Core (bytesAt leNat)
open Silmaril.Formats

/-- Both guards together require all four bytes to fit in memory32. -/
theorem addressable_iff {base index : BitVec 32} :
    Addressable base index ↔ base.toNat + 4 * index.toNat + 4 ≤ 2 ^ 32 :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop.addressable_iff

/-- The Wasm arithmetic reads the same address as the natural-offset decoder. -/
theorem address_eq {base index : BitVec 32} (guard : Addressable base index) :
    (base + index * 4).toNat = base.toNat + 4 * index.toNat :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop.address_eq guard

/-- An iteration that passes the address guards cannot wrap its index. -/
theorem next_index {base index : BitVec 32} (guard : Addressable base index) :
    (index + 1).toNat = index.toNat + 1 :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop.next_index guard

/-- Every guarded back edge decreases the number of unchecked children. -/
theorem remaining_decreases {base index : BitVec 32} {length : Nat}
    (guard : Addressable base index) (unchecked : index.toNat < length) :
    length - (index + 1).toNat < length - index.toNat := by
  rw [next_index guard]
  omega

/-- Every decoded child word is the little-endian word at its natural byte offset. -/
theorem words_spec {bytes : List UInt8} {words : List (BitVec 32)}
    (decoded : le32s bytes = some words) : bytes.length = 4 * words.length ∧
      ∀ index (bound : index < words.length),
        words[index] = BitVec.ofNat 32 (leNat ((bytes.drop (4 * index)).take 4)) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop.words_spec decoded

/-- A valid reply fixes both header loads and every in-range child load. -/
theorem items_loads {mem : ByteArray} {words : List (BitVec 32)}
    (decoded : itemsList mem 0 = some words) :
    ∃ base : BitVec 32, 8 ≤ mem.size ∧
      base = BitVec.ofNat 32 (leNat (bytesAt mem ⟨0, 4⟩)) ∧
      words.length = (BitVec.ofNat 32 (leNat (bytesAt mem ⟨4, 4⟩))).toNat ∧
      base.toNat + 4 * words.length ≤ mem.size ∧
      ∀ pos (bound : pos < words.length),
        words[pos] = BitVec.ofNat 32 (leNat (bytesAt mem ⟨base.toNat + 4 * pos, 4⟩)) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop.items_loads decoded

/-- Correct rereads may change handle identities, but not the length or denotation at each index. -/
theorem reread_prefix {kind : Set SymStrBytesSExp}
    {env : Silmaril.Accept.Handle.Env (BitVec 32) SymStrBytesSExp}
    {root : BitVec 32} {children reread : List SymStrBytesSExp} {index : Nat}
    {handles : List (BitVec 32)} (checked : CheckedPrefix kind env root children index)
    (sameRoot : env root = some (SExp.ofList reread))
    (correct : List.Forall₂ (fun handle child => env handle = some child) handles reread) :
    handles.length = children.length ∧ ∀ pos (hpos : pos < handles.length)
      (bound : pos < children.length), env handles[pos] = some children[pos] :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop.reread_prefix checked sameRoot correct

theorem advance_prefix {kind : Set SymStrBytesSExp}
    {env : Silmaril.Accept.Handle.Env (BitVec 32) SymStrBytesSExp}
    {root handle : BitVec 32} {children : List SymStrBytesSExp} {index : Nat}
    (checked : CheckedPrefix kind env root children index) (bound : index < children.length)
    (linked : env handle = some children[index])
    (reply : ∃ child ∈ kind, env handle = some child) :
    CheckedPrefix kind env root children (index + 1) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop.advance_prefix checked bound linked reply

theorem finish_prefix {kind : Set SymStrBytesSExp}
    {env : Silmaril.Accept.Handle.Env (BitVec 32) SymStrBytesSExp}
    {root : BitVec 32} {children : List SymStrBytesSExp} {index : Nat}
    (checked : CheckedPrefix kind env root children index) (done : index = children.length) :
    ∃ tree ∈ listsOf kind, env root = some tree :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop.finish_prefix checked done

end Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop
