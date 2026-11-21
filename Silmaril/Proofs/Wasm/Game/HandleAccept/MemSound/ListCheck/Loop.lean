module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop.Defs
public import Silmaril.Wasm.Logic.Memory.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Items

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop

open Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop
open Silmaril.Wasm.Game.HandleAccept.Memory (le32s)
open Silmaril.Wasm.Game.HandleAccept.MemSound (itemsList pair32 segOf)
open Silmaril.Wasm.Logic.Core (Region bytesAt leNat length_bytesAt)
open Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Items (segOf_eq)
open Silmaril.Formats

theorem addressable_iff {base index : BitVec 32} :
    Addressable base index ↔ base.toNat + 4 * index.toNat + 4 ≤ 2 ^ 32 := by
  unfold Addressable
  omega

theorem address_eq {base index : BitVec 32} (guard : Addressable base index) :
    (base + index * 4).toNat = base.toNat + 4 * index.toNat := by
  have bound := addressable_iff.mp guard
  have offsetBound : index.toNat * 4 < 2 ^ 32 := by omega
  have addressBound : base.toNat + index.toNat * 4 < 2 ^ 32 := by omega
  rw [BitVec.toNat_add, BitVec.toNat_mul]
  change (base.toNat + index.toNat * 4 % 2 ^ 32) % 2 ^ 32 = base.toNat + 4 * index.toNat
  rw [Nat.mod_eq_of_lt offsetBound, Nat.mod_eq_of_lt addressBound, Nat.mul_comm index.toNat 4]

theorem next_index {base index : BitVec 32} (guard : Addressable base index) :
    (index + 1).toNat = index.toNat + 1 := by
  have bound := guard.1
  rw [BitVec.toNat_add]
  change (index.toNat + 1) % 2 ^ 32 = index.toNat + 1
  exact Nat.mod_eq_of_lt (by omega)

theorem words_spec : ∀ {bytes : List UInt8} {words : List (BitVec 32)},
    le32s bytes = some words → bytes.length = 4 * words.length ∧
      ∀ index (bound : index < words.length),
        words[index] = BitVec.ofNat 32 (leNat ((bytes.drop (4 * index)).take 4))
  | [], words, decoded => by
    simp only [le32s, Option.some.injEq] at decoded
    subst words
    exact ⟨rfl, fun _ bound => by simp at bound⟩
  | [_], _, decoded => by simp [le32s] at decoded
  | [_, _], _, decoded => by simp [le32s] at decoded
  | [_, _, _], _, decoded => by simp [le32s] at decoded
  | first :: second :: third :: fourth :: rest, _, decoded => by
    simp only [le32s, Option.map_eq_some_iff] at decoded
    obtain ⟨tail, decodedTail, rfl⟩ := decoded
    obtain ⟨tailLength, tailWords⟩ := words_spec decodedTail
    constructor
    · simp only [List.length_cons, tailLength]; omega
    intro index bound
    cases index with
    | zero =>
      change BitVec.ofNat 32 _ = BitVec.ofNat 32 (leNat [first, second, third, fourth])
      congr 1
      simp [leNat, Nat.mul_add]
      omega
    | succ index =>
      have tailBound : index < tail.length := by simpa using bound
      have offset : 4 * (index + 1) = 4 * index + 4 := by omega
      rw [offset]
      exact tailWords index tailBound

theorem words_at {mem : ByteArray} {base count : Nat} {bytes : List UInt8}
    {words : List (BitVec 32)} (range : segOf mem base count = some bytes)
    (decoded : le32s bytes = some words) :
    base + count ≤ mem.size ∧ count = 4 * words.length ∧
      ∀ pos (bound : pos < words.length),
        words[pos] = BitVec.ofNat 32 (leNat (bytesAt mem ⟨base + 4 * pos, 4⟩)) := by
  obtain ⟨inBounds, bytesEq⟩ := segOf_eq range
  obtain ⟨length, offsets⟩ := words_spec decoded
  have countEq : count = 4 * words.length := by
    rw [← length, bytesEq]
    exact (length_bytesAt (show (Region.mk base count).InBounds mem from inBounds)).symm
  refine ⟨inBounds, countEq, fun pos bound => ?_⟩
  have room : 4 ≤ count - 4 * pos := by omega
  simpa only [bytesEq, bytesAt, List.drop_take, List.drop_drop, List.take_take,
    Nat.min_eq_left room] using offsets pos bound

theorem items_loads {mem : ByteArray} {words : List (BitVec 32)}
    (decoded : itemsList mem 0 = some words) :
    ∃ base : BitVec 32, 8 ≤ mem.size ∧
      base = BitVec.ofNat 32 (leNat (bytesAt mem ⟨0, 4⟩)) ∧
      words.length = (BitVec.ofNat 32 (leNat (bytesAt mem ⟨4, 4⟩))).toNat ∧
      base.toNat + 4 * words.length ≤ mem.size ∧
      ∀ pos (bound : pos < words.length),
        words[pos] = BitVec.ofNat 32 (leNat (bytesAt mem ⟨base.toNat + 4 * pos, 4⟩)) := by
  unfold itemsList at decoded
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at decoded
  obtain ⟨header, headerRange, heads, headWords, ⟨base, count⟩, headPair, data, range, read⟩ := decoded
  have headsEq : heads = [base, count] := by
    rcases heads with _ | ⟨first, _ | ⟨second, _ | ⟨third, rest⟩⟩⟩ <;>
      simp_all only [pair32, reduceCtorEq, Option.some.injEq, Prod.mk.injEq]
  subst heads
  dsimp only at range
  obtain ⟨headerBound, _, headerAt⟩ := words_at headerRange headWords
  obtain ⟨dataBound, dataLength, atIndex⟩ := words_at range read
  have baseEq : base = BitVec.ofNat 32 (leNat (bytesAt mem ⟨0, 4⟩)) := headerAt 0 (by simp)
  have countEq : count = BitVec.ofNat 32 (leNat (bytesAt mem ⟨4, 4⟩)) := headerAt 1 (by simp)
  have wordsLength : words.length = count.toNat := by omega
  exact ⟨base, by simpa using headerBound, baseEq, countEq ▸ wordsLength, by omega, atIndex⟩

theorem reread_prefix {kind : Set SymStrBytesSExp}
    {env : Silmaril.Accept.Handle.Env (BitVec 32) SymStrBytesSExp}
    {root : BitVec 32} {children reread : List SymStrBytesSExp} {index : Nat}
    {handles : List (BitVec 32)} (checked : CheckedPrefix kind env root children index)
    (sameRoot : env root = some (SExp.ofList reread))
    (correct : List.Forall₂ (fun handle child => env handle = some child) handles reread) :
    handles.length = children.length ∧ ∀ pos (hpos : pos < handles.length)
      (bound : pos < children.length), env handles[pos] = some children[pos] := by
  have sameChildren := SExp.ofList_injective (Option.some.inj (sameRoot.symm.trans checked.1))
  subst reread
  exact ⟨correct.length_eq, fun _ hpos bound => correct.get hpos bound⟩

theorem advance_prefix {kind : Set SymStrBytesSExp}
    {env : Silmaril.Accept.Handle.Env (BitVec 32) SymStrBytesSExp}
    {root handle : BitVec 32} {children : List SymStrBytesSExp} {index : Nat}
    (checked : CheckedPrefix kind env root children index) (bound : index < children.length)
    (linked : env handle = some children[index])
    (reply : ∃ child ∈ kind, env handle = some child) :
    CheckedPrefix kind env root children (index + 1) := by
  obtain ⟨child, member, denotes⟩ := reply
  have sameChild := Option.some.inj (denotes.symm.trans linked)
  refine ⟨checked.1, by omega, fun pos hpos before => ?_⟩
  by_cases old : pos < index
  · exact checked.2.2 pos hpos old
  · obtain rfl : pos = index := by omega
    exact sameChild ▸ member

theorem finish_prefix {kind : Set SymStrBytesSExp}
    {env : Silmaril.Accept.Handle.Env (BitVec 32) SymStrBytesSExp}
    {root : BitVec 32} {children : List SymStrBytesSExp} {index : Nat}
    (checked : CheckedPrefix kind env root children index) (done : index = children.length) :
    ∃ tree ∈ listsOf kind, env root = some tree := by
  refine ⟨SExp.ofList children, ⟨children, ?_, rfl⟩, checked.1⟩
  intro child member
  obtain ⟨pos, found⟩ := List.mem_iff_getElem?.mp member
  obtain ⟨bound, rfl⟩ := List.getElem?_eq_some_iff.mp found
  exact checked.2.2 pos bound (by omega)

end Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop
