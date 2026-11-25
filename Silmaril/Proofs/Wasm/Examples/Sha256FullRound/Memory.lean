module

public import Silmaril.Wasm.Examples.Sha256FullRound.Defs
import Silmaril.Wasm.Logic.Memory.Thms

public section
namespace Silmaril.Proofs.Wasm.Examples.Sha256FullRound

open Silmaril.Wasm.Examples.Sha256FullRound
open Silmaril.Wasm.Execution Silmaril.Wasm.Logic.Core
open Silmaril.Crypto.SHA256.Kernel (Word)

theorem store_word (dst : Nat) (slot : Fin 8) (word : Word) (before : ByteArray)
    (bounds : dst + 32 ≤ before.size) :
    Memory.store before (dst + 4 * slot.val) (count := 4) word =
      some (writeWord dst (slot, word) before) := by
  have hi := slot.isLt
  have fit : dst + 4 * slot.val + 4 ≤ before.size := by omega
  simp only [Memory.store, Memory.writeBytes, Memory.encodeLE_size, fit, ↓reduceIte, writeWord]

private theorem word_disjoint (dst : Nat) (i j : Fin 8) (different : i ≠ j) :
    Region.Disjoint ⟨dst + 4 * i.val, 4⟩ ⟨dst + 4 * j.val, 4⟩ := by
  have differentVal : i.val ≠ j.val := fun eq => different (Fin.ext eq)
  simp only [Region.Disjoint, Region.stop]
  omega

private theorem word_outside (dst : Nat) (slot : Fin 8) (region : Region)
    (outside : Region.Disjoint ⟨dst, 32⟩ region) :
    Region.Disjoint ⟨dst + 4 * slot.val, 4⟩ region := by
  have hi := slot.isLt
  simp only [Region.Disjoint, Region.stop] at *
  omega

theorem writes_size (dst : Nat) (words : List (Fin 8 × Word)) (before : ByteArray)
    (bounds : dst + 32 ≤ before.size) :
    (writeWords dst words before).size = before.size := by
  induction words generalizing before with
  | nil => rfl
  | cons word rest ih =>
    obtain ⟨slot, val⟩ := word
    have size := size_store (store_word dst slot val before bounds)
    exact (ih _ (size ▸ bounds)).trans size

private theorem writes_frame (dst : Nat) (words : List (Fin 8 × Word)) (before : ByteArray)
    (bounds : dst + 32 ≤ before.size) (region : Region)
    (outside : Region.Disjoint ⟨dst, 32⟩ region) :
    bytesAt (writeWords dst words before) region = bytesAt before region := by
  induction words generalizing before with
  | nil => rfl
  | cons word rest ih =>
    obtain ⟨slot, val⟩ := word
    have store := store_word dst slot val before bounds
    have size := size_store store
    exact (ih _ (size ▸ bounds)).trans (bytesAt_store_disjoint store (word_outside dst slot region outside))

private theorem read_unwritten (dst : Nat) (slot : Fin 8) (writes : List Destination)
    (output : Vector Word 8) (before : ByteArray) (bounds : dst + 32 ≤ before.size)
    (absent : slot ∉ writes.map Prod.fst) :
    Memory.load (writeWords dst (slotWords writes output) before) (dst + 4 * slot.val) 4 =
      Memory.load before (dst + 4 * slot.val) 4 := by
  induction writes generalizing before with
  | nil => rfl
  | cons target rest ih =>
    obtain ⟨i, source⟩ := target
    have store := store_word dst i output[i] before bounds
    have size := size_store store
    have different : i ≠ slot := fun eq => absent (eq ▸ List.mem_cons_self)
    have tailAbsent : slot ∉ rest.map Prod.fst := fun h => absent (List.mem_cons_of_mem _ h)
    exact (ih _ (size ▸ bounds) tailAbsent).trans
      (load_store_disjoint store (word_disjoint dst i slot different))

private theorem read_written (dst : Nat) (slot : Fin 8) (writes : List Destination)
    (output : Vector Word 8) (before : ByteArray) (bounds : dst + 32 ≤ before.size)
    (distinct : (writes.map Prod.fst).Nodup) (selected : slot ∈ writes.map Prod.fst) :
    Memory.load (writeWords dst (slotWords writes output) before) (dst + 4 * slot.val) 4 =
      some output[slot] := by
  induction writes generalizing before with
  | nil => simp at selected
  | cons target rest ih =>
    obtain ⟨i, source⟩ := target
    have store := store_word dst i output[i] before bounds
    have size := size_store store
    have unique := List.nodup_cons.mp distinct
    rcases List.mem_cons.mp selected with eq | mem
    · change slot = i at eq
      subst i
      exact (read_unwritten dst slot rest output _ (size ▸ bounds) unique.1).trans
        (load_store_same store)
    · exact ih _ (size ▸ bounds) unique.2 mem

theorem round_output (dst : Nat) (words : Vector Word 8) (before : ByteArray)
    (bounds : dst + 32 ≤ before.size) :
    OutputOk before (roundMemory dst words before) dst words := by
  refine ⟨writes_size dst _ before bounds, ?_, writes_frame dst _ before bounds⟩
  have present : ∀ i : Fin 8, i ∈ (firstWrites ++ finalWrites).map Prod.fst := by decide
  intro slot
  exact read_written dst slot _ words before bounds (by decide) (present slot)

end Silmaril.Proofs.Wasm.Examples.Sha256FullRound
