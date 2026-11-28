module

public import Silmaril.Formats.Arrow.Writer.Defs
import Silmaril.Prelude.Bytes.Write.Thms
import Init.Data.List.Nat.TakeDrop
import Init.Omega

@[expose] public section

namespace Silmaril.Proofs.Formats.Arrow.Writer

open Silmaril.Formats.Arrow Silmaril.Formats.Arrow.Writer

theorem emitWords_wf (width : Nat) (words : List Nat) : (emitWords width words).wf = true :=
  KBytes.wf_ofChunks _ _ _

private theorem chunksBytes_full (width : Nat) (words : List Nat) :
    KBytes.chunksBytes width (width * words.length) words =
      words.flatMap (KBytes.unpack width) := by
  induction words with
  | nil => rfl
  | cons word words ih =>
    simp [KBytes.chunksBytes, Nat.mul_succ, ih, Nat.min_eq_left]

theorem emitWords_bytes (width : Nat) (words : List Nat) :
    (emitWords width words).toList = words.flatMap (KBytes.unpack width) :=
  (KBytes.toList_ofChunks _ _ _).trans (chunksBytes_full width words)

theorem emitWords_length (width : Nat) (words : List Nat) :
    (emitWords width words).len = width * words.length := by
  rw [← KBytes.length_toList _ (emitWords_wf width words), emitWords_bytes]
  induction words with
  | nil => simp
  | cons word words ih =>
    simp [KBytes.length_unpack, Nat.mul_succ, Nat.add_comm width, ih]

private theorem wordWindow (width : Nat) (words : List Nat) (index : Nat)
    (bound : index < words.length) :
    (((words.flatMap (KBytes.unpack width)).drop (width * index)).take width) =
      KBytes.unpack width words[index] := by
  induction words generalizing index with
  | nil => simp at bound
  | cons word words ih =>
    cases index with
    | zero =>
      simp only [List.flatMap_cons, Nat.mul_zero, List.drop_zero, List.getElem_cons_zero]
      have takeHead := List.take_append_length (l₁ := KBytes.unpack width word)
        (l₂ := words.flatMap (KBytes.unpack width))
      rw [KBytes.length_unpack] at takeHead
      exact takeHead
    | succ index =>
      simp only [List.flatMap_cons, List.getElem_cons_succ, Nat.mul_succ]
      have dropHead := List.drop_append_length (l₁ := KBytes.unpack width word)
        (l₂ := words.flatMap (KBytes.unpack width))
      rw [KBytes.length_unpack] at dropHead
      rw [Nat.add_comm (width * index) width, ← List.drop_drop, dropHead]
      exact ih index (by simpa using bound)

theorem readLE_emitWords (width : Nat) (words : List Nat) (index : Nat)
    (bound : index < words.length) :
    (emitWords width words).readLE (width * index) width =
      some (words[index] % 256^width) := by
  have fits : width * index + width ≤ (emitWords width words).len := by
    rw [emitWords_length, ← Nat.mul_succ]
    exact Nat.mul_le_mul_left width bound
  rw [KBytes.readLE, ite_eq_left fits, KBytes.read_eq _ _ _ (emitWords_wf _ _) fits,
    emitWords_bytes, wordWindow width words index bound, KBytes.leVal_unpack]

theorem emitBytes_bytes (bytes : List UInt8) :
    (emitWords 1 (bytes.map UInt8.toNat)).toList = bytes := by
  rw [emitWords_bytes]
  induction bytes with
  | nil => rfl
  | cons byte bytes ih =>
    simp only [List.map_cons, List.flatMap_cons]
    rw [ih]
    simp [KBytes.unpack]

theorem padding_aligned (size : Nat) : (size + padding size) % 8 = 0 := by
  unfold padding
  by_cases h : size % 8 = 0 <;> omega

theorem packBuffers_wf (offset : Nat) (pieces : List KBytes)
    (wf : ∀ piece ∈ pieces, piece.wf = true) : (packBuffers offset pieces).2.wf = true := by
  induction pieces generalizing offset with
  | nil => rfl
  | cons first rest ih =>
    exact KBytes.wf_append (wf first (by simp))
      (KBytes.wf_append (KBytes.wf_zeros _) (ih _ fun p h => wf p (by simp [h])))

theorem packBuffers_fits (offset : Nat) (pieces : List KBytes)
    (aligned : offset % 8 = 0) :
    BuffersFit (offset + (packBuffers offset pieces).2.len) offset (packBuffers offset pieces).1 := by
  induction pieces generalizing offset with
  | nil => trivial
  | cons first rest ih =>
    have nextAligned : (offset + first.len + padding first.len) % 8 = 0 := by
      have hp := padding_aligned first.len
      omega
    have tail := ih _ nextAligned
    change Buffer.Fits
        (offset + (first.len + (padding first.len +
          (packBuffers (offset + first.len + padding first.len) rest).2.len))) offset
        ⟨offset, first.len⟩ ∧
      BuffersFit _ (offset + first.len) (packBuffers (offset + first.len + padding first.len) rest).1
    constructor
    · refine ⟨Nat.le_refl _, aligned, ?_⟩
      change offset + first.len ≤ offset + (first.len + _)
      omega
    · -- The first descriptor may leave padding before the next descriptor.
      have bound :
          offset + (first.len + (padding first.len +
            (packBuffers (offset + first.len + padding first.len) rest).2.len)) =
          offset + first.len + padding first.len +
            (packBuffers (offset + first.len + padding first.len) rest).2.len := by omega
      change BuffersFit (offset + (first.len + (padding first.len +
        (packBuffers (offset + first.len + padding first.len) rest).2.len))) _ _
      rw [bound]
      generalize (packBuffers (offset + first.len + padding first.len) rest).1 = descriptors at tail ⊢
      cases descriptors with
      | nil => trivial
      | cons next remaining =>
        obtain ⟨fits, tailFits⟩ := tail
        exact ⟨⟨by have := fits.1; omega, fits.2.1, fits.2.2⟩, tailFits⟩

theorem packBuffers_exact (front : List UInt8) (pieces : List KBytes)
    (wf : ∀ piece ∈ pieces, piece.wf = true) :
    PackedWire (front ++ (packBuffers front.length pieces).2.toList)
      front.length pieces (packBuffers front.length pieces).1 := by
  induction pieces generalizing front with
  | nil => trivial
  | cons first rest ih =>
    let gap := KBytes.zeros (padding first.len)
    let extended := front ++ (first.toList ++ gap.toList)
    have firstLen := KBytes.length_toList first (wf first (by simp))
    have extendedLen : extended.length = front.length + first.len + padding first.len := by
      simp [extended, gap, firstLen, KBytes.toList_zeros]
      omega
    have tail := ih extended (fun piece h => wf piece (by simp [h]))
    rw [extendedLen] at tail
    simp only [packBuffers, KBytes.toList_append, PackedWire]
    refine ⟨trivial, ?_, ?_⟩
    · rw [List.drop_append_length, ← firstLen, List.take_append_length]
    · simpa [extended, gap, List.append_assoc] using tail

theorem packBuffers_length (offset : Nat) (pieces : List KBytes) :
    (packBuffers offset pieces).2.len = (pieces.map fun p => p.len + padding p.len).sum := by
  induction pieces generalizing offset with
  | nil => rfl
  | cons head tail ih =>
    change head.len + (padding head.len + (packBuffers _ tail).2.len) =
      head.len + padding head.len + (tail.map fun p => p.len + padding p.len).sum
    rw [ih]
    omega

theorem packBuffers_aligned (offset : Nat) (pieces : List KBytes) :
    (packBuffers offset pieces).2.len % 8 = 0 := by
  induction pieces generalizing offset with
  | nil => rfl
  | cons head tail ih =>
    have first := padding_aligned head.len
    have rest := ih (offset + head.len + padding head.len)
    change (head.len + (padding head.len + (packBuffers _ tail).2.len)) % 8 = 0
    omega

theorem packBuffers_count (offset : Nat) (pieces : List KBytes) :
    (packBuffers offset pieces).1.length = pieces.length := by
  induction pieces generalizing offset with
  | nil => rfl
  | cons head tail ih => simp [packBuffers, ih]

end Silmaril.Proofs.Formats.Arrow.Writer
